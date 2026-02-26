# Brief: Type-Driven Serialization

**Status:** design
**Priority:** Phase 2 (needed for web, MCP, config, IPC — not for self-hosting)
**Depends on:** 0g-advanced-types (associated types), 0h-stdlib-errors (@derive)
**Blocks:** web framework, MCP tool generation, distributed actors

## Motivation

Serialization touches everything. Web services, config files, CLI tools,
IPC, persistence, logging — every program that communicates with the
outside world converts between typed values and bytes.

Adapted from Rill's Format brief. The design is ~90% portable. Key
changes: no HKTs (Validated is a concrete type), separate Encode/Decode
traits, effect signatures on codec functions.

## What Kea's Type System Gives Us

**Row polymorphism → typed partial deserialization.** Deserialize only
the fields you need from a 20-field JSON object, fully typed:

```kea
let user: { name: String, age: Int | r } = Json.parse(json_string)?
-- user.name and user.age are typed. Extra fields ignored.
```

No equivalent in Rust (you define all 20 fields or use `serde_json::Value`).

**Effects → pure vs impure serialization.** `Json.to_string(x)` is
`-> String` (pure). `Json.from_string(s)` is `-[Fail DecodeError]> T`.
`Json.to_file(x, path)` is `-[IO, Fail IoError]>`. The effect system
tracks this automatically.

**Associated types → format-agnostic traits.** The Format trait uses
associated types for output/input. The format uniquely determines these:

```kea
Json.encode(value)      -- -> String
MsgPack.encode(value)   -- -> Bytes
```

## Decisions

- **Separate Encode/Decode traits, not Codec.** Real types are often
  one-directional: logging payloads are encode-only, API response DTOs
  are decode-only, opaque types with invariants might manually implement
  Decode with validation but derive Encode. `@derive(Encode, Decode)`
  covers the common case.

- **Validated as a concrete type, not an Applicative instance.**
  Rill's brief used `Applicative` to justify `Validated.apply`, but
  the compiler codegen always targets `Validated` specifically — it's
  never generic over "any Applicative." Making `pure`/`apply` inherent
  methods on `Validated` removes a layer of indirection. The generated
  code is identical. The user experience is identical (all errors at
  once). The implementation is simpler.

  ```kea
  struct Validated A E

  fn pure(_ value: A) -> Validated A E
  fn apply(_ self: Validated (A -> B) E, _ arg: Validated A E) -> Validated B E

  -- Compiler generates for @derive(Decode):
  Validated.pure(|name, age, email| -> User { name, age, email })
    |> .apply(read_field(reader, "name", String))
    |> .apply(read_field(reader, "age", Int))
    |> .apply(read_field(reader, "email", Option String))
  ```

- **Format-specific Value types.** No universal `SerdeValue`. JSON has
  no Date, TOML has no null, MessagePack has Bytes. Format-specific
  types are honest about what each format can represent.

## Design

### Encode / Decode Traits

```kea
trait Encode
  fn encode(_ self: Self, _ w: FormatWriter) -> FormatWriter

trait Decode
  fn decode(_ r: FormatReader) -[Fail DecodeError]> Self
```

### FormatWriter / FormatReader

Core abstraction. Each format implements these. No visitor pattern.

```kea
trait FormatWriter
  type Output
  fn write_null(_ self: Self) -> Self
  fn write_bool(_ self: Self, _ value: Bool) -> Self
  fn write_int(_ self: Self, _ value: Int) -> Self
  fn write_float(_ self: Self, _ value: Float) -> Self
  fn write_string(_ self: Self, _ value: String) -> Self
  fn begin_list(_ self: Self, _ len: Option Int) -> Self
  fn end_list(_ self: Self) -> Self
  fn begin_map(_ self: Self, _ len: Option Int) -> Self
  fn write_key(_ self: Self, _ key: String) -> Self
  fn end_map(_ self: Self) -> Self
  fn finish(_ self: Self) -[Fail FormatError]> Self.Output

trait FormatReader
  type Input
  fn from_input(_ input: Self.Input) -[Fail FormatError]> Self
  fn read_bool(_ self: Self) -[Fail FormatError]> Bool
  fn read_int(_ self: Self) -[Fail FormatError]> Int
  fn read_float(_ self: Self) -[Fail FormatError]> Float
  fn read_string(_ self: Self) -[Fail FormatError]> String
  fn begin_list(_ self: Self) -[Fail FormatError]> Option Int
  fn has_next(_ self: Self) -> Bool
  fn end_list(_ self: Self) -[Fail FormatError]> Unit
  fn begin_map(_ self: Self) -[Fail FormatError]> Option Int
  fn read_key(_ self: Self) -[Fail FormatError]> String
  fn end_map(_ self: Self) -[Fail FormatError]> Unit
```

### Compiler-Generated Impls

```kea
@derive(Encode, Decode)
struct User
  name: String
  age: Int
  email: Option String
```

Generates encode as direct FormatWriter calls. Generates decode
using Validated for Applicative error accumulation — all field
errors reported at once, not just the first.

### Partial Deserialization

Open row types enable typed partial deserialization:

```kea
-- JSON has 20 fields. You need 3.
let user: { name: String, email: String | r } = Json.parse(json_string)?
-- Typed fields parsed. Extra fields skipped. No struct for all 20.
```

### Bundled Formats

- **Json** — primary format, text-based
- **Toml** — configuration files
- **MsgPack** — binary, compact
- **Csv** — tabular data (flat records only)

Third-party formats implement FormatWriter/FormatReader and get
the full compiled serialization path.

### Field Customization

```kea
@derive(Encode, Decode)
@encode(naming: snake_case)
struct ApiResponse
  userName: String      -- encodes as "user_name"
  createdAt: DateTime   -- encodes as "created_at"

  @rename("id")
  userId: Int           -- encodes as "id"

  @default(30)
  timeout: Int          -- defaults to 30 when missing on decode

  @skip_if(Option.is_none)
  metadata: Option String  -- omitted when None
```

### Sum Type Representation

```kea
-- Externally tagged (default): {"Circle": 3.14}
@derive(Encode, Decode)
enum Shape
  Circle(Float)
  Rect(Float, Float)
  Point

-- Internally tagged: {"type": "Circle", "radius": 3.14}
@derive(Encode, Decode)
@tagged(style: "internal", field: "type")
enum Message
  Text(String)
  Image(Bytes)
```

### Error Handling

```kea
enum DecodeError
  MissingField(String)
  TypeMismatch(field: String, expected: String, got: String)
  InvalidValue(field: String, reason: String)
  UnknownVariant(name: String, expected: List String)
  FormatSyntax(String)
```

Errors include path to problematic value:
`"users[2].address.zip: expected Int, got String"`.

Validated accumulates ALL errors. Fix everything in one pass.

## What's Unique vs Rust's Serde

| Feature | Serde (Rust) | Kea |
|---------|-------------|-----|
| Error reporting | First error only | All errors (Validated) |
| Partial deserialization | New struct or Value | Open row type |
| Effect tracking | None | Pure vs impure distinguished |
| Derive generation | Proc macro | Compiler-generated from type |

## Implementation Plan

### Phase 1: Core traits + JSON
- Encode/Decode trait signatures
- FormatWriter/FormatReader traits
- JsonWriter/JsonReader
- @derive(Encode) codegen for structs, enums
- @derive(Decode) with Validated error accumulation
- Json.to_string, Json.parse

### Phase 2: Partial deserialization + additional formats
- Open row deserialization
- Toml, MsgPack formats

### Phase 3: Customization
- @rename, @default, @skip_if, @tagged annotations
- Sum type representation modes

## Testing

- Round-trip: `Json.parse(Json.to_string(x))? == x`
- Applicative errors: two bad fields → two errors, not one
- Partial deser: open row parses subset of fields
- Sum types: all 4 representation modes round-trip
- Format-agnostic: same type serializes to JSON, TOML, MsgPack

## Open Questions

- Should opaque types be automatically non-serializable? (Proposal:
  yes. Opaque types require manual Encode/Decode impls. The opacity
  contract means the internal representation shouldn't leak.)
- Round-trip preservation through open rows? (Post-v1. Requires
  records to carry hidden overflow maps. See Rill brief §13.)

; Kea syntax highlighting queries
; Effect-aware capture strategy: effects are a distinct visual layer.

; ── Keywords ─────────────────────────────────────────────────────

["let" "fn" "expr" "pub" "if" "else" "case" "when"
 "type" "struct" "trait" "impl" "where" "use" "as" "test"
 "for" "in" "while" "cond"] @keyword

; Effect keywords — distinct from regular keywords so themes
; can give effects their own colour.
["effect" "handle" "resume" "fail" "catch" "then"] @keyword.effect

; Logical operators as keywords
["and" "or" "not"] @keyword.operator

; ── Functions ────────────────────────────────────────────────────

(function_declaration
  name: (identifier) @function)

(expr_declaration
  name: (identifier) @function)

(call_expression
  function: (identifier) @function.call)

(call_expression
  function: (field_expression
    field: (identifier) @function.call))

; ── Types ────────────────────────────────────────────────────────

(type_definition
  name: (upper_identifier) @type.definition)

(struct_definition
  name: (upper_identifier) @type.definition)

(trait_definition
  name: (upper_identifier) @type.definition)

(variant
  name: (upper_identifier) @constructor)

; Type annotations
(named_type
  (upper_identifier) @type)

(applied_type
  constructor: (upper_identifier) @type)

(fn_type "fn" @type.builtin)
(fn_effect_type "fn" @type.builtin)

; ── Effects ──────────────────────────────────────────────────────

; Effect declarations — name gets @type.effect
(effect_declaration
  name: (upper_identifier) @type.effect)

; Effect references in arrows: -[IO, Fail E]>
(effect_ref
  name: (upper_identifier) @type.effect)

; Effect arrow punctuation
(effect_row "[" @punctuation.bracket.effect)
(effect_row "]" @punctuation.bracket.effect)
(effect_return_type "-" @punctuation.bracket.effect)
(effect_return_type ">" @punctuation.bracket.effect)

; Handle expression — effect name + operation
(operation_clause
  effect: (upper_identifier) @type.effect)
(operation_clause
  operation: (identifier) @function.effect)

; ── Constructors ─────────────────────────────────────────────────

(constructor_expression
  constructor: (upper_identifier) @constructor)

(constructor_pattern
  constructor: (upper_identifier) @constructor)

; ── Annotations ──────────────────────────────────────────────────

(annotation
  "@" @attribute
  name: (identifier) @attribute)

; ── Literals ─────────────────────────────────────────────────────

(integer) @number
(float) @number.float
(string) @string
(boolean) @boolean
(none) @constant.builtin

; ── Operators ────────────────────────────────────────────────────

["+" "-" "*" "/" "%" "++" "<>"
 "==" "!=" "<" "<=" ">" ">="
 "=" "->" "~"] @operator

; Try operator (effect sugar)
(try_expression "?" @operator.effect)

; ── Punctuation ──────────────────────────────────────────────────

["(" ")" "[" "]" "{" "}"] @punctuation.bracket
["," "." ":" "|"] @punctuation.delimiter

; ── Receiver placeholder ─────────────────────────────────────────

(receiver_placeholder) @variable.builtin

; ── Variables ────────────────────────────────────────────────────

(identifier) @variable

; ── Parameters ───────────────────────────────────────────────────

(parameter
  pattern: (variable_pattern
    (identifier) @variable.parameter))

(lambda_parameter
  pattern: (variable_pattern
    (identifier) @variable.parameter))

; ── Comments ─────────────────────────────────────────────────────

(line_comment) @comment
(doc_comment) @comment.documentation

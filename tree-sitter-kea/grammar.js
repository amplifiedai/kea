/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

// Kea tree-sitter grammar.
// Uses an external scanner (src/scanner.c) for indentation-sensitive
// layout: INDENT/DEDENT/NEWLINE tokens plus DOC_BLOCK scanning.

const PREC = {
  or: 1,
  and: 3,
  equality: 5,
  comparison: 7,
  concat: 8,
  additive: 9,
  multiplicative: 11,
  unary: 13,
  postfix: 15,
};

module.exports = grammar({
  name: "kea",

  // Horizontal whitespace and comments are ignorable.
  // Newlines are NOT extras — they are handled by the external scanner.
  extras: ($) => [/[\s]/, $.line_comment],

  externals: ($) => [
    $.indent,
    $.dedent,
    $.newline,
    $.doc_start,
    $.doc_body,
  ],

  word: ($) => $.identifier,

  conflicts: ($) => [
    [$.lambda_parameter, $.or_pattern],
    [$.pure_return_type, $.effect_function_type],
    [$.type_constraint, $.effect_function_type],
    [$.trait_definition, $.effect_function_type],
    [$.field_init, $.field_pattern],
    [$.effect_return_type, $.effect_function_type],
    [$.impl_block, $.constructor_expression],
    [$.alias_declaration, $.effect_function_type],
    [$.applied_type, $.paren_type],
    [$.function_declaration, $.struct_field],
    [$.function_declaration, $.struct_field],
  ],

  rules: {
    source_file: ($) => repeat($._top_level),

    _top_level: ($) =>
      choice(
        seq($._declaration, optional($.newline)),
        seq($._expression, optional($.newline)),
      ),

    // ── Doc blocks ──────────────────────────────────────────────
    // Handled entirely by the external scanner.  The scanner matches
    // `doc` + optional inline text + indented body lines (including
    // blank lines within the body).

    // ── Declarations ──────────────────────────────────────────────

    _declaration: ($) =>
      choice(
        $.documented_declaration,
        $._bare_declaration,
      ),

    doc_block: ($) => seq($.doc_start, optional($.doc_body)),

    documented_declaration: ($) =>
      seq($.doc_block, optional($.newline), $._bare_declaration),

    _bare_declaration: ($) =>
      choice(
        $.function_declaration,
        $.expr_declaration,
        $.type_definition,
        $.struct_definition,
        $.trait_definition,
        $.impl_block,
        $.legacy_impl_block,
        $.effect_declaration,
        $.use_declaration,
        $.test_declaration,
        $.alias_declaration,
      ),

    function_declaration: ($) =>
      prec.right(seq(
        repeat(seq($.annotation, optional($.newline))),
        optional("pub"),
        "fn",
        field("name", $.identifier),
        $.parameter_list,
        optional($._return_type),
        optional($.where_clause),
        optional($._block),
      )),

    // Bodyless fn signature — used in trait/effect declarations.
    function_signature: ($) =>
      seq(
        optional("pub"),
        "fn",
        field("name", $.identifier),
        $.parameter_list,
        optional($._return_type),
      ),

    expr_declaration: ($) =>
      prec.right(seq(
        repeat(seq($.annotation, optional($.newline))),
        "expr",
        field("name", $.identifier),
        $.parameter_list,
        optional($._return_type),
        optional($._block),
      )),

    parameter_list: ($) =>
      seq("(", commaSep($.parameter), ")"),

    parameter: ($) =>
      seq(
        field("pattern", $._pattern),
        optional(seq(":", field("type", $._type))),
      ),

    _return_type: ($) =>
      choice(
        $.pure_return_type,
        $.effect_return_type,
      ),

    pure_return_type: ($) => seq("->", field("type", $._type)),

    effect_return_type: ($) =>
      seq("-", $.effect_row, ">", field("type", $._type)),

    effect_row: ($) =>
      seq(
        "[",
        commaSep1(choice($.effect_ref, field("tail", $.identifier))),
        optional(seq("|", field("tail", $.identifier))),
        "]",
      ),

    effect_ref: ($) =>
      seq(
        field("name", $.upper_identifier),
        repeat(field("arg", $._simple_type)),
      ),

    where_clause: ($) =>
      seq("where", commaSep1($.type_constraint)),

    type_constraint: ($) =>
      seq(
        field("type", $._type),
        ":",
        field("bound", $._type),
      ),

    type_definition: ($) =>
      prec.right(choice(
        // Inline form: type Color = Red | Green | Blue
        seq(
          repeat(seq($.annotation, optional($.newline))),
          optional("pub"),
          choice("type", "enum"),
          field("name", $.upper_identifier),
          repeat(field("param", $._type_param)),
          "=",
          sep1($.variant, "|"),
        ),
        // Block form: enum List a\n  Nil\n  Cons(a, List a)
        seq(
          repeat(seq($.annotation, optional($.newline))),
          optional("pub"),
          choice("type", "enum"),
          field("name", $.upper_identifier),
          repeat(field("param", $._type_param)),
          $.indent,
          repeat1(seq($.variant, optional($.newline))),
          $.dedent,
        ),
      )),

    variant: ($) =>
      prec.right(seq(
        field("name", $.upper_identifier),
        optional(seq("(", commaSep($._type), ")")),
      )),

    _type_param: ($) =>
      choice($.identifier, $.upper_identifier),

    struct_definition: ($) =>
      prec.right(seq(
        repeat(seq($.annotation, optional($.newline))),
        optional("pub"),
        "struct",
        field("name", $.upper_identifier),
        repeat(field("param", $._type_param)),
        optional(seq(
          $.indent,
          repeat1(seq(choice($.struct_field, $.function_declaration), optional($.newline))),
          $.dedent,
        )),
      )),

    struct_field: ($) =>
      seq(
        repeat($.annotation),
        field("name", $.identifier),
        ":",
        field("type", $._type),
      ),

    trait_definition: ($) =>
      prec.right(seq(
        repeat(seq($.annotation, optional($.newline))),
        optional("pub"),
        "trait",
        field("name", $.upper_identifier),
        repeat(field("param", $._type_param)),
        optional(seq(":", commaSep1($._type))),
        optional(seq(
          $.indent,
          repeat1(choice(
            seq($.doc_block, optional($.newline)),
            seq($.function_signature, optional($.newline)),
            seq($.type_member, optional($.newline)),
          )),
          $.dedent,
        )),
      )),

    type_member: ($) =>
      seq("type", field("name", $.upper_identifier)),

    // Canonical syntax: Type as Trait
    impl_block: ($) =>
      prec.right(seq(
        repeat(seq($.annotation, optional($.newline))),
        field("target", $.upper_identifier),
        repeat(field("param", $._type_param)),
        "as",
        field("trait", $.upper_identifier),
        optional(seq(
          $.indent,
          repeat1(seq($.function_declaration, optional($.newline))),
          $.dedent,
        )),
      )),

    // Legacy syntax: impl Trait for Type
    legacy_impl_block: ($) =>
      prec.right(seq(
        repeat(seq($.annotation, optional($.newline))),
        "impl",
        field("trait", $._type),
        optional(seq("for", field("target", $._type))),
        optional($.where_clause),
        optional(seq(
          $.indent,
          repeat1(choice(
            seq($.doc_block, optional($.newline)),
            seq($.function_declaration, optional($.newline)),
          )),
          $.dedent,
        )),
      )),

    effect_declaration: ($) =>
      prec.right(seq(
        optional("pub"),
        "effect",
        field("name", $.upper_identifier),
        repeat(field("param", $._type_param)),
        optional(seq(
          $.indent,
          repeat1(choice(
            seq($.doc_block, optional($.newline)),
            seq($.function_signature, optional($.newline)),
          )),
          $.dedent,
        )),
      )),

    alias_declaration: ($) =>
      seq(
        optional("pub"),
        "alias",
        field("name", $.upper_identifier),
        repeat(field("param", $._type_param)),
        "=",
        field("type", $._type),
      ),

    use_declaration: ($) =>
      seq(
        "use",
        field("module", $.upper_identifier),
        optional(
          choice(
            seq(".", "{", commaSep1($.identifier), "}"),
            seq("as", field("alias", $.upper_identifier)),
          ),
        ),
      ),

    test_declaration: ($) =>
      prec.right(seq(
        "test",
        field("name", $.string),
        optional($._block),
      )),

    annotation: ($) =>
      seq(
        "@",
        field("name", $.identifier),
        optional(seq("(", commaSep($._annotation_arg), ")")),
      ),

    _annotation_arg: ($) =>
      choice($.identifier, $.upper_identifier, $.string, $.triple_quoted_string, $.integer),

    // ── Types ─────────────────────────────────────────────────────

    _type: ($) =>
      choice(
        $.named_type,
        $.applied_type,
        $.function_type,
        $.effect_function_type,
        $.fn_type,
        $.fn_effect_type,
        $.row_type,
        $.paren_type,
      ),

    // Simple types for applied_type args and effect_ref args.
    _simple_type: ($) =>
      choice(
        $.named_type,
        $.paren_type,
      ),

    named_type: ($) =>
      choice($.identifier, $.upper_identifier),

    applied_type: ($) =>
      choice(
        // Parenthesized: Result(a, e), Option(Int)
        prec(2, seq(
          field("constructor", $.upper_identifier),
          "(",
          commaSep1(field("arg", $._type)),
          ")",
        )),
        // Space-separated (single arg): Option a, List b
        prec.right(1, seq(
          field("constructor", $.upper_identifier),
          repeat1(field("arg", $._simple_type)),
        )),
      ),

    function_type: ($) =>
      prec.right(seq(
        field("param", $._type),
        "->",
        field("return", $._type),
      )),

    effect_function_type: ($) =>
      prec.right(seq(
        field("param", $._type),
        "-",
        $.effect_row,
        ">",
        field("return", $._type),
      )),

    fn_type: ($) =>
      prec(2, seq(
        "fn",
        "(",
        commaSep($._type),
        ")",
        "->",
        field("return", $._type),
      )),

    fn_effect_type: ($) =>
      prec(2, seq(
        "fn",
        "(",
        commaSep($._type),
        ")",
        "-",
        $.effect_row,
        ">",
        field("return", $._type),
      )),

    row_type: ($) =>
      seq(
        "{",
        commaSep1($.row_type_field),
        optional(seq("|", field("tail", $.identifier))),
        "}",
      ),

    row_type_field: ($) =>
      seq(field("name", $.identifier), ":", field("type", $._type)),

    paren_type: ($) => seq("(", commaSep1($._type), ")"),

    // ── Expressions ───────────────────────────────────────────────

    _expression: ($) =>
      choice(
        $.let_expression,
        $.if_expression,
        $.case_expression,
        $.cond_expression,
        $.handle_expression,
        $.catch_expression,
        $.fail_expression,
        $.for_expression,
        $.while_expression,
        $.lambda_expression,
        $.binary_expression,
        $.unary_expression,
        $._postfix_expression,
        $._primary_expression,
      ),

    let_expression: ($) =>
      prec.right(seq(
        "let",
        field("pattern", $._pattern),
        optional(seq(":", field("type", $._type))),
        "=",
        field("value", $._expression),
        optional(field("body", $._expression)),
      )),

    if_expression: ($) =>
      prec.right(seq(
        "if",
        field("condition", $._expression),
        field("then", choice($._expression, $._block)),
        optional(seq(
          "else",
          field("else", choice($._expression, $._block)),
        )),
      )),

    case_expression: ($) =>
      prec.right(seq(
        "case",
        field("scrutinee", $._expression),
        $.indent,
        repeat1(seq($.case_arm, optional($.newline))),
        $.dedent,
      )),

    case_arm: ($) =>
      prec.right(seq(
        field("pattern", $._pattern),
        optional(seq("when", field("guard", $._expression))),
        "->",
        field("body", choice($._expression, $._block)),
      )),

    cond_expression: ($) =>
      prec.right(seq(
        "cond",
        $.indent,
        repeat1(seq($.cond_arm, optional($.newline))),
        $.dedent,
      )),

    cond_arm: ($) =>
      prec.right(seq(
        field("condition", $._expression),
        "->",
        field("body", choice($._expression, $._block)),
      )),

    handle_expression: ($) =>
      prec.right(seq(
        "handle",
        field("expr", $._expression),
        $.indent,
        repeat1(seq($.operation_clause, optional($.newline))),
        optional(seq($.then_clause, optional($.newline))),
        $.dedent,
      )),

    then_clause: ($) =>
      prec.right(seq(
        "then",
        optional(seq(field("pattern", $._pattern), "->")),
        field("body", choice($._expression, $._block)),
      )),

    operation_clause: ($) =>
      prec.right(seq(
        field("effect", $.upper_identifier),
        ".",
        field("operation", $.identifier),
        optional(seq("(", commaSep($._pattern), ")")),
        "->",
        field("body", choice($._expression, $._block)),
      )),

    resume_expression: ($) =>
      prec.right(seq("resume", field("value", $._expression))),

    catch_expression: ($) =>
      prec.right(seq("catch", field("expr", $._expression))),

    fail_expression: ($) =>
      prec.right(seq("fail", field("value", $._expression))),

    for_expression: ($) =>
      prec.right(seq(
        "for",
        field("pattern", $._pattern),
        "in",
        field("iterable", $._expression),
        optional(seq(",", field("guard", $._expression))),
        field("body", choice($._expression, $._block)),
      )),

    while_expression: ($) =>
      prec.right(seq(
        "while",
        field("condition", $._expression),
        field("body", choice($._expression, $._block)),
      )),

    lambda_expression: ($) =>
      prec.right(seq(
        "|",
        commaSep($.lambda_parameter),
        "|",
        field("body", choice($._expression, $._block)),
      )),

    lambda_parameter: ($) =>
      seq(
        field("pattern", $._pattern),
        optional(seq(":", field("type", $._type))),
      ),

    binary_expression: ($) =>
      choice(
        prec.left(PREC.or, seq($._expression, "or", $._expression)),
        prec.left(PREC.and, seq($._expression, "and", $._expression)),
        prec.left(PREC.equality, seq($._expression, choice("==", "!="), $._expression)),
        prec.left(PREC.comparison, seq($._expression, choice("<", "<=", ">", ">="), $._expression)),
        prec.left(PREC.concat, seq($._expression, choice("++", "<>"), $._expression)),
        prec.left(PREC.additive, seq($._expression, choice("+", "-"), $._expression)),
        prec.left(PREC.multiplicative, seq($._expression, choice("*", "/", "%"), $._expression)),
      ),

    unary_expression: ($) =>
      choice(
        prec(PREC.unary, seq("-", $._expression)),
        prec(PREC.unary, seq("not", $._expression)),
      ),

    _postfix_expression: ($) =>
      choice(
        $.call_expression,
        $.field_expression,
        $.try_expression,
        $.functional_update,
      ),

    call_expression: ($) =>
      prec(PREC.postfix, seq(
        field("function", $._expression),
        "(",
        commaSep($._expression),
        ")",
      )),

    field_expression: ($) =>
      prec(PREC.postfix, seq(
        field("object", $._expression),
        ".",
        field("field", choice($.identifier, $.upper_identifier, $.integer)),
      )),

    try_expression: ($) =>
      prec(PREC.postfix, seq(
        field("expr", $._expression),
        "?",
      )),

    _primary_expression: ($) =>
      choice(
        $.identifier,
        $.constructor_expression,
        $.integer,
        $.float,
        $.string,
        $.triple_quoted_string,
        $.boolean,
        $.none,
        $.unit,
        $.list_expression,
        $.struct_expression,
        $.receiver_placeholder,
        $.resume_expression,
        $.parenthesized_expression,
      ),

    parenthesized_expression: ($) => seq("(", commaSep1($._expression), ")"),

    list_expression: ($) => seq("[", commaSep($._expression), "]"),

    struct_expression: ($) =>
      prec(1, seq(
        field("type", $.upper_identifier),
        "{",
        commaSep($.field_init),
        "}",
      )),

    functional_update: ($) =>
      prec(PREC.postfix, seq(
        field("base", $._expression),
        "~",
        "{",
        commaSep1($.field_init),
        "}",
      )),

    // Bare upper identifier: Some, IO, Ok, None, etc.
    // Constructor application Some(x) parses as call_expression on this.
    constructor_expression: ($) =>
      field("constructor", $.upper_identifier),

    field_init: ($) =>
      seq(
        field("name", $.identifier),
        optional(seq(":", field("value", $._expression))),
      ),

    receiver_placeholder: (_$) => "$",

    // ── Patterns ──────────────────────────────────────────────────

    _pattern: ($) =>
      choice(
        $.wildcard_pattern,
        $.variable_pattern,
        $.literal_pattern,
        $.constructor_pattern,
        $.list_pattern,
        $.struct_pattern,
        $.or_pattern,
        $.as_pattern,
        $.parenthesized_pattern,
      ),

    wildcard_pattern: (_$) => "_",

    variable_pattern: ($) => prec(-1, $.identifier),

    literal_pattern: ($) =>
      prec(-1, choice($.integer, $.float, $.string, $.triple_quoted_string, $.boolean, $.none)),

    constructor_pattern: ($) =>
      prec(-1, seq(
        field("constructor", $.upper_identifier),
        optional(seq("(", commaSep($._pattern), ")")),
      )),

    list_pattern: ($) =>
      prec(-1, seq(
        "[",
        commaSep($._pattern),
        optional(seq("..", field("rest", $.identifier))),
        "]",
      )),

    struct_pattern: ($) =>
      prec(-1, seq(
        optional(field("type", $.upper_identifier)),
        "{",
        commaSep($.field_pattern),
        optional(".."),
        "}",
      )),

    field_pattern: ($) =>
      seq(
        field("name", $.identifier),
        optional(seq(":", field("pattern", $._pattern))),
      ),

    or_pattern: ($) =>
      prec.left(seq($._pattern, "|", $._pattern)),

    as_pattern: ($) =>
      seq($._pattern, "as", field("name", $.identifier)),

    parenthesized_pattern: ($) => seq("(", $._pattern, ")"),

    // ── Block (indentation-delimited) ───────────────────────────

    _block: ($) =>
      seq($.indent, repeat1(seq($._expression, optional($.newline))), $.dedent),

    // ── Terminals ─────────────────────────────────────────────────

    identifier: (_$) => /[a-z_][a-zA-Z0-9_]*/,

    upper_identifier: (_$) => /[A-Z][a-zA-Z0-9_]*/,

    integer: (_$) =>
      token(choice(
        /0[xX][0-9a-fA-F][0-9a-fA-F_]*/,
        /0[bB][01][01_]*/,
        /0[oO][0-7][0-7_]*/,
        /[0-9][0-9_]*/,
      )),

    float: (_$) => token(/[0-9][0-9_]*\.[0-9][0-9_]*([eE][+-]?[0-9]+)?/),

    string: (_$) =>
      token(seq(
        '"',
        repeat(choice(
          /[^"\\]/,
          /\\./,
        )),
        '"',
      )),

    triple_quoted_string: (_$) =>
      token(seq(
        '"""',
        repeat(choice(
          /[^"\\]/,
          /\\./,
          // One quote not followed by two more
          /"[^"]/,
          // Two quotes not followed by a third
          /""[^"]/,
        )),
        '"""',
      )),

    boolean: (_$) => choice("true", "false"),

    none: (_$) => "None",

    unit: (_$) => seq("(", ")"),

    line_comment: (_$) => token(prec(-1, seq("--", /[^\n|][^\n]*/))),

  },
});

// ── Helpers ─────────────────────────────────────────────────────

/**
 * Comma-separated list (possibly empty).
 */
function commaSep(rule) {
  return optional(commaSep1(rule));
}

/**
 * Comma-separated list (at least one).
 */
function commaSep1(rule) {
  return sep1(rule, ",");
}

/**
 * Separated list (at least one).
 */
function sep1(rule, separator) {
  return seq(rule, repeat(seq(separator, rule)));
}


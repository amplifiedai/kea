//! Token types produced by the Kea lexer.

use kea_ast::Span;

/// The kind of a trivia element (whitespace/comment attached to a token).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TriviaKind {
    /// Spaces and tabs (not newlines).
    Whitespace,
    /// A single newline (`\n` or `\r\n`).
    Newline,
    /// A line comment including the `//` prefix.
    LineComment,
}

/// A trivia element — whitespace or comment attached to an adjacent token.
#[derive(Debug, Clone, PartialEq)]
pub struct Trivia {
    pub kind: TriviaKind,
    pub text: String,
    pub span: Span,
}

/// A token with its kind, source span, and attached trivia.
///
/// Leading trivia is whitespace/comments between the previous token and this one.
/// Trailing trivia is same-line whitespace/comments after this token (up to and
/// including the newline).
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub leading_trivia: Vec<Trivia>,
    pub trailing_trivia: Vec<Trivia>,
}

/// Reconstruct source text from tokens with trivia.
///
/// The key invariant: for any source that lexes successfully,
/// `reconstruct_source(&lex(source), source) == source`.
pub fn reconstruct_source(tokens: &[Token], source: &str) -> String {
    let mut output = String::new();
    for token in tokens {
        for t in &token.leading_trivia {
            output.push_str(&t.text);
        }
        // Eof has zero-width span; don't extract source text for it
        if token.kind != TokenKind::Eof {
            let start = token.span.start as usize;
            let end = token.span.end as usize;
            output.push_str(&source[start..end]);
        }
        for t in &token.trailing_trivia {
            output.push_str(&t.text);
        }
    }
    output
}

/// A part of a string interpolation.
#[derive(Debug, Clone, PartialEq)]
pub enum StringPart {
    /// Literal text segment.
    Literal(String),
    /// Expression source text to be parsed.
    Expr(String),
}

/// The kind of a lexical token.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // -- Literals --
    Int(i64),
    Float(f64),
    String(String),
    /// String with interpolation: `"hello ${name}"`.
    StringInterp(Vec<StringPart>),

    // -- Identifiers --
    /// Lowercase-initial identifier: `foo`, `bar_baz`
    Ident(String),
    /// PascalCase identifier: `Some`, `User`, `Ok`
    UpperIdent(String),

    // -- Keywords --
    Let,
    Fn,
    ExprKw,
    TestKw,
    Property,
    Pub,
    If,
    When,
    Else,
    Case,
    Cond,
    True,
    False,
    NoneKw,
    Struct,
    TypeKw,
    Alias,
    Opaque,
    Impl,
    Trait,
    Effect,
    Forall,
    Where,
    Import,
    Deriving,
    Testing,
    Use,
    And,
    Or,
    Not,
    Borrow,
    In,

    // -- Reserved words (KERNEL §16) --
    Sql,
    Html,
    Markdown,
    Spawn,
    Await,
    Stream,
    Yield,
    YieldFrom,
    Assert,
    AssertEq,
    AssertNe,
    AssertFrameEqual,
    AssertSnapshot,
    AssertOk,
    AssertError,

    // -- Operators --
    Plus,      // +
    PlusPlus,  // ++
    Minus,     // -
    Star,      // *
    Slash,     // /
    Percent,   // %
    Tilde,     // ~
    EqEq,      // ==
    BangEq,    // !=
    Lt,        // <
    LtEq,      // <=
    Gt,        // >
    GtEq,      // >=
    DiamondOp, // <>
    Question,  // ?

    // -- Assignment / arrows --
    Eq,        // =
    Arrow,     // ->
    LeftArrow, // <-
    FatArrow,  // =>
    DotDot,    // ..
    DotDotEq,  // ..=

    // -- Delimiters --
    LParen,       // (
    RParen,       // )
    LBrace,       // {
    RBrace,       // }
    LBracket,     // [
    RBracket,     // ]
    HashBracket,  // #[
    HashBrace,    // #{
    PercentBrace, // %{

    // -- Punctuation --
    Colon,      // :
    ColonColon, // ::
    Comma,      // ,
    Dot,        // .
    Pipe,       // |
    Dollar,     // $
    At,         // @

    // -- SQL --
    /// Raw SQL body text collected between `sql {` and matching `}`.
    SqlBody(String),
    /// Raw template body text collected between `html {` and matching `}`.
    HtmlBody(String),
    /// Raw template body text collected between `markdown {` and matching `}`.
    MarkdownBody(String),

    // -- Structural --
    /// Doc comment line: `--| ...` (without the `--|` prefix).
    DocComment(String),
    /// Increase in significant indentation level.
    Indent,
    /// Decrease in significant indentation level.
    Dedent,
    Newline,
    Eof,
}

impl TokenKind {
    /// Returns `true` if this token is a newline.
    pub fn is_newline(&self) -> bool {
        matches!(self, TokenKind::Newline)
    }
}

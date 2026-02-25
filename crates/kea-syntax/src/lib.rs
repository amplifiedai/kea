//! Lexer and recursive descent parser for Kea source code.
//!
//! This crate takes source text and produces an AST defined in `kea-ast`.
//! The parser uses Pratt-style precedence climbing for binary operators.

pub mod chunks;
pub mod lexer;
pub mod parser;
pub mod token;

use kea_ast::{Expr, FileId, Module, Spanned, TypeAnnotation};
use kea_diag::Diagnostic;

pub use chunks::{Chunk, classify_as_declaration, split_chunks};
pub use lexer::{lex, lex_layout};
pub use parser::{parse_expr, parse_module, parse_type};
pub use token::{Token, TokenKind, Trivia, TriviaKind, reconstruct_source};

/// Parse an expression directly from source text using layout-aware lexing.
pub fn parse_expr_source(source: &str, file: FileId) -> Result<Expr, Vec<Diagnostic>> {
    let tokens = lex_layout(source, file)?.0;
    parse_expr(tokens, file)
}

/// Parse a module directly from source text using layout-aware lexing.
pub fn parse_module_source(source: &str, file: FileId) -> Result<Module, Vec<Diagnostic>> {
    let tokens = lex_layout(source, file)?.0;
    parse_module(tokens, file)
}

/// Parse a type annotation directly from source text using layout-aware lexing.
pub fn parse_type_source(
    source: &str,
    file: FileId,
) -> Result<Spanned<TypeAnnotation>, Vec<Diagnostic>> {
    let tokens = lex_layout(source, file)?.0;
    parse_type(tokens, file)
}

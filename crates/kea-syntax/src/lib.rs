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

#[cfg(test)]
mod tests {
    use super::*;
    use kea_ast::{DeclKind, ExprKind};

    #[test]
    fn parse_expr_source_supports_layout_blocks() {
        let expr = parse_expr_source("if true\n  1\nelse\n  2", FileId(0)).expect("parse expr");
        assert!(matches!(expr.node, ExprKind::If { .. }));
    }

    #[test]
    fn parse_module_source_supports_indented_fn_body() {
        let module = parse_module_source("fn id(x) -> Int\n  x", FileId(0)).expect("parse module");
        assert_eq!(module.declarations.len(), 1);
        assert!(matches!(module.declarations[0].node, DeclKind::Function(_)));
    }

    #[test]
    fn parse_type_source_parses_type_annotation() {
        let ty = parse_type_source("List(Int)", FileId(0)).expect("parse type");
        assert!(matches!(ty.node, TypeAnnotation::Applied(_, _)));
    }
}

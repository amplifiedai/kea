//! Lexer and recursive descent parser for Kea source code.
//!
//! This crate takes source text and produces an AST defined in `kea-ast`.
//! The parser uses Pratt-style precedence climbing for binary operators.

pub mod chunks;
pub mod lexer;
pub mod parser;
pub mod token;

pub use chunks::{Chunk, classify_as_declaration, split_chunks};
pub use lexer::{lex, lex_layout};
pub use parser::{parse_expr, parse_module, parse_type};
pub use token::{Token, TokenKind, Trivia, TriviaKind, reconstruct_source};

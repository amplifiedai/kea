//! Source splitting for script-style Kea files.
//!
//! Splits source code into logical chunks (declarations and expressions)
//! separated by blank lines at brace depth 0. Used by the CLI runner,
//! formatter, and LSP.

use kea_ast::FileId;

use crate::token::TokenKind;

/// A chunk of source code with its byte offset in the original source.
#[derive(Debug, Clone)]
pub struct Chunk {
    /// Byte offset of this chunk's first character in the original source.
    pub offset: u32,
    /// The chunk text.
    pub text: String,
}

/// Classify a token stream as a declaration (vs expression).
///
/// Returns `true` if the first significant token indicates a declaration:
/// `fn`, `pub fn`, `record`, `pub record`, `type`, `pub type`,
/// `alias`, `pub alias`, `opaque`, `pub opaque`, `trait`, `pub trait`, `impl`,
/// `test`, or `import`.
pub fn classify_as_declaration(tokens: &[crate::Token]) -> bool {
    // Skip newlines, doc comments, and leading #[...] blocks to find the
    // first "significant" token. This ensures `/// doc\nrecord Foo { ... }`
    // is correctly classified as a declaration even for malformed input.
    let mut iter = tokens
        .iter()
        .filter(|t| !t.kind.is_newline())
        .map(|t| &t.kind)
        .peekable();

    // Skip leading doc comments.
    while matches!(iter.peek(), Some(TokenKind::DocComment(_))) {
        iter.next();
    }

    // Skip #[...] attribute blocks.
    while matches!(iter.peek(), Some(TokenKind::HashBracket)) {
        iter.next(); // consume #[
        let mut depth = 1i32;
        while depth > 0 {
            match iter.next() {
                Some(TokenKind::LBracket) | Some(TokenKind::LParen) => depth += 1,
                Some(TokenKind::RBracket) | Some(TokenKind::RParen) => depth -= 1,
                None => break,
                _ => {}
            }
        }
    }

    // Skip leading @annotation(...) blocks.
    while matches!(iter.peek(), Some(TokenKind::At)) {
        iter.next(); // consume '@'
        match iter.peek() {
            Some(TokenKind::Ident(_)) | Some(TokenKind::UpperIdent(_)) => {
                iter.next();
            }
            _ => break,
        }

        if matches!(iter.peek(), Some(TokenKind::LParen)) {
            iter.next(); // consume '('
            let mut depth = 1i32;
            while depth > 0 {
                match iter.next() {
                    Some(TokenKind::LParen) => depth += 1,
                    Some(TokenKind::RParen) => depth -= 1,
                    None => break,
                    _ => {}
                }
            }
        }

        while matches!(iter.peek(), Some(TokenKind::Newline)) {
            iter.next();
        }
    }

    let first = iter.next();
    let second = iter.next();

    matches!(first, Some(TokenKind::Import))
        || matches!(first, Some(TokenKind::Record))
        || matches!(first, Some(TokenKind::TypeKw))
        || matches!(first, Some(TokenKind::Alias))
        || matches!(first, Some(TokenKind::Opaque))
        || matches!(first, Some(TokenKind::Trait))
        || matches!(first, Some(TokenKind::Impl))
        || matches!(first, Some(TokenKind::TestKw))
        || matches!(first, Some(TokenKind::Fn))
        || matches!(first, Some(TokenKind::ExprKw))
        || (matches!(first, Some(TokenKind::Pub))
            && matches!(
                second,
                Some(
                    TokenKind::Fn
                        | TokenKind::ExprKw
                        | TokenKind::Record
                        | TokenKind::TypeKw
                        | TokenKind::Alias
                        | TokenKind::Opaque
                        | TokenKind::Trait
                )
            ))
}

fn line_starts_with_continuation(trimmed: &str) -> bool {
    matches!(
        trimmed,
        s if s.starts_with("|>")
            || s.starts_with("&&")
            || s.starts_with("||")
            || s.starts_with("==")
            || s.starts_with("!=")
            || s.starts_with("<=")
            || s.starts_with(">=")
            || s.starts_with("->")
            || s.starts_with('+')
            || s.starts_with('-')
            || s.starts_with('*')
            || s.starts_with('/')
            || s.starts_with('%')
            || s.starts_with('|')
            || s.starts_with('.')
    )
}

fn line_ends_with_continuation(trimmed: &str) -> bool {
    trimmed.ends_with("|>")
        || trimmed.ends_with('=')
        || trimmed.ends_with(',')
        || trimmed.ends_with('|')
        || trimmed.ends_with("->")
}

/// Split source into chunks separated by blank lines at brace depth 0.
///
/// Each chunk carries its byte offset in the original source.
/// Declaration chunks (fn, record, type, trait, impl, import) can span
/// multiple non-blank lines. Expression chunks are further split by
/// newlines at depth 0 since each line is a standalone expression.
pub fn split_chunks(source: &str) -> Vec<Chunk> {
    // Phase 1: Split at blank lines at depth 0.
    let mut raw_chunks: Vec<Chunk> = Vec::new();
    let mut current = String::new();
    let mut current_offset: u32 = 0;
    let mut depth: i32 = 0;
    let mut byte_pos: u32 = 0;
    let mut chunk_started = false;

    for line in source.lines() {
        let trimmed = line.trim();
        let line_len = line.len() as u32;

        // Blank line at depth 0 = chunk boundary.
        if trimmed.is_empty() && depth == 0 {
            if !current.trim().is_empty() {
                raw_chunks.push(Chunk {
                    offset: current_offset,
                    text: std::mem::take(&mut current),
                });
                chunk_started = false;
            }
            // +1 for the newline character
            byte_pos += line_len + 1;
            continue;
        }

        // Track brace depth.
        for ch in trimmed.chars() {
            match ch {
                '{' | '(' | '[' => depth += 1,
                '}' | ')' | ']' => depth -= 1,
                _ => {}
            }
        }

        if !chunk_started {
            current_offset = byte_pos;
            chunk_started = true;
        }

        if !current.is_empty() {
            current.push('\n');
        }
        current.push_str(line);
        byte_pos += line_len + 1; // +1 for newline
    }

    if !current.trim().is_empty() {
        raw_chunks.push(Chunk {
            offset: current_offset,
            text: current,
        });
    }

    // Phase 2: For expression chunks (non-declarations) that have multiple
    // lines, split further by newlines at depth 0. This handles consecutive
    // expressions like `send(c, :inc)\nsend(c, :inc)` on adjacent lines.
    let mut chunks = Vec::new();
    let file = FileId(0);
    for chunk in raw_chunks {
        let trimmed = chunk.text.trim();
        if trimmed.is_empty() {
            continue;
        }
        // Comment-only chunks stay as-is.
        if trimmed
            .lines()
            .all(|l| l.trim().starts_with("//") || l.trim().is_empty())
        {
            chunks.push(chunk);
            continue;
        }
        // Check if this is a declaration chunk.
        if let Ok((tokens, _)) = crate::lex(trimmed, file)
            && classify_as_declaration(&tokens)
        {
            chunks.push(chunk);
            continue;
        }
        // Expression chunk: split by newlines at depth 0.
        let mut sub = String::new();
        let mut sub_offset = chunk.offset;
        let mut sub_depth: i32 = 0;
        let mut line_byte_pos = chunk.offset;
        let mut prev_nonempty_trimmed: Option<String> = None;
        for line in chunk.text.lines() {
            let lt = line.trim();
            let prev_continues = prev_nonempty_trimmed
                .as_deref()
                .map(line_ends_with_continuation)
                .unwrap_or(false);
            let line_continues = line_starts_with_continuation(lt);
            if sub_depth == 0 && !sub.trim().is_empty() && !prev_continues && !line_continues {
                chunks.push(Chunk {
                    offset: sub_offset,
                    text: std::mem::take(&mut sub),
                });
                sub_offset = line_byte_pos;
            }
            if !sub.is_empty() {
                sub.push('\n');
            }
            sub.push_str(line);
            for ch in lt.chars() {
                match ch {
                    '{' | '(' | '[' => sub_depth += 1,
                    '}' | ')' | ']' => sub_depth -= 1,
                    _ => {}
                }
            }
            if !lt.is_empty() {
                prev_nonempty_trimmed = Some(lt.to_string());
            }
            line_byte_pos += line.len() as u32 + 1; // +1 for newline
        }
        if !sub.trim().is_empty() {
            chunks.push(Chunk {
                offset: sub_offset,
                text: sub,
            });
        }
    }

    chunks
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_expression() {
        let chunks = split_chunks("let x = 42\n");
        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].offset, 0);
        assert_eq!(chunks[0].text.trim(), "let x = 42");
    }

    #[test]
    fn two_chunks_blank_separated() {
        let source = "let x = 1\n\nlet y = 2\n";
        let chunks = split_chunks(source);
        assert_eq!(chunks.len(), 2);
        assert_eq!(chunks[0].offset, 0);
        assert_eq!(chunks[0].text.trim(), "let x = 1");
        assert_eq!(chunks[1].offset, 11); // "let x = 1\n\n" = 11 bytes
        assert_eq!(chunks[1].text.trim(), "let y = 2");
    }

    #[test]
    fn duplicate_text_different_offsets() {
        let source = "let x = 1\n\nlet x = 1\n";
        let chunks = split_chunks(source);
        assert_eq!(chunks.len(), 2);
        assert_eq!(chunks[0].offset, 0);
        assert_eq!(chunks[1].offset, 11);
        // Both have the same text but different offsets.
        assert_eq!(chunks[0].text.trim(), chunks[1].text.trim());
    }

    #[test]
    fn function_declaration_stays_together() {
        let source = "fn add(x, y) -> Int {\n  x + y\n}\n";
        let chunks = split_chunks(source);
        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].offset, 0);
    }

    #[test]
    fn consecutive_expressions_split() {
        let source = "send(c, :inc)\nsend(c, :inc)\n";
        let chunks = split_chunks(source);
        assert_eq!(chunks.len(), 2);
        assert_eq!(chunks[0].offset, 0);
        assert_eq!(chunks[0].text.trim(), "send(c, :inc)");
        assert_eq!(chunks[1].offset, 14); // "send(c, :inc)\n" = 14 bytes
        assert_eq!(chunks[1].text.trim(), "send(c, :inc)");
    }

    #[test]
    fn pipeline_continuation_line_not_split() {
        let source = "let pipeline = employees\n  |> filter(:active == true)\npipeline\n";
        let chunks = split_chunks(source);
        assert_eq!(chunks.len(), 2);
        assert!(chunks[0].text.contains("|> filter"));
        assert_eq!(chunks[1].text.trim(), "pipeline");
    }

    #[test]
    fn multiline_lambda_expression_not_split() {
        let source = "let f = x ->\n  x + 1\nf(1)\n";
        let chunks = split_chunks(source);
        assert_eq!(chunks.len(), 2);
        assert!(chunks[0].text.contains("x ->"));
        assert_eq!(chunks[1].text.trim(), "f(1)");
    }

    #[test]
    fn multiline_record_expression_not_split() {
        let source = "let r = #{\n  a: 1,\n  b: 2\n}\nr\n";
        let chunks = split_chunks(source);
        assert_eq!(chunks.len(), 2);
        assert!(chunks[0].text.contains("let r = #{"));
        assert_eq!(chunks[1].text.trim(), "r");
    }

    #[test]
    fn classify_expr_as_declaration() {
        let tokens = crate::lex("expr double(x: Int) -> Int { x + x }", FileId(0))
            .unwrap()
            .0;
        assert!(classify_as_declaration(&tokens));
    }

    #[test]
    fn classify_pub_expr_as_declaration() {
        let tokens = crate::lex("pub expr add(x: Int, y: Int) -> Int { x + y }", FileId(0))
            .unwrap()
            .0;
        assert!(classify_as_declaration(&tokens));
    }

    #[test]
    fn classify_alias_as_declaration() {
        let tokens = crate::lex("alias UserId = Int", FileId(0)).unwrap().0;
        assert!(classify_as_declaration(&tokens));
    }

    #[test]
    fn classify_opaque_as_declaration() {
        let tokens = crate::lex("opaque UserId = Int", FileId(0)).unwrap().0;
        assert!(classify_as_declaration(&tokens));
    }

    #[test]
    fn classify_test_as_declaration() {
        let tokens = crate::lex(r#"test "smoke" { assert true }"#, FileId(0))
            .unwrap()
            .0;
        assert!(classify_as_declaration(&tokens));
    }

    #[test]
    fn classify_annotated_declaration_as_declaration() {
        let tokens = crate::lex("@deprecated(\"use new_api\")\nfn old(x: Int) -> Int { x }", FileId(0))
            .unwrap()
            .0;
        assert!(classify_as_declaration(&tokens));
    }

    #[test]
    fn expr_declaration_stays_together() {
        let source = "expr f(x: Int) -> Int {\n  x + 1\n}\n";
        let chunks = split_chunks(source);
        assert_eq!(chunks.len(), 1);
    }

    #[test]
    fn expr_ident_not_declaration() {
        // "expr" as a variable name should NOT be classified as a declaration
        // (but it will lex as ExprKw, so it IS classified as one).
        // This is expected — `expr` is a reserved keyword.
        let tokens = crate::lex("expr", FileId(0)).unwrap().0;
        assert!(classify_as_declaration(&tokens));
    }
}

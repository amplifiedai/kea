//! Hand-written lexer for Kea source code.

use kea_ast::{FileId, Span};
use kea_diag::{Category, Diagnostic};

use crate::token::{Token, TokenKind, Trivia, TriviaKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockBodyKind {
    Sql,
    Html,
    Markdown,
}

/// Lex source text into a sequence of tokens.
///
/// Returns `Ok(tokens)` where the last token is always `Eof`.
/// Returns `Err` with diagnostics for lexical errors.
/// Lex source text into a sequence of tokens.
///
/// Returns `Ok((tokens, warnings))` on success. Warnings (like missing `$` in
/// interpolation) are non-fatal and returned alongside tokens.
/// Returns `Err` with diagnostics only when there are actual errors.
pub fn lex(source: &str, file: FileId) -> Result<(Vec<Token>, Vec<Diagnostic>), Vec<Diagnostic>> {
    let mut lexer = Lexer::new(source, file);
    lexer.scan_all();
    let has_errors = lexer
        .errors
        .iter()
        .any(|d| d.severity == kea_diag::Severity::Error);
    if has_errors {
        Err(lexer.errors)
    } else {
        let warnings = lexer.errors;
        Ok((lexer.tokens, warnings))
    }
}

/// Lex source text and apply indentation layout rules.
///
/// This keeps `lex` as the raw token stream and layers significant-whitespace
/// handling on top so parser migration can happen incrementally.
pub fn lex_layout(
    source: &str,
    file: FileId,
) -> Result<(Vec<Token>, Vec<Diagnostic>), Vec<Diagnostic>> {
    let (tokens, mut warnings) = lex(source, file)?;
    let (tokens, mut diagnostics) = apply_layout(tokens, source, file);
    let has_errors = diagnostics
        .iter()
        .any(|d| d.severity == kea_diag::Severity::Error);
    if has_errors {
        diagnostics.extend(warnings);
        Err(diagnostics)
    } else {
        warnings.extend(diagnostics);
        Ok((tokens, warnings))
    }
}

fn apply_layout(tokens: Vec<Token>, source: &str, file: FileId) -> (Vec<Token>, Vec<Diagnostic>) {
    let mut out = Vec::with_capacity(tokens.len() + 8);
    let mut diagnostics = Vec::new();
    let mut indent_stack: Vec<u32> = vec![0];
    let mut delim_depth: usize = 0;

    for (idx, token) in tokens.iter().enumerate() {
        if token.kind == TokenKind::Eof {
            let anchor = token.span.start as usize;
            while indent_stack.len() > 1 {
                indent_stack.pop();
                out.push(layout_token(TokenKind::Dedent, file, anchor));
            }
            out.push(token.clone());
            continue;
        }

        out.push(token.clone());
        update_delimiter_depth(&token.kind, &mut delim_depth);

        if token.kind != TokenKind::Newline {
            continue;
        }
        if delim_depth > 0 {
            continue;
        }

        let Some(next) = next_non_newline_token(&tokens, idx + 1) else {
            continue;
        };
        if next.kind == TokenKind::Eof {
            continue;
        }
        if previous_line_continues_expression(&tokens, idx) {
            continue;
        }
        if next.kind == TokenKind::Dot {
            // Kea method-chain continuation line:
            // expr
            //   .map(...)
            continue;
        }

        let line_start = line_start_offset(source, next.span.start as usize);
        let indent = match measure_indent(source, line_start, next.span.start as usize) {
            Ok(indent) => indent,
            Err(tab_offset) => {
                diagnostics.push(
                    Diagnostic::error(Category::Syntax, "tabs are not allowed in indentation")
                        .at(kea_diag::SourceLocation {
                            file_id: file.0,
                            start: tab_offset as u32,
                            end: (tab_offset + 1) as u32,
                        })
                        .with_help("replace tabs with spaces"),
                );
                continue;
            }
        };

        let current = *indent_stack
            .last()
            .expect("indent stack is never empty in layout pass");
        let anchor = next.span.start as usize;
        if indent > current {
            indent_stack.push(indent);
            out.push(layout_token(TokenKind::Indent, file, anchor));
            continue;
        }
        if indent < current {
            while indent < *indent_stack
                .last()
                .expect("indent stack is never empty in layout pass")
            {
                indent_stack.pop();
                out.push(layout_token(TokenKind::Dedent, file, anchor));
            }
            if indent
                != *indent_stack
                    .last()
                    .expect("indent stack is never empty in layout pass")
            {
                diagnostics.push(
                    Diagnostic::error(
                        Category::Syntax,
                        format!(
                            "inconsistent indentation: expected one of {:?} spaces, got {}",
                            indent_stack, indent
                        ),
                    )
                    .at(kea_diag::SourceLocation {
                        file_id: file.0,
                        start: line_start as u32,
                        end: next.span.start,
                    }),
                );
            }
        }
    }

    (out, diagnostics)
}

fn layout_token(kind: TokenKind, file: FileId, pos: usize) -> Token {
    Token {
        kind,
        span: Span::new(file, pos as u32, pos as u32),
        leading_trivia: Vec::new(),
        trailing_trivia: Vec::new(),
    }
}

fn next_non_newline_token(tokens: &[Token], mut idx: usize) -> Option<&Token> {
    while let Some(tok) = tokens.get(idx) {
        if tok.kind != TokenKind::Newline {
            return Some(tok);
        }
        idx += 1;
    }
    None
}

fn previous_non_newline_token(tokens: &[Token], newline_idx: usize) -> Option<&Token> {
    if newline_idx == 0 {
        return None;
    }
    let mut idx = newline_idx - 1;
    loop {
        let tok = tokens.get(idx)?;
        if tok.kind != TokenKind::Newline {
            return Some(tok);
        }
        if idx == 0 {
            return None;
        }
        idx -= 1;
    }
}

fn previous_line_continues_expression(tokens: &[Token], newline_idx: usize) -> bool {
    let Some(prev) = previous_non_newline_token(tokens, newline_idx) else {
        return false;
    };

    matches!(
        &prev.kind,
        TokenKind::Plus
            | TokenKind::PlusPlus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::Slash
            | TokenKind::Percent
            | TokenKind::EqEq
            | TokenKind::BangEq
            | TokenKind::Lt
            | TokenKind::LtEq
            | TokenKind::Gt
            | TokenKind::GtEq
            | TokenKind::DiamondOp
            | TokenKind::And
            | TokenKind::Or
            | TokenKind::In
            | TokenKind::DotDot
            | TokenKind::DotDotEq
            | TokenKind::Eq
            | TokenKind::LeftArrow
            | TokenKind::Comma
            | TokenKind::Colon
            | TokenKind::Dot
            | TokenKind::Pipe
    )
}

fn line_start_offset(source: &str, offset: usize) -> usize {
    source[..offset]
        .rfind('\n')
        .map_or(0, |line_break| line_break + 1)
}

fn measure_indent(source: &str, start: usize, end: usize) -> Result<u32, usize> {
    let mut indent = 0_u32;
    for (idx, byte) in source.as_bytes()[start..end].iter().enumerate() {
        match byte {
            b' ' => indent += 1,
            b'\t' => return Err(start + idx),
            _ => break,
        }
    }
    Ok(indent)
}

fn update_delimiter_depth(kind: &TokenKind, depth: &mut usize) {
    match kind {
        TokenKind::LParen
        | TokenKind::LBracket
        | TokenKind::LBrace
        | TokenKind::HashBracket
        | TokenKind::HashParen
        | TokenKind::HashBrace
        | TokenKind::PercentBrace => *depth += 1,
        TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
            *depth = depth.saturating_sub(1);
        }
        _ => {}
    }
}

struct Lexer<'src> {
    source: &'src [u8],
    file: FileId,
    pos: usize,
    tokens: Vec<Token>,
    errors: Vec<Diagnostic>,
    /// Accumulated trivia to attach as leading trivia on the next emitted token.
    pending_trivia: Vec<Trivia>,
}

impl<'src> Lexer<'src> {
    fn new(source: &'src str, file: FileId) -> Self {
        Self {
            source: source.as_bytes(),
            file,
            pos: 0,
            tokens: Vec::new(),
            errors: Vec::new(),
            pending_trivia: Vec::new(),
        }
    }

    fn scan_all(&mut self) {
        loop {
            self.collect_whitespace();
            if self.is_at_end() {
                self.emit(TokenKind::Eof, self.pos, self.pos);
                break;
            }
            self.scan_token();
        }
        self.redistribute_trailing_trivia();
    }

    fn scan_token(&mut self) {
        let start = self.pos;
        let ch = self.advance();

        match ch {
            b'\n' => {
                // The first \n is covered by the Newline token's span.
                // Additional \n characters (blank lines) become trivia.
                // Spaces/tabs after the last \n are indentation — they'll be
                // collected by collect_whitespace() at the top of scan_all().
                let newline_end = self.pos; // end of the first \n
                while self.peek() == Some(b'\n') || self.peek() == Some(b'\r') {
                    let extra_start = self.pos;
                    let ch = self.advance();
                    let (kind, text) = match ch {
                        b'\n' => (TriviaKind::Newline, "\n".to_string()),
                        _ => (TriviaKind::Whitespace, "\r".to_string()),
                    };
                    self.pending_trivia.push(Trivia {
                        kind,
                        text,
                        span: Span::new(self.file, extra_start as u32, self.pos as u32),
                    });
                }
                // Don't emit newline if last token was already a newline or there are no tokens yet
                if !self.tokens.is_empty() && !self.last_is_newline() {
                    self.emit(TokenKind::Newline, start, newline_end);
                } else {
                    // No Newline token emitted — the first \n still needs to be
                    // preserved as trivia for lossless round-trip reconstruction.
                    self.pending_trivia.push(Trivia {
                        kind: TriviaKind::Newline,
                        text: "\n".to_string(),
                        span: Span::new(self.file, start as u32, newline_end as u32),
                    });
                }
            }
            b'\r' => {
                // Carriage return — collect as trivia for lossless round-trip
                self.pending_trivia.push(Trivia {
                    kind: TriviaKind::Whitespace,
                    text: "\r".to_string(),
                    span: Span::new(self.file, start as u32, self.pos as u32),
                });
            }

            // Single-char tokens (with multi-char lookahead)
            b'+' => {
                if self.match_char(b'+') {
                    self.emit(TokenKind::PlusPlus, start, self.pos);
                } else {
                    self.emit(TokenKind::Plus, start, self.pos);
                }
            }
            b'*' => self.emit(TokenKind::Star, start, self.pos),
            b'%' => {
                if self.peek() == Some(b'{') {
                    self.advance(); // consume '{'
                    self.emit(TokenKind::PercentBrace, start, self.pos);
                } else {
                    self.emit(TokenKind::Percent, start, self.pos);
                }
            }
            b'(' => self.emit(TokenKind::LParen, start, self.pos),
            b')' => self.emit(TokenKind::RParen, start, self.pos),
            b'{' => {
                if let Some(kind) = self.last_non_newline_block_kind() {
                    self.scan_block_body(start, kind);
                } else {
                    self.emit(TokenKind::LBrace, start, self.pos);
                }
            }
            b'}' => self.emit(TokenKind::RBrace, start, self.pos),
            b'[' => self.emit(TokenKind::LBracket, start, self.pos),
            b']' => self.emit(TokenKind::RBracket, start, self.pos),
            b':' => self.emit(TokenKind::Colon, start, self.pos),
            b',' => self.emit(TokenKind::Comma, start, self.pos),
            b'?' => self.emit(TokenKind::Question, start, self.pos),
            b'@' => self.emit(TokenKind::At, start, self.pos),
            b'$' => {
                self.emit(TokenKind::Dollar, start, self.pos);
            }

            // Two-char possibilities
            b'-' => {
                if self.match_char(b'>') {
                    self.emit(TokenKind::Arrow, start, self.pos);
                } else if self.match_char(b'-') {
                    if self.match_char(b'|') {
                        // Kea doc comment line: `--| ...`
                        let content_start = self.pos;
                        while self.peek() != Some(b'\n') && !self.is_at_end() {
                            self.advance();
                        }
                        let raw = std::str::from_utf8(&self.source[content_start..self.pos])
                            .expect("lexer source is guaranteed UTF-8");
                        let content = raw.strip_prefix(' ').unwrap_or(raw).to_string();
                        self.emit(TokenKind::DocComment(content), start, self.pos);
                    } else {
                        // Kea line comment: `-- ...`
                        while self.peek() != Some(b'\n') && !self.is_at_end() {
                            self.advance();
                        }
                        let comment_text = std::str::from_utf8(&self.source[start..self.pos])
                            .expect("lexer source is guaranteed UTF-8")
                            .to_string();
                        self.pending_trivia.push(Trivia {
                            kind: TriviaKind::LineComment,
                            text: comment_text,
                            span: Span::new(self.file, start as u32, self.pos as u32),
                        });
                    }
                } else {
                    self.emit(TokenKind::Minus, start, self.pos);
                }
            }
            b'=' => {
                if self.match_char(b'=') {
                    self.emit(TokenKind::EqEq, start, self.pos);
                } else if self.match_char(b'>') {
                    self.emit(TokenKind::FatArrow, start, self.pos);
                } else {
                    self.emit(TokenKind::Eq, start, self.pos);
                }
            }
            b'!' => {
                if self.match_char(b'=') {
                    self.emit(TokenKind::BangEq, start, self.pos);
                } else {
                    self.error(start, "unexpected character '!'; use 'not' instead");
                }
            }
            b'<' => {
                if self.match_char(b'>') {
                    self.emit(TokenKind::DiamondOp, start, self.pos);
                } else if self.match_char(b'-') {
                    self.emit(TokenKind::LeftArrow, start, self.pos);
                } else if self.match_char(b'=') {
                    self.emit(TokenKind::LtEq, start, self.pos);
                } else {
                    self.emit(TokenKind::Lt, start, self.pos);
                }
            }
            b'>' => {
                if self.match_char(b'=') {
                    self.emit(TokenKind::GtEq, start, self.pos);
                } else {
                    self.emit(TokenKind::Gt, start, self.pos);
                }
            }
            b'&' => {
                if self.match_char(b'&') {
                    self.error(start, "operator '&&' is not supported; use 'and' instead");
                } else {
                    self.error(start, "unexpected character '&'; use 'and' instead");
                }
            }
            b'|' => {
                self.emit(TokenKind::Pipe, start, self.pos);
            }
            b'.' => {
                if self.match_char(b'.') {
                    if self.match_char(b'=') {
                        self.emit(TokenKind::DotDotEq, start, self.pos);
                    } else {
                        self.emit(TokenKind::DotDot, start, self.pos);
                    }
                } else {
                    self.emit(TokenKind::Dot, start, self.pos);
                }
            }
            b'#' => {
                if self.match_char(b'[') {
                    self.emit(TokenKind::HashBracket, start, self.pos);
                } else if self.match_char(b'(') {
                    self.emit(TokenKind::HashParen, start, self.pos);
                } else if self.match_char(b'{') {
                    self.emit(TokenKind::HashBrace, start, self.pos);
                } else {
                    self.error(
                        start,
                        "unexpected character '#'; expected '#[', '#(', or '#{'",
                    );
                }
            }

            // Comments
            b'/' => {
                if self.match_char(b'/') {
                    // Legacy line comment support (`// ...`) retained during migration.
                    while self.peek() != Some(b'\n') && !self.is_at_end() {
                        self.advance();
                    }
                    let comment_text = std::str::from_utf8(&self.source[start..self.pos])
                        .expect("lexer source is guaranteed UTF-8")
                        .to_string();
                    self.pending_trivia.push(Trivia {
                        kind: TriviaKind::LineComment,
                        text: comment_text,
                        span: Span::new(self.file, start as u32, self.pos as u32),
                    });
                } else {
                    self.emit(TokenKind::Slash, start, self.pos);
                }
            }

            // String literals
            b'"' => self.scan_string(start),

            // Numbers
            b'0'..=b'9' => self.scan_number(start),

            // Identifiers and keywords
            b'a'..=b'z' | b'_' => self.scan_ident(start),

            // Upper identifiers
            b'A'..=b'Z' => self.scan_upper_ident(start),

            _ => {
                self.error(start, format!("unexpected character '{}'", ch as char));
            }
        }
    }

    fn scan_string(&mut self, start: usize) {
        let mut current_lit = String::new();
        let mut parts: Vec<crate::token::StringPart> = Vec::new();
        let mut has_interp = false;

        loop {
            if self.is_at_end() {
                self.error(start, "unterminated string literal");
                return;
            }
            let ch = self.advance();
            match ch {
                b'"' => break,
                b'\\' => {
                    if self.is_at_end() {
                        self.error(start, "unterminated string literal");
                        return;
                    }
                    let esc = self.advance();
                    match esc {
                        b'n' => current_lit.push('\n'),
                        b't' => current_lit.push('\t'),
                        b'\\' => current_lit.push('\\'),
                        b'"' => current_lit.push('"'),
                        _ => {
                            self.error(
                                self.pos - 1,
                                format!("unknown escape sequence '\\{}'", esc as char),
                            );
                        }
                    }
                }
                b'$' if self.match_char(b'{') => {
                    has_interp = true;
                    if !current_lit.is_empty() {
                        parts.push(crate::token::StringPart::Literal(std::mem::take(
                            &mut current_lit,
                        )));
                    }
                    // Collect expression text until matching '}'
                    let mut depth = 1u32;
                    let mut expr_text = String::new();
                    loop {
                        if self.is_at_end() {
                            self.error(start, "unterminated interpolation in string");
                            return;
                        }
                        let c = self.advance();
                        match c {
                            b'{' => {
                                depth += 1;
                                expr_text.push('{');
                            }
                            b'}' => {
                                depth -= 1;
                                if depth == 0 {
                                    break;
                                }
                                expr_text.push('}');
                            }
                            _ => expr_text.push(c as char),
                        }
                    }
                    parts.push(crate::token::StringPart::Expr(expr_text));
                }
                b'\n' => {
                    self.error(start, "unterminated string literal (newline in string)");
                    return;
                }
                b'{' => {
                    // Warn if this looks like a missing $ interpolation
                    if let Some(name) = self.looks_like_interpolation(self.pos - 1) {
                        let brace_pos = self.pos - 1;
                        let end_pos = self.pos + name.len() + 1; // } char
                        self.warning(
                            brace_pos,
                            end_pos,
                            format!(
                                "did you mean ${{{name}}}? \
                                 Use ${{{name}}} for interpolation, \
                                 or \\{{ for a literal brace"
                            ),
                        );
                    }
                    current_lit.push('{');
                }
                _ => current_lit.push(ch as char),
            }
        }

        if has_interp {
            if !current_lit.is_empty() {
                parts.push(crate::token::StringPart::Literal(current_lit));
            }
            self.emit(TokenKind::StringInterp(parts), start, self.pos);
        } else {
            self.emit(TokenKind::String(current_lit), start, self.pos);
        }
    }

    fn scan_number(&mut self, start: usize) {
        while self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.advance();
        }
        // Check for float: `.` followed by a digit
        if self.peek() == Some(b'.') && self.peek_next().is_some_and(|c| c.is_ascii_digit()) {
            self.advance(); // consume '.'
            while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                self.advance();
            }
            let text = &self.source[start..self.pos];
            let text = std::str::from_utf8(text).unwrap();
            match text.parse::<f64>() {
                Ok(v) => self.emit(TokenKind::Float(v), start, self.pos),
                Err(_) => self.error(start, format!("invalid float literal: {text}")),
            }
        } else {
            let text = &self.source[start..self.pos];
            let text = std::str::from_utf8(text).unwrap();
            match text.parse::<i64>() {
                Ok(v) => self.emit(TokenKind::Int(v), start, self.pos),
                Err(_) => self.error(start, format!("invalid integer literal: {text}")),
            }
        }
    }

    fn scan_ident(&mut self, start: usize) {
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_')
        {
            self.advance();
        }
        let text = std::str::from_utf8(&self.source[start..self.pos]).unwrap();
        let kind = match text {
            "let" => TokenKind::Let,
            "fn" => TokenKind::Fn,
            "expr" => TokenKind::ExprKw,
            "test" => TokenKind::TestKw,
            "property" => TokenKind::Property,
            "pub" => TokenKind::Pub,
            "if" => TokenKind::If,
            "when" => TokenKind::When,
            "else" => TokenKind::Else,
            "case" => TokenKind::Case,
            "cond" => TokenKind::Cond,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "record" => TokenKind::Record,
            "type" => TokenKind::TypeKw,
            "alias" => TokenKind::Alias,
            "opaque" => TokenKind::Opaque,
            "impl" => TokenKind::Impl,
            "trait" => TokenKind::Trait,
            "forall" => TokenKind::Forall,
            "where" => TokenKind::Where,
            "import" => TokenKind::Import,
            "deriving" => TokenKind::Deriving,
            "testing" => TokenKind::Testing,
            "use" => TokenKind::Use,
            "and" => TokenKind::And,
            "or" => TokenKind::Or,
            "not" => TokenKind::Not,
            "in" => TokenKind::In,
            "nil" => {
                self.error(start, "`nil` is not supported; use `None`");
                return;
            }
            "sql" => TokenKind::Sql,
            "html" => TokenKind::Html,
            "markdown" => TokenKind::Markdown,
            "spawn" => TokenKind::Spawn,
            "await" => TokenKind::Await,
            "stream" => TokenKind::Stream,
            "yield" => TokenKind::Yield,
            "yield_from" => TokenKind::YieldFrom,
            "assert" => TokenKind::Assert,
            "assert_eq" => TokenKind::AssertEq,
            "assert_ne" => TokenKind::AssertNe,
            "assert_frame_equal" => TokenKind::AssertFrameEqual,
            "assert_snapshot" => TokenKind::AssertSnapshot,
            "assert_ok" => TokenKind::AssertOk,
            "assert_error" => TokenKind::AssertError,
            _ => TokenKind::Ident(text.to_string()),
        };
        self.emit(kind, start, self.pos);
    }

    fn scan_upper_ident(&mut self, start: usize) {
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_')
        {
            self.advance();
        }
        let text = std::str::from_utf8(&self.source[start..self.pos]).unwrap();
        let kind = match text {
            "True" => TokenKind::True,
            "False" => TokenKind::False,
            "None" => TokenKind::NoneKw,
            _ => TokenKind::UpperIdent(text.to_string()),
        };
        self.emit(kind, start, self.pos);
    }

    // -- SQL body collection --

    /// Check whether the last non-newline token expects a raw `{...}` body.
    fn last_non_newline_block_kind(&self) -> Option<BlockBodyKind> {
        let tok = self
            .tokens
            .iter()
            .rev()
            .find(|t| !matches!(t.kind, TokenKind::Newline))?;
        match tok.kind {
            TokenKind::Sql => Some(BlockBodyKind::Sql),
            TokenKind::Html => Some(BlockBodyKind::Html),
            TokenKind::Markdown => Some(BlockBodyKind::Markdown),
            _ => None,
        }
    }

    /// Collect raw block body text between braces for `sql/html/markdown`.
    fn scan_block_body(&mut self, brace_start: usize, kind: BlockBodyKind) {
        if matches!(kind, BlockBodyKind::Sql) {
            self.scan_sql_body(brace_start);
            return;
        }
        self.scan_template_body(brace_start, kind);
    }

    /// Collect raw SQL body text between braces.
    fn scan_sql_body(&mut self, brace_start: usize) {
        let body_start = self.pos; // first byte after `{`
        let mut depth: u32 = 1;

        while !self.is_at_end() {
            let ch = self.advance();
            match ch {
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        let body_end = self.pos - 1; // exclude closing `}`
                        let body_text = std::str::from_utf8(&self.source[body_start..body_end])
                            .expect("lexer source is guaranteed UTF-8")
                            .trim();
                        self.emit(
                            TokenKind::SqlBody(body_text.to_string()),
                            brace_start,
                            self.pos,
                        );
                        return;
                    }
                }
                // SQL single-quoted string: 'hello' with '' escape
                b'\'' => {
                    loop {
                        if self.is_at_end() {
                            self.error(
                                brace_start,
                                "unterminated SQL string literal inside sql block",
                            );
                            return;
                        }
                        let c = self.advance();
                        if c == b'\'' {
                            // '' is an escape, keep going; otherwise end of string
                            if self.peek() == Some(b'\'') {
                                self.advance(); // consume second quote
                            } else {
                                break;
                            }
                        }
                    }
                }
                // SQL double-quoted identifier: "column name"
                b'"' => {
                    loop {
                        if self.is_at_end() {
                            self.error(
                                brace_start,
                                "unterminated double-quoted identifier inside sql block",
                            );
                            return;
                        }
                        let c = self.advance();
                        if c == b'"' {
                            // "" is an escape in SQL; otherwise end of identifier
                            if self.peek() == Some(b'"') {
                                self.advance(); // consume second quote
                            } else {
                                break;
                            }
                        }
                    }
                }
                // SQL line comment: -- to end of line
                b'-' if self.peek() == Some(b'-') => {
                    self.advance(); // consume second '-'
                    while self.peek() != Some(b'\n') && !self.is_at_end() {
                        self.advance();
                    }
                }
                // SQL block comment: /* ... */
                b'/' if self.peek() == Some(b'*') => {
                    self.advance(); // consume '*'
                    let mut comment_depth: u32 = 1;
                    while comment_depth > 0 && !self.is_at_end() {
                        let c = self.advance();
                        if c == b'/' && self.peek() == Some(b'*') {
                            self.advance();
                            comment_depth += 1;
                        } else if c == b'*' && self.peek() == Some(b'/') {
                            self.advance();
                            comment_depth -= 1;
                        }
                    }
                    if comment_depth > 0 {
                        self.error(brace_start, "unterminated block comment inside sql block");
                        return;
                    }
                }
                _ => {}
            }
        }

        self.error(brace_start, "unterminated sql block");
    }

    /// Collect raw template body text between braces.
    ///
    /// Handles nested `${...}` interpolations and quoted strings inside
    /// interpolations so braces in strings don't terminate early.
    fn scan_template_body(&mut self, brace_start: usize, kind: BlockBodyKind) {
        let body_start = self.pos;
        let mut depth: u32 = 1;

        while !self.is_at_end() {
            let ch = self.advance();
            match ch {
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        let body_end = self.pos - 1; // exclude closing brace
                        let body_text = std::str::from_utf8(&self.source[body_start..body_end])
                            .expect("lexer source is guaranteed UTF-8")
                            .to_string();
                        match kind {
                            BlockBodyKind::Html => {
                                self.emit(TokenKind::HtmlBody(body_text), brace_start, self.pos)
                            }
                            BlockBodyKind::Markdown => {
                                self.emit(TokenKind::MarkdownBody(body_text), brace_start, self.pos)
                            }
                            BlockBodyKind::Sql => unreachable!("handled above"),
                        }
                        return;
                    }
                }
                b'"' | b'\'' => {
                    let quote = ch;
                    while !self.is_at_end() {
                        let c = self.advance();
                        if c == b'\\' && !self.is_at_end() {
                            self.advance(); // skip escaped char
                            continue;
                        }
                        if c == quote {
                            break;
                        }
                    }
                }
                _ => {}
            }
        }

        let label = match kind {
            BlockBodyKind::Html => "html",
            BlockBodyKind::Markdown => "markdown",
            BlockBodyKind::Sql => "sql",
        };
        self.error(brace_start, format!("unterminated {label} block"));
    }

    // -- Helpers --

    fn is_at_end(&self) -> bool {
        self.pos >= self.source.len()
    }

    fn peek(&self) -> Option<u8> {
        self.source.get(self.pos).copied()
    }

    fn peek_next(&self) -> Option<u8> {
        self.source.get(self.pos + 1).copied()
    }

    fn advance(&mut self) -> u8 {
        let ch = self.source[self.pos];
        self.pos += 1;
        ch
    }

    fn match_char(&mut self, expected: u8) -> bool {
        if self.peek() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// Collect horizontal whitespace (spaces/tabs) as trivia instead of discarding.
    fn collect_whitespace(&mut self) {
        let start = self.pos;
        while self.peek() == Some(b' ') || self.peek() == Some(b'\t') {
            self.pos += 1;
        }
        if self.pos > start {
            let text = std::str::from_utf8(&self.source[start..self.pos])
                .expect("whitespace is ASCII")
                .to_string();
            self.pending_trivia.push(Trivia {
                kind: TriviaKind::Whitespace,
                text,
                span: Span::new(self.file, start as u32, self.pos as u32),
            });
        }
    }

    fn last_is_newline(&self) -> bool {
        self.tokens
            .last()
            .is_some_and(|t| t.kind == TokenKind::Newline)
    }

    fn emit(&mut self, kind: TokenKind, start: usize, end: usize) {
        let leading = std::mem::take(&mut self.pending_trivia);
        self.tokens.push(Token {
            kind,
            span: Span::new(self.file, start as u32, end as u32),
            leading_trivia: leading,
            trailing_trivia: Vec::new(),
        });
    }

    /// Redistribute trivia so same-line content after a token becomes trailing trivia.
    ///
    /// Rule (Roslyn/Swift model): any trivia before the first Newline in the next
    /// token's leading trivia moves to the current token's trailing trivia, including
    /// that first Newline.
    ///
    /// Note: trivia collection is NOT active during opaque body scanning (sql/html/markdown).
    /// A `// comment` inside `sql { ... }` is SQL text, not Kea trivia.
    fn redistribute_trailing_trivia(&mut self) {
        for i in 0..self.tokens.len().saturating_sub(1) {
            let next_is_newline = self.tokens[i + 1].kind == TokenKind::Newline;
            let next_leading = &self.tokens[i + 1].leading_trivia;

            let split_at = if next_is_newline {
                // A Newline token represents a \n. ALL its leading trivia is
                // same-line content (whitespace/comments before the \n).
                next_leading.len()
            } else {
                // Move trivia before the first TriviaKind::Newline entry
                // (including that newline) to the previous token's trailing trivia.
                next_leading
                    .iter()
                    .position(|t| t.kind == TriviaKind::Newline)
                    .map(|j| j + 1)
                    .unwrap_or(0)
            };

            if split_at > 0 {
                let mut next_leading = std::mem::take(&mut self.tokens[i + 1].leading_trivia);
                let trailing: Vec<Trivia> = next_leading.drain(..split_at).collect();
                self.tokens[i + 1].leading_trivia = next_leading;
                self.tokens[i].trailing_trivia = trailing;
            }
        }
    }

    fn error(&mut self, pos: usize, message: impl Into<String>) {
        self.errors
            .push(
                Diagnostic::error(Category::Syntax, message).at(kea_diag::SourceLocation {
                    file_id: self.file.0,
                    start: pos as u32,
                    end: self.pos as u32,
                }),
            );
    }

    fn warning(&mut self, start: usize, end: usize, message: impl Into<String>) {
        self.errors
            .push(
                Diagnostic::warning(Category::Syntax, message).at(kea_diag::SourceLocation {
                    file_id: self.file.0,
                    start: start as u32,
                    end: end as u32,
                }),
            );
    }

    /// Check if position starts `{identifier}` pattern — likely missing `$` prefix.
    fn looks_like_interpolation(&self, brace_pos: usize) -> Option<String> {
        let after_brace = brace_pos + 1;
        if after_brace >= self.source.len() {
            return None;
        }
        // First char must be alphabetic or underscore
        let first = self.source[after_brace];
        if !first.is_ascii_alphabetic() && first != b'_' {
            return None;
        }
        // Scan identifier chars
        let mut end = after_brace + 1;
        while end < self.source.len()
            && (self.source[end].is_ascii_alphanumeric() || self.source[end] == b'_')
        {
            end += 1;
        }
        // Must be closed by }
        if end < self.source.len() && self.source[end] == b'}' {
            let name = std::str::from_utf8(&self.source[after_brace..end]).unwrap_or("?");
            Some(name.to_string())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_ok(source: &str) -> Vec<TokenKind> {
        lex(source, FileId(0))
            .unwrap()
            .0
            .into_iter()
            .map(|t| t.kind)
            .collect()
    }

    fn lex_kinds(source: &str) -> Vec<TokenKind> {
        // Strip Eof for cleaner assertions
        let mut kinds = lex_ok(source);
        if kinds.last() == Some(&TokenKind::Eof) {
            kinds.pop();
        }
        kinds
    }

    fn lex_layout_kinds(source: &str) -> Vec<TokenKind> {
        let mut kinds: Vec<_> = lex_layout(source, FileId(0))
            .unwrap()
            .0
            .into_iter()
            .map(|t| t.kind)
            .collect();
        if kinds.last() == Some(&TokenKind::Eof) {
            kinds.pop();
        }
        kinds
    }

    #[test]
    fn single_int() {
        assert_eq!(lex_kinds("42"), vec![TokenKind::Int(42)]);
    }

    #[test]
    fn single_float() {
        assert_eq!(lex_kinds("1.5"), vec![TokenKind::Float(1.5)]);
    }

    #[test]
    fn int_dot_no_digit_is_int_then_dot() {
        assert_eq!(
            lex_kinds("42.foo"),
            vec![
                TokenKind::Int(42),
                TokenKind::Dot,
                TokenKind::Ident("foo".into()),
            ]
        );
    }

    #[test]
    fn string_literal() {
        assert_eq!(
            lex_kinds(r#""hello""#),
            vec![TokenKind::String("hello".into())]
        );
    }

    #[test]
    fn string_escapes() {
        assert_eq!(
            lex_kinds(r#""a\nb\\c\"""#),
            vec![TokenKind::String("a\nb\\c\"".into())]
        );
    }

    #[test]
    fn string_interpolation_uses_dollar_brace() {
        assert_eq!(
            lex_kinds(r#""hello ${name}""#),
            vec![TokenKind::StringInterp(vec![
                crate::token::StringPart::Literal("hello ".into()),
                crate::token::StringPart::Expr("name".into()),
            ])]
        );
    }

    #[test]
    fn bare_brace_interpolation_warns() {
        // {name} without $ should produce a warning, not an error
        let (tokens, warnings) = lex(r#""hello {name}""#, FileId(0)).unwrap();
        // Should still lex successfully as a plain string
        assert_eq!(tokens[0].kind, TokenKind::String("hello {name}".into()));
        // But with a warning
        assert_eq!(warnings.len(), 1);
        assert!(
            warnings[0].message.contains("did you mean ${name}"),
            "got: {}",
            warnings[0].message
        );
    }

    #[test]
    fn bare_brace_non_identifier_no_warning() {
        // {1 + 2} shouldn't warn — doesn't look like a variable
        let (_, warnings) = lex(r#""result: {1 + 2}""#, FileId(0)).unwrap();
        assert!(warnings.is_empty());
    }

    #[test]
    fn keywords() {
        assert_eq!(
            lex_kinds(
                "let fn expr test property pub if when else case cond alias opaque deriving testing use forall"
            ),
            vec![
                TokenKind::Let,
                TokenKind::Fn,
                TokenKind::ExprKw,
                TokenKind::TestKw,
                TokenKind::Property,
                TokenKind::Pub,
                TokenKind::If,
                TokenKind::When,
                TokenKind::Else,
                TokenKind::Case,
                TokenKind::Cond,
                TokenKind::Alias,
                TokenKind::Opaque,
                TokenKind::Deriving,
                TokenKind::Testing,
                TokenKind::Use,
                TokenKind::Forall,
            ]
        );
    }

    #[test]
    fn reserved_words() {
        assert_eq!(
            lex_kinds(
                "sql html markdown spawn await stream yield yield_from assert assert_eq assert_ne assert_frame_equal assert_snapshot assert_ok assert_error",
            ),
            vec![
                TokenKind::Sql,
                TokenKind::Html,
                TokenKind::Markdown,
                TokenKind::Spawn,
                TokenKind::Await,
                TokenKind::Stream,
                TokenKind::Yield,
                TokenKind::YieldFrom,
                TokenKind::Assert,
                TokenKind::AssertEq,
                TokenKind::AssertNe,
                TokenKind::AssertFrameEqual,
                TokenKind::AssertSnapshot,
                TokenKind::AssertOk,
                TokenKind::AssertError,
            ]
        );
    }

    #[test]
    fn identifiers_and_upper() {
        assert_eq!(
            lex_kinds("foo Bar None True False"),
            vec![
                TokenKind::Ident("foo".into()),
                TokenKind::UpperIdent("Bar".into()),
                TokenKind::NoneKw,
                TokenKind::True,
                TokenKind::False,
            ]
        );
    }

    #[test]
    fn operators() {
        assert_eq!(
            lex_kinds("+ - * / % == != < <= > >= ?"),
            vec![
                TokenKind::Plus,
                TokenKind::Minus,
                TokenKind::Star,
                TokenKind::Slash,
                TokenKind::Percent,
                TokenKind::EqEq,
                TokenKind::BangEq,
                TokenKind::Lt,
                TokenKind::LtEq,
                TokenKind::Gt,
                TokenKind::GtEq,
                TokenKind::Question,
            ]
        );
    }

    #[test]
    fn word_boolean_operators() {
        assert_eq!(
            lex_kinds("and or not"),
            vec![TokenKind::And, TokenKind::Or, TokenKind::Not]
        );
    }

    #[test]
    fn nil_is_lex_error() {
        let err = lex("nil", FileId(0)).expect_err("nil should be rejected");
        assert!(err[0].message.contains("use `None`"), "got: {:?}", err[0]);
    }

    #[test]
    fn delimiters_and_punctuation() {
        assert_eq!(
            lex_kinds("( ) { } [ ] #[ #( #{ : , . | @ -> <- => .. ..= ="),
            vec![
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::LBrace,
                TokenKind::RBrace,
                TokenKind::LBracket,
                TokenKind::RBracket,
                TokenKind::HashBracket,
                TokenKind::HashParen,
                TokenKind::HashBrace,
                TokenKind::Colon,
                TokenKind::Comma,
                TokenKind::Dot,
                TokenKind::Pipe,
                TokenKind::At,
                TokenKind::Arrow,
                TokenKind::LeftArrow,
                TokenKind::FatArrow,
                TokenKind::DotDot,
                TokenKind::DotDotEq,
                TokenKind::Eq,
            ]
        );
    }

    #[test]
    fn comment_skipped() {
        assert_eq!(
            lex_kinds("42 -- this is ignored\n7"),
            vec![TokenKind::Int(42), TokenKind::Newline, TokenKind::Int(7)]
        );
    }

    #[test]
    fn doc_comment_tokenized() {
        assert_eq!(
            lex_kinds("--| Adds two numbers\nfn add(x, y) { x + y }"),
            vec![
                TokenKind::DocComment("Adds two numbers".into()),
                TokenKind::Newline,
                TokenKind::Fn,
                TokenKind::Ident("add".into()),
                TokenKind::LParen,
                TokenKind::Ident("x".into()),
                TokenKind::Comma,
                TokenKind::Ident("y".into()),
                TokenKind::RParen,
                TokenKind::LBrace,
                TokenKind::Ident("x".into()),
                TokenKind::Plus,
                TokenKind::Ident("y".into()),
                TokenKind::RBrace,
            ]
        );
    }

    #[test]
    fn legacy_slash_comment_still_skipped() {
        assert_eq!(
            lex_kinds("42 // this is ignored\n7"),
            vec![TokenKind::Int(42), TokenKind::Newline, TokenKind::Int(7)]
        );
    }

    #[test]
    fn newlines_collapsed() {
        assert_eq!(
            lex_kinds("1\n\n\n2"),
            vec![TokenKind::Int(1), TokenKind::Newline, TokenKind::Int(2)]
        );
    }

    #[test]
    fn no_leading_newline() {
        assert_eq!(lex_kinds("\n\n42"), vec![TokenKind::Int(42)]);
    }

    #[test]
    fn layout_emits_indent_and_dedent() {
        assert_eq!(
            lex_layout_kinds("let x = 1\n  x\nlet y = 2"),
            vec![
                TokenKind::Let,
                TokenKind::Ident("x".into()),
                TokenKind::Eq,
                TokenKind::Int(1),
                TokenKind::Newline,
                TokenKind::Indent,
                TokenKind::Ident("x".into()),
                TokenKind::Newline,
                TokenKind::Dedent,
                TokenKind::Let,
                TokenKind::Ident("y".into()),
                TokenKind::Eq,
                TokenKind::Int(2),
            ]
        );
    }

    #[test]
    fn layout_supports_nested_indent() {
        assert_eq!(
            lex_layout_kinds("a\n  b\n    c\nd"),
            vec![
                TokenKind::Ident("a".into()),
                TokenKind::Newline,
                TokenKind::Indent,
                TokenKind::Ident("b".into()),
                TokenKind::Newline,
                TokenKind::Indent,
                TokenKind::Ident("c".into()),
                TokenKind::Newline,
                TokenKind::Dedent,
                TokenKind::Dedent,
                TokenKind::Ident("d".into()),
            ]
        );
    }

    #[test]
    fn layout_dot_continuation_does_not_indent() {
        assert_eq!(
            lex_layout_kinds("xs\n  .map(f)\nys"),
            vec![
                TokenKind::Ident("xs".into()),
                TokenKind::Newline,
                TokenKind::Dot,
                TokenKind::Ident("map".into()),
                TokenKind::LParen,
                TokenKind::Ident("f".into()),
                TokenKind::RParen,
                TokenKind::Newline,
                TokenKind::Ident("ys".into()),
            ]
        );
    }

    #[test]
    fn layout_rejects_tabs_in_indentation() {
        let result = lex_layout("a\n\tb", FileId(0));
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("tabs are not allowed in indentation")),
            "missing tab indentation error: {errors:?}"
        );
    }

    #[test]
    fn layout_rejects_inconsistent_dedent() {
        let result = lex_layout("a\n  b\n c", FileId(0));
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("inconsistent indentation")),
            "missing inconsistent indentation error: {errors:?}"
        );
    }

    #[test]
    fn pipe_tokens() {
        assert_eq!(
            lex_kinds("| ||"),
            vec![TokenKind::Pipe, TokenKind::Pipe, TokenKind::Pipe]
        );
    }

    #[test]
    fn multitoken_expression() {
        assert_eq!(
            lex_kinds("let x = 42 + y"),
            vec![
                TokenKind::Let,
                TokenKind::Ident("x".into()),
                TokenKind::Eq,
                TokenKind::Int(42),
                TokenKind::Plus,
                TokenKind::Ident("y".into()),
            ]
        );
    }

    #[test]
    fn unterminated_string_error() {
        let result = lex("\"hello", FileId(0));
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(errors[0].message.contains("unterminated"));
    }

    #[test]
    fn lambda_tokens() {
        assert_eq!(
            lex_kinds("x -> x + 1"),
            vec![
                TokenKind::Ident("x".into()),
                TokenKind::Arrow,
                TokenKind::Ident("x".into()),
                TokenKind::Plus,
                TokenKind::Int(1),
            ]
        );
    }

    #[test]
    fn dollar_token() {
        assert_eq!(
            lex_kinds("$x $threshold"),
            vec![
                TokenKind::Dollar,
                TokenKind::Ident("x".into()),
                TokenKind::Dollar,
                TokenKind::Ident("threshold".into()),
            ]
        );
    }

    #[test]
    fn atom_tokens() {
        // :name produces Colon + Ident
        assert_eq!(
            lex_kinds(":age"),
            vec![TokenKind::Colon, TokenKind::Ident("age".into())]
        );
    }

    // -- SQL body collection tests --

    #[test]
    fn sql_body_basic() {
        assert_eq!(
            lex_kinds("sql { SELECT 1 }"),
            vec![TokenKind::Sql, TokenKind::SqlBody("SELECT 1".into())]
        );
    }

    #[test]
    fn sql_body_multiline() {
        let src = "sql {\n  SELECT *\n  FROM users\n  WHERE age > 28\n}";
        let kinds = lex_kinds(src);
        assert_eq!(kinds.len(), 2); // Sql, SqlBody
        assert_eq!(kinds[0], TokenKind::Sql);
        match &kinds[1] {
            TokenKind::SqlBody(body) => {
                assert!(body.contains("SELECT *"));
                assert!(body.contains("FROM users"));
                assert!(body.contains("WHERE age > 28"));
            }
            other => panic!("expected SqlBody, got {other:?}"),
        }
    }

    #[test]
    fn sql_body_single_quoted_string() {
        // Single quotes with '' escape should not end the SQL body
        assert_eq!(
            lex_kinds("sql { SELECT 'it''s' AS x }"),
            vec![
                TokenKind::Sql,
                TokenKind::SqlBody("SELECT 'it''s' AS x".into()),
            ]
        );
    }

    #[test]
    fn sql_body_line_comment() {
        // -- comment should not affect brace tracking
        let src = "sql { SELECT 1 -- } not a close\n}";
        let kinds = lex_kinds(src);
        assert_eq!(kinds[0], TokenKind::Sql);
        match &kinds[1] {
            TokenKind::SqlBody(body) => {
                assert!(body.contains("-- } not a close"));
            }
            other => panic!("expected SqlBody, got {other:?}"),
        }
    }

    #[test]
    fn sql_body_block_comment() {
        // /* } */ should not affect brace tracking
        let src = "sql { SELECT /* } */ 1 }";
        let kinds = lex_kinds(src);
        assert_eq!(kinds[0], TokenKind::Sql);
        match &kinds[1] {
            TokenKind::SqlBody(body) => {
                assert!(body.contains("/* } */"));
                assert!(body.contains("1"));
            }
            other => panic!("expected SqlBody, got {other:?}"),
        }
    }

    #[test]
    fn sql_body_captures_preserved() {
        // $var references are kept as-is in the raw SQL text
        assert_eq!(
            lex_kinds("sql { SELECT * FROM t WHERE x > $min }"),
            vec![
                TokenKind::Sql,
                TokenKind::SqlBody("SELECT * FROM t WHERE x > $min".into()),
            ]
        );
    }

    #[test]
    fn sql_body_unterminated_error() {
        let result = lex("sql { SELECT 1", FileId(0));
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(errors[0].message.contains("unterminated sql block"));
    }

    #[test]
    fn sql_body_tokens_after() {
        // Normal Kea tokens follow after sql block
        assert_eq!(
            lex_kinds("sql { SELECT 1 } + 1"),
            vec![
                TokenKind::Sql,
                TokenKind::SqlBody("SELECT 1".into()),
                TokenKind::Plus,
                TokenKind::Int(1),
            ]
        );
    }

    #[test]
    fn sql_body_nested_braces() {
        // Nested braces in SQL (e.g. CASE WHEN) should be tracked
        assert_eq!(
            lex_kinds("sql { SELECT CASE WHEN x > 0 THEN 'a' ELSE 'b' END }"),
            vec![
                TokenKind::Sql,
                TokenKind::SqlBody("SELECT CASE WHEN x > 0 THEN 'a' ELSE 'b' END".into()),
            ]
        );
    }

    #[test]
    fn sql_body_double_quoted_identifier() {
        // Double-quoted identifiers should be handled (even with } inside)
        assert_eq!(
            lex_kinds(r#"sql { SELECT "my col" FROM t }"#),
            vec![
                TokenKind::Sql,
                TokenKind::SqlBody(r#"SELECT "my col" FROM t"#.into()),
            ]
        );
    }

    #[test]
    fn sql_body_double_quoted_with_brace() {
        // A } inside a double-quoted identifier should not terminate the SQL body
        assert_eq!(
            lex_kinds(r#"sql { SELECT "col}name" FROM t }"#),
            vec![
                TokenKind::Sql,
                TokenKind::SqlBody(r#"SELECT "col}name" FROM t"#.into()),
            ]
        );
    }

    #[test]
    fn html_body_basic() {
        assert_eq!(
            lex_kinds("html { <h1>{:name}</h1> }"),
            vec![
                TokenKind::Html,
                TokenKind::HtmlBody(" <h1>{:name}</h1> ".into()),
            ]
        );
    }

    #[test]
    fn markdown_body_basic() {
        assert_eq!(
            lex_kinds("markdown { # {:title} }"),
            vec![
                TokenKind::Markdown,
                TokenKind::MarkdownBody(" # {:title} ".into()),
            ]
        );
    }

    // -- Trivia tests --

    fn lex_tokens(source: &str) -> Vec<Token> {
        lex(source, FileId(0)).unwrap().0
    }

    #[test]
    fn trivia_whitespace_preserved() {
        let tokens = lex_tokens("  42");
        // Int(42) should have leading whitespace trivia
        assert_eq!(tokens[0].leading_trivia.len(), 1);
        assert_eq!(tokens[0].leading_trivia[0].kind, TriviaKind::Whitespace);
        assert_eq!(tokens[0].leading_trivia[0].text, "  ");
    }

    #[test]
    fn trivia_line_comment_preserved() {
        let tokens = lex_tokens("42 // this is a comment\n7");
        // The comment should be trailing trivia on Int(42)
        assert!(
            tokens[0]
                .trailing_trivia
                .iter()
                .any(|t| t.kind == TriviaKind::LineComment),
            "expected line comment in trailing trivia, got: {:?}",
            tokens[0].trailing_trivia
        );
        let comment = tokens[0]
            .trailing_trivia
            .iter()
            .find(|t| t.kind == TriviaKind::LineComment)
            .unwrap();
        assert_eq!(comment.text, "// this is a comment");
    }

    #[test]
    fn trivia_trailing_comment() {
        // Comment after code on same line becomes trailing trivia
        let tokens = lex_tokens("let x = 42 // meaning of life\nlet y = 7");
        // Find Int(42) token
        let int_tok = tokens
            .iter()
            .find(|t| t.kind == TokenKind::Int(42))
            .unwrap();
        assert!(
            int_tok
                .trailing_trivia
                .iter()
                .any(|t| t.kind == TriviaKind::LineComment),
            "expected trailing comment on 42, got: {:?}",
            int_tok.trailing_trivia
        );
    }

    #[test]
    fn trivia_doc_comment_is_token_not_trivia() {
        // Doc comments should be tokens, not trivia entries
        let tokens = lex_tokens("--| Docs\nfn foo() { 1 }");
        assert_eq!(tokens[0].kind, TokenKind::DocComment("Docs".into()));
        // The doc comment text comes from the token span, not trivia
        assert!(tokens[0].leading_trivia.is_empty());
    }

    #[test]
    fn trivia_multiple_newlines_preserved() {
        // "1\n\n\n2": first \n is Newline token span, two extras in trivia
        let tokens = lex_tokens("1\n\n\n2");
        // Extra newlines end up as trailing trivia on Int(1)
        // (redistributed from the Newline token's leading trivia)
        let int1 = tokens.iter().find(|t| t.kind == TokenKind::Int(1)).unwrap();
        let newline_count = int1
            .trailing_trivia
            .iter()
            .filter(|t| t.kind == TriviaKind::Newline)
            .count();
        assert_eq!(
            newline_count, 2,
            "expected 2 extra newlines as trailing trivia on Int(1), got: {:?}",
            int1.trailing_trivia
        );
        // Round-trip still works
        let source = "1\n\n\n2";
        let reconstructed = crate::token::reconstruct_source(&tokens, source);
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn trivia_comment_between_tokens() {
        // Comment between two lines: lives in the Newline token's trailing trivia
        // (redistributed from Int(2)'s leading trivia because it precedes a TriviaKind::Newline)
        let tokens = lex_tokens("1\n// middle\n2");
        let newline_tok = tokens
            .iter()
            .find(|t| t.kind == TokenKind::Newline)
            .unwrap();
        assert!(
            newline_tok
                .trailing_trivia
                .iter()
                .any(|t| t.kind == TriviaKind::LineComment),
            "expected comment in trailing trivia of Newline, got: {:?}",
            newline_tok.trailing_trivia
        );
        // Round-trip still works
        let source = "1\n// middle\n2";
        let reconstructed = crate::token::reconstruct_source(&tokens, source);
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn trivia_end_of_file_comment() {
        let tokens = lex_tokens("42\n// trailing");
        let eof = tokens.iter().find(|t| t.kind == TokenKind::Eof).unwrap();
        assert!(
            eof.leading_trivia
                .iter()
                .any(|t| t.kind == TriviaKind::LineComment),
            "expected trailing comment on Eof, got: {:?}",
            eof.leading_trivia
        );
    }

    #[test]
    fn trivia_empty_source() {
        let tokens = lex_tokens("");
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].kind, TokenKind::Eof);
        assert!(tokens[0].leading_trivia.is_empty());
    }

    #[test]
    fn trivia_only_comments() {
        let tokens = lex_tokens("// just a comment\n// another");
        // Should just be Eof with comments as leading trivia
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].kind, TokenKind::Eof);
        let comments: Vec<_> = tokens[0]
            .leading_trivia
            .iter()
            .filter(|t| t.kind == TriviaKind::LineComment)
            .collect();
        assert_eq!(comments.len(), 2);
    }

    #[test]
    fn trivia_round_trip_simple() {
        let source = "let x = 42\nlet y = 7\n";
        let tokens = lex_tokens(source);
        let reconstructed = crate::token::reconstruct_source(&tokens, source);
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn trivia_round_trip_with_comments() {
        let source = "let x = 42 // meaning of life\nlet y = 7\n";
        let tokens = lex_tokens(source);
        let reconstructed = crate::token::reconstruct_source(&tokens, source);
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn trivia_round_trip_blank_lines() {
        let source = "1\n\n\n2\n";
        let tokens = lex_tokens(source);
        let reconstructed = crate::token::reconstruct_source(&tokens, source);
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn trivia_round_trip_leading_whitespace() {
        let source = "  42 + 7";
        let tokens = lex_tokens(source);
        let reconstructed = crate::token::reconstruct_source(&tokens, source);
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn trivia_round_trip_mixed() {
        let source = "fn fib(n) -> Int { case n { 0 -> 0, 1 -> 1, n -> fib(n - 1) + fib(n - 2) } } // recursive\n";
        let tokens = lex_tokens(source);
        let reconstructed = crate::token::reconstruct_source(&tokens, source);
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn trivia_round_trip_doc_comments() {
        let source = "--| Adds two numbers\nfn add(x, y) -> Int { x + y }\n";
        let tokens = lex_tokens(source);
        let reconstructed = crate::token::reconstruct_source(&tokens, source);
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn trivia_sql_body_not_collected() {
        // A // comment inside sql {} is SQL text, not Kea trivia
        let source = "sql { SELECT 1 // divisor\n}";
        let tokens = lex_tokens(source);
        // The comment text should be inside SqlBody, not as trivia
        let sql_body = tokens.iter().find_map(|t| {
            if let TokenKind::SqlBody(body) = &t.kind {
                Some(body.clone())
            } else {
                None
            }
        });
        assert!(sql_body.is_some(), "expected SqlBody token");
        // Verify no token has "// divisor" as trivia
        for tok in &tokens {
            for trivia in tok.leading_trivia.iter().chain(tok.trailing_trivia.iter()) {
                assert!(
                    !trivia.text.contains("divisor"),
                    "SQL comment leaked into Kea trivia: {:?}",
                    trivia
                );
            }
        }
    }

    #[test]
    fn trivia_round_trip_multiline_source() {
        let source = r#"struct Math
  fn inc(x: Int) -> Int
    x + 1

  fn label(x: Int) -> String
    "n=${x}"
"#;
        let (tokens, _warnings) = lex(source, FileId(0)).unwrap();
        let reconstructed = crate::token::reconstruct_source(&tokens, source);
        assert_eq!(reconstructed, source, "multiline source round-trip failed");
    }
}

//! Recursive descent parser with Pratt-style precedence climbing for Kea.

use kea_ast::*;
use kea_diag::{Category, Diagnostic, SourceLocation};

use crate::token::{Token, TokenKind};

/// Parse an expression from a token stream.
pub fn parse_expr(tokens: Vec<Token>, file: FileId) -> Result<Expr, Vec<Diagnostic>> {
    let mut parser = Parser::new(tokens, file);
    let expr = parser.expression();
    parser.skip_newlines();
    if !parser.at_eof() {
        parser.error_at_current("unexpected token after expression");
    }
    if parser.errors.is_empty() {
        match expr {
            Some(e) => Ok(e),
            None => Err(vec![Diagnostic::error(
                Category::Syntax,
                "expected expression",
            )]),
        }
    } else {
        Err(parser.errors)
    }
}

/// Parse a standalone type annotation from a token stream.
///
/// Used by the extension system to parse type signatures from metadata strings.
pub fn parse_type(
    tokens: Vec<Token>,
    file: FileId,
) -> Result<Spanned<TypeAnnotation>, Vec<Diagnostic>> {
    let mut parser = Parser::new(tokens, file);
    let ann = parser.type_annotation();
    parser.skip_newlines();
    if !parser.at_eof() {
        parser.error_at_current("unexpected token after type annotation");
    }
    if parser.errors.is_empty() {
        match ann {
            Some(a) => Ok(a),
            None => Err(vec![Diagnostic::error(
                Category::Syntax,
                "expected type annotation",
            )]),
        }
    } else {
        Err(parser.errors)
    }
}

/// Parse a module (sequence of function declarations) from tokens.
pub fn parse_module(tokens: Vec<Token>, file: FileId) -> Result<Module, Vec<Diagnostic>> {
    let mut parser = Parser::new(tokens, file);
    let module = parser.module();
    if parser.errors.is_empty() {
        Ok(module)
    } else {
        Err(parser.errors)
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    file: FileId,
    errors: Vec<Diagnostic>,
    /// When true, `UpperIdent {` is NOT parsed as a named record literal.
    /// Used in case scrutinee position (same as Rust's struct-literal restriction).
    restrict_struct_literals: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockDelimiter {
    Indent,
}

impl Parser {
    fn new(tokens: Vec<Token>, file: FileId) -> Self {
        Self {
            tokens,
            pos: 0,
            file,
            errors: Vec::new(),
            restrict_struct_literals: false,
        }
    }

    // -- Module-level parsing --

    fn module(&mut self) -> Module {
        let start = self.current_span();
        let mut declarations: Vec<Decl> = Vec::new();
        self.skip_newlines();
        while !self.at_eof() {
            if let Some(decl) = self.declaration() {
                declarations.push(decl);
            }
            self.skip_newlines();
        }
        let end = self.current_span();
        Module {
            declarations,
            span: start.merge(end),
        }
    }

    fn declaration(&mut self) -> Option<Decl> {
        let doc = self.consume_doc_comment_block();
        let start = self.current_span();
        self.parse_legacy_derive_attributes();
        let annotations = self.parse_annotations()?;

        // import Kea.Core
        // import Kea.Core.{read_csv, write_csv}
        // import Kea.Core as C
        if self.check(&TokenKind::Import) {
            if doc.is_some() {
                self.error_at_current(
                    "doc comments can only be attached to fn, type, alias, opaque, record, or trait declarations",
                );
            }
            if !annotations.is_empty() {
                self.error_at_current("annotations are not allowed on import declarations");
            }
            self.advance(); // consume 'import'
            return self.import_decl(start);
        }

        // alias Name = Type
        // pub alias Name = Type
        if self.check(&TokenKind::Alias)
            || (self.check(&TokenKind::Pub) && self.peek_is(|k| matches!(k, TokenKind::Alias)))
        {
            let public = self.match_token(&TokenKind::Pub);
            if !annotations.is_empty() {
                self.error_at_current("annotations are not supported on alias declarations");
            }
            self.advance(); // consume 'alias'
            return self.alias_decl(public, start, doc);
        }

        // opaque Name = Type
        // pub opaque Name = Type
        if self.check(&TokenKind::Opaque)
            || (self.check(&TokenKind::Pub) && self.peek_is(|k| matches!(k, TokenKind::Opaque)))
        {
            let public = self.match_token(&TokenKind::Pub);
            if !annotations.is_empty() {
                self.error_at_current("annotations are not supported on opaque declarations");
            }
            self.advance(); // consume 'opaque'
            return self.opaque_type_def(public, start, doc);
        }

        // type Name = Variant1 | Variant2(Type) | ...
        // pub type Name = Variant1 | Variant2(Type) | ...
        if self.check(&TokenKind::TypeKw)
            || (self.check(&TokenKind::Pub) && self.peek_is(|k| matches!(k, TokenKind::TypeKw)))
        {
            let public = self.match_token(&TokenKind::Pub);
            self.advance(); // consume 'type'
            return self.type_def(public, start, doc, annotations);
        }

        // record Name { field: Type, ... }
        // pub record Name { field: Type, ... }
        if self.check(&TokenKind::Record)
            || (self.check(&TokenKind::Pub) && self.peek_is(|k| matches!(k, TokenKind::Record)))
        {
            let public = self.match_token(&TokenKind::Pub);
            self.advance(); // consume 'record'
            return self.record_def(public, start, doc, annotations);
        }

        // trait Name { methods }
        // pub trait Name { methods }
        if self.check(&TokenKind::Trait)
            || (self.check(&TokenKind::Pub) && self.peek_is(|k| matches!(k, TokenKind::Trait)))
        {
            let public = self.match_token(&TokenKind::Pub);
            if !annotations.is_empty() {
                self.error_at_current("annotations are not supported on trait declarations");
            }
            self.advance(); // consume 'trait'
            return self.trait_def(public, start, doc);
        }

        // impl Trait for Type { methods }
        // impl Type { methods }
        if self.check(&TokenKind::Impl) {
            if doc.is_some() {
                self.error_at_current(
                    "doc comments can only be attached to fn, type, record, or trait declarations",
                );
            }
            if !annotations.is_empty() {
                self.error_at_current("annotations are not allowed on impl blocks");
            }
            self.advance(); // consume 'impl'
            return self.impl_block(start);
        }

        // expr name(params) -> Type { body }
        // pub expr name(params) -> Type { body }
        if self.check(&TokenKind::ExprKw)
            || (self.check(&TokenKind::Pub) && self.peek_is(|k| matches!(k, TokenKind::ExprKw)))
        {
            let public = self.match_token(&TokenKind::Pub);
            self.advance(); // consume 'expr'
            return self.expr_fn_decl(public, start, doc, annotations);
        }

        // test "name" { body }
        // test property "name" { body }
        if self.check(&TokenKind::TestKw) {
            if doc.is_some() {
                self.error_at_current("doc comments cannot be attached to test declarations");
            }
            if !annotations.is_empty() {
                self.error_at_current("annotations are not allowed on test declarations");
            }
            self.advance(); // consume 'test'
            return self.test_decl(start);
        }

        if self.check(&TokenKind::Pub) || self.check(&TokenKind::Fn) {
            let public = self.match_token(&TokenKind::Pub);
            if self.match_token(&TokenKind::Fn) {
                return self.fn_decl(public, start, doc, annotations);
            } else {
                self.error_at_current(
                    "expected 'fn', 'expr', 'type', 'alias', 'opaque', 'record', or 'trait' after 'pub'",
                );
                return None;
            }
        }
        if doc.is_some() {
            self.error_at_current(
                "doc comments can only be attached to fn, type, alias, opaque, record, or trait declarations",
            );
        }
        self.error_at_current(
            "expected declaration (fn, expr, test, pub fn, type, alias, opaque, record, trait, impl, or import)",
        );
        // Skip to next newline to recover
        while !self.at_eof() && !self.check_newline() {
            self.advance();
        }
        None
    }

    fn parse_annotations(&mut self) -> Option<Vec<Annotation>> {
        let mut annotations = Vec::new();
        self.skip_newlines();
        while self.check(&TokenKind::At) {
            annotations.push(self.parse_annotation()?);
            self.skip_newlines();
        }
        Some(annotations)
    }

    fn parse_annotation(&mut self) -> Option<Annotation> {
        let at = self.expect(&TokenKind::At, "expected '@' to start annotation")?;
        let name = match self.peek_kind() {
            Some(TokenKind::Ident(_)) => self.expect_ident("expected annotation name after '@'")?,
            Some(TokenKind::UpperIdent(_)) => {
                self.expect_upper_ident("expected annotation name after '@'")?
            }
            _ => {
                self.error_at_current("expected annotation name after '@'");
                return None;
            }
        };

        let mut args = Vec::new();
        if self.match_token(&TokenKind::LParen) {
            self.skip_newlines();
            if !self.check(&TokenKind::RParen) {
                loop {
                    self.skip_newlines();
                    let label = if matches!(
                        (self.peek_kind(), self.peek_at(1).map(|tok| &tok.kind)),
                        (Some(TokenKind::Ident(_)), Some(TokenKind::Colon))
                    ) {
                        let label = self.expect_ident("expected annotation argument label")?;
                        self.expect(
                            &TokenKind::Colon,
                            "expected ':' after annotation argument label",
                        )?;
                        Some(label)
                    } else {
                        None
                    };
                    self.skip_newlines();
                    let value = self.expression()?;
                    args.push(Argument { label, value });
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                    self.skip_newlines();
                    if self.check(&TokenKind::RParen) {
                        break;
                    }
                }
            }
            self.expect(
                &TokenKind::RParen,
                "expected ')' to close annotation arguments",
            )?;
        }

        let end = self.current_span();
        Some(Annotation {
            name,
            args,
            span: at.span.merge(end),
        })
    }

    /// Parse an import declaration after the `import` keyword has been consumed.
    ///
    /// Syntax:
    /// - `import Kea.Core`           → ImportItems::Module (qualified access only)
    /// - `import Kea.Core.{a, b}`    → ImportItems::Named(["a", "b"]) (bare access)
    /// - `import Kea.Core as C`      → ImportItems::Module with alias
    fn import_decl(&mut self, start: Span) -> Option<Decl> {
        // Parse dotted module path: UpperIdent(.UpperIdent)*
        let first = self.expect_upper_ident("expected module name after 'import'")?;
        let mut path = first.node.clone();
        let mut end = first.span;

        while self.check(&TokenKind::Dot) {
            // Peek ahead: could be `.UpperIdent`, `.{`, or `.*`
            let after_dot = self.tokens.get(self.pos + 1).map(|t| &t.kind);
            match after_dot {
                Some(TokenKind::UpperIdent(_)) => {
                    self.advance(); // consume '.'
                    let seg = self.expect_upper_ident("expected module segment")?;
                    path.push('.');
                    path.push_str(&seg.node);
                    end = seg.span;
                }
                Some(TokenKind::LBrace) | Some(TokenKind::Star) => {
                    // Stop path parsing; the `.{` or `.*` belongs to the items part.
                    break;
                }
                _ => {
                    break;
                }
            }
        }

        // Parse items: `.{a, b}` or nothing (whole module).
        // Glob imports (`.*`) are not supported.
        let items = if self.check(&TokenKind::Dot) {
            self.advance(); // consume '.'
            if self.check(&TokenKind::Star) {
                self.error_at_current(
                    "glob imports are not supported; use `import Module` for qualified access or `import Module.{name}` for specific names",
                );
                return None;
            } else if self.match_token(&TokenKind::LBrace) {
                let mut names = Vec::new();
                self.skip_newlines();
                if !self.check(&TokenKind::RBrace) {
                    loop {
                        self.skip_newlines();
                        let name = self.expect_ident("expected function name in import")?;
                        names.push(name);
                        self.skip_newlines();
                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                        self.skip_newlines();
                        if self.check(&TokenKind::RBrace) {
                            break; // trailing comma
                        }
                    }
                }
                end = self.current_span();
                self.expect(&TokenKind::RBrace, "expected '}' to close import list")?;
                ImportItems::Named(names)
            } else {
                self.error_at_current("expected '{' after '.' in import");
                return None;
            }
        } else {
            ImportItems::Module
        };

        // Parse optional alias: `as Alias`
        let alias = if self.check_ident("as") {
            self.advance(); // consume 'as'
            let alias_name = self.expect_upper_ident("expected module alias after 'as'")?;
            end = alias_name.span;
            Some(alias_name)
        } else {
            None
        };

        let module_span = start.merge(end);
        Some(Spanned::new(
            DeclKind::Import(ImportDecl {
                module: Spanned::new(path, module_span),
                items,
                alias,
            }),
            start.merge(end),
        ))
    }

    fn alias_decl(&mut self, public: bool, start: Span, doc: Option<String>) -> Option<Decl> {
        let name = self.expect_upper_ident("expected alias name")?;
        self.skip_newlines();

        let mut params = Vec::new();
        if self.match_token(&TokenKind::LParen) {
            loop {
                let p = self.expect_type_param_name("expected type parameter")?;
                params.push(p.node);
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(&TokenKind::RParen, "expected ')' after type parameters")?;
            self.skip_newlines();
        }

        self.expect(&TokenKind::Eq, "expected '=' after alias name")?;
        self.skip_newlines();
        let target = self.type_annotation()?;
        let end = target.span;

        Some(Spanned::new(
            DeclKind::AliasDecl(AliasDecl {
                public,
                name,
                doc,
                params,
                target,
            }),
            start.merge(end),
        ))
    }

    fn opaque_type_def(&mut self, public: bool, start: Span, doc: Option<String>) -> Option<Decl> {
        let name = self.expect_upper_ident("expected opaque type name")?;
        self.skip_newlines();

        let mut params = Vec::new();
        if self.match_token(&TokenKind::LParen) {
            loop {
                let p = self.expect_type_param_name("expected type parameter")?;
                params.push(p.node);
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(&TokenKind::RParen, "expected ')' after type parameters")?;
            self.skip_newlines();
        }

        self.expect(&TokenKind::Eq, "expected '=' after opaque type name")?;
        self.skip_newlines();
        let target = self.type_annotation()?;

        let mut derives = Vec::new();
        if self.check(&TokenKind::Deriving) {
            let mut post_derives = self.parse_deriving_clause()?;
            derives.append(&mut post_derives);
        }

        let end = self.current_span();
        Some(Spanned::new(
            DeclKind::OpaqueTypeDef(OpaqueTypeDef {
                public,
                name,
                doc,
                params,
                target,
                derives,
            }),
            start.merge(end),
        ))
    }

    fn record_def(
        &mut self,
        public: bool,
        start: Span,
        doc: Option<String>,
        annotations: Vec<Annotation>,
    ) -> Option<Decl> {
        let name = self.expect_upper_ident("expected record name")?;
        self.skip_newlines();

        // Optional type parameters: record ApiResponse(t) { ... }
        let mut params = Vec::new();
        if self.match_token(&TokenKind::LParen) {
            loop {
                let p = self.expect_ident("expected type parameter")?;
                params.push(p.node);
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(&TokenKind::RParen, "expected ')' after type parameters")?;
            self.skip_newlines();
        }

        if self.check(&TokenKind::Deriving) {
            self.error_at_current(
                "`deriving` must appear after the record body (`record Name { ... } deriving Eq`)",
            );
        }
        let mut derives = Vec::new();
        let delimiter = self.expect_block_start("expected record body block after record name")?;
        let mut fields = Vec::new();
        let mut field_annotations = Vec::new();
        self.skip_newlines();
        if !self.at_block_end(delimiter) {
            loop {
                self.skip_newlines();
                if self.at_block_end(delimiter) {
                    break;
                }
                let anns = self.parse_annotations()?;
                self.skip_newlines();
                let field_name = self.expect_ident("expected field name in record definition")?;
                self.expect(&TokenKind::Colon, "expected ':' after field name")?;
                let field_type = self.type_annotation()?;
                fields.push((field_name, field_type.node));
                field_annotations.push(anns);
                self.skip_newlines();
                let _ = self.match_token(&TokenKind::Comma);
            }
        }
        self.skip_newlines();
        self.expect_block_end(delimiter, "expected end of record definition")?;
        if self.check(&TokenKind::Deriving) {
            let mut post_derives = self.parse_deriving_clause()?;
            derives.append(&mut post_derives);
        }
        let end = self.current_span();
        Some(Spanned::new(
            DeclKind::RecordDef(RecordDef {
                public,
                name,
                doc,
                annotations,
                params,
                fields,
                field_annotations,
                derives,
            }),
            start.merge(end),
        ))
    }

    /// Parse a sum type definition: `type Name = V1 | V2(T) | V3(T1, T2)`
    fn type_def(
        &mut self,
        public: bool,
        start: Span,
        doc: Option<String>,
        annotations: Vec<Annotation>,
    ) -> Option<Decl> {
        let name = self.expect_upper_ident("expected type name")?;
        self.skip_newlines();

        // Optional type parameters: type Option(T) = ...
        // Type params are uppercase idents (T, E, K, V, etc.)
        let mut params = Vec::new();
        if self.match_token(&TokenKind::LParen) {
            loop {
                let p = self.expect_upper_ident("expected type parameter")?;
                params.push(p.node);
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(&TokenKind::RParen, "expected ')' after type parameters")?;
            self.skip_newlines();
        }

        if self.check(&TokenKind::Deriving) {
            self.error_at_current(
                "`deriving` must appear after variants (`type Name = A | B deriving Eq`)",
            );
        }
        let mut derives = Vec::new();

        self.expect(&TokenKind::Eq, "expected '=' after type name")?;
        self.skip_newlines();
        let _ = self.match_token(&TokenKind::Indent);
        self.skip_newlines();

        // Optional leading pipe: type Color = | Red | Green | Blue
        self.match_token(&TokenKind::Pipe);
        self.skip_newlines();

        // Parse variants separated by |
        let mut variants = Vec::new();
        loop {
            self.skip_newlines();
            let variant_annotations = self.parse_annotations()?;
            self.skip_newlines();
            let variant_name = self.expect_upper_ident("expected variant name")?;
            let mut fields = Vec::new();
            if self.match_token(&TokenKind::LParen) {
                self.skip_newlines();
                if !self.check(&TokenKind::RParen) {
                    // Named and positional variant fields cannot be mixed.
                    let mut named_fields = None;
                    loop {
                        self.skip_newlines();
                        let field_annotations = self.parse_annotations()?;
                        self.skip_newlines();
                        let is_named = matches!(
                            (self.peek_kind(), self.peek_at(1).map(|tok| &tok.kind)),
                            (Some(TokenKind::Ident(_)), Some(TokenKind::Colon))
                        );
                        match named_fields {
                            Some(expected) if expected != is_named => {
                                self.error_at_current(
                                    "cannot mix named and positional fields in one variant",
                                );
                            }
                            None => named_fields = Some(is_named),
                            _ => {}
                        }
                        if is_named {
                            let field_name = self.expect_ident("expected variant field name")?;
                            self.skip_newlines();
                            self.expect(
                                &TokenKind::Colon,
                                "expected ':' after variant field name",
                            )?;
                            self.skip_newlines();
                            let field_ty = self.type_annotation()?;
                            let span = field_name.span.merge(field_ty.span);
                            fields.push(VariantField {
                                annotations: field_annotations,
                                name: Some(field_name),
                                ty: field_ty,
                                span,
                            });
                        } else {
                            if !field_annotations.is_empty() {
                                self.error_at_current(
                                    "annotations on variant fields require named fields",
                                );
                            }
                            let field_ty = self.type_annotation()?;
                            fields.push(VariantField {
                                annotations: Vec::new(),
                                name: None,
                                span: field_ty.span,
                                ty: field_ty,
                            });
                        }
                        self.skip_newlines();
                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                    }
                }
                self.expect(&TokenKind::RParen, "expected ')' after variant fields")?;
            }
            self.skip_newlines();
            let mut where_clause = Vec::new();
            if self.match_token(&TokenKind::Where) {
                loop {
                    self.skip_newlines();
                    let type_var =
                        self.expect_upper_ident("expected type variable in variant where clause")?;
                    self.skip_newlines();
                    self.expect(
                        &TokenKind::Eq,
                        "expected '=' in variant where-clause equality",
                    )?;
                    self.skip_newlines();
                    let ty = self.type_annotation()?;
                    where_clause.push(VariantWhereItem { type_var, ty });
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                }
            }
            variants.push(TypeVariant {
                annotations: variant_annotations,
                name: variant_name,
                fields,
                where_clause,
            });
            self.skip_newlines();
            let _ = self.match_token(&TokenKind::Indent);
            self.skip_newlines();
            if self.match_token(&TokenKind::Dedent) {
                break;
            }
            if !self.match_token(&TokenKind::Pipe) {
                break;
            }
        }

        // Canonical form: `type Name = V1 | V2 deriving Eq, Display`.
        if self.check(&TokenKind::Deriving) {
            let mut post_derives = self.parse_deriving_clause()?;
            derives.append(&mut post_derives);
        }

        let end = self.current_span();
        Some(Spanned::new(
            DeclKind::TypeDef(TypeDef {
                public,
                name,
                doc,
                annotations,
                params,
                variants,
                derives,
            }),
            start.merge(end),
        ))
    }

    /// Parse `deriving` followed by a bare trait list.
    fn parse_deriving_clause(&mut self) -> Option<Vec<Spanned<String>>> {
        self.expect(&TokenKind::Deriving, "expected 'deriving'")?;
        self.skip_newlines();
        if self.check(&TokenKind::LParen) {
            self.error_at_current(
                "parenthesized deriving lists are not supported; use `deriving Eq, Display`",
            );
            return None;
        }
        self.parse_deriving_list()
    }

    /// Parse `Eq, Display, Serialize` after a `deriving` keyword.
    fn parse_deriving_list(&mut self) -> Option<Vec<Spanned<String>>> {
        let mut derives = Vec::new();
        let first = self.expect_upper_ident("expected trait name after 'deriving'")?;
        derives.push(first);
        while self.match_token(&TokenKind::Comma) {
            self.skip_newlines();
            let trait_name = self.expect_upper_ident("expected trait name after ','")?;
            derives.push(trait_name);
        }
        Some(derives)
    }

    fn parse_legacy_derive_attributes(&mut self) {
        self.skip_newlines();
        while self.check(&TokenKind::HashBracket) {
            self.advance(); // #[
            let attr_name = match self.peek_kind() {
                Some(TokenKind::Ident(name)) => {
                    let name = name.clone();
                    self.advance();
                    name
                }
                _ => {
                    self.error_at_current("expected attribute name after `#[`");
                    return;
                }
            };

            if !self.match_token(&TokenKind::LParen) {
                self.error_at_current("expected '(' after attribute name");
                return;
            }

            self.skip_newlines();
            while !self.check(&TokenKind::RParen) && !self.at_eof() {
                self.advance();
                self.skip_newlines();
                if !self.match_token(&TokenKind::Comma) && !self.check(&TokenKind::RParen) {
                    self.advance();
                }
                self.skip_newlines();
            }
            if !self.match_token(&TokenKind::RParen) {
                self.error_at_current("expected ')' to close attribute");
                return;
            }
            if !self.match_token(&TokenKind::RBracket) {
                self.error_at_current("expected ']' to close attribute");
                return;
            }
            if attr_name == "derive" {
                self.error_at_current(
                    "legacy `#[derive(...)]` is not supported; use postfix `deriving Eq, Display`",
                );
            } else {
                let msg = format!("attributes are not supported (`#[{attr_name}(...)]`)");
                self.error_at_current(&msg);
            }
            self.skip_newlines();
        }
    }

    fn trait_def(&mut self, public: bool, start: Span, doc: Option<String>) -> Option<Decl> {
        let name = self.expect_upper_ident("expected trait name")?;
        let mut type_params = Vec::new();
        if self.match_token(&TokenKind::LParen) {
            self.skip_newlines();
            if !self.check(&TokenKind::RParen) {
                loop {
                    self.skip_newlines();
                    let param_name =
                        self.expect_type_param_name("expected trait type parameter name")?;
                    self.expect(
                        &TokenKind::Colon,
                        "expected ':' after trait type parameter name",
                    )?;
                    self.skip_newlines();
                    let kind = self.kind_annotation()?;
                    type_params.push(TraitTypeParam {
                        name: param_name,
                        kind,
                    });
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                }
            }
            self.expect(
                &TokenKind::RParen,
                "expected ')' after trait type parameters",
            )?;
        }
        let mut supertraits = Vec::new();
        if self.match_token(&TokenKind::Colon) {
            self.skip_newlines();
            loop {
                let supertrait = self
                    .expect_upper_ident("expected supertrait name after ':' in trait definition")?;
                supertraits.push(supertrait);
                self.skip_newlines();
                if !self.match_token(&TokenKind::Plus) {
                    break;
                }
                self.skip_newlines();
            }
        }
        let fundeps = self.parse_trait_fundeps()?;
        let delimiter = self.expect_block_start("expected trait body block after trait name")?;
        let mut associated_types = Vec::new();
        let mut methods = Vec::new();
        self.skip_newlines();
        while !self.at_block_end(delimiter) && !self.at_eof() {
            // Associated type declaration:
            // `type Name`
            // `type Name where Name: Constraint`
            // `type Name = SomeType`
            if self.check(&TokenKind::TypeKw) {
                self.advance(); // consume 'type'
                self.skip_newlines();
                let assoc_name =
                    self.expect_upper_ident("expected associated type name after 'type'")?;
                let mut constraints = Vec::new();
                let mut default = None;
                self.skip_newlines();
                if self.match_token(&TokenKind::Where) {
                    // Parse constraints: `where Name: Trait, Name: Trait2`
                    loop {
                        self.skip_newlines();
                        let _constraint_var = self.expect_upper_ident(
                            "expected type name in associated type constraint",
                        )?;
                        self.expect(
                            &TokenKind::Colon,
                            "expected ':' after type name in constraint",
                        )?;
                        let constraint_trait =
                            self.expect_upper_ident("expected trait name in constraint")?;
                        constraints.push(constraint_trait);
                        self.skip_newlines();
                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                    }
                }
                self.skip_newlines();
                if self.match_token(&TokenKind::Eq) {
                    self.skip_newlines();
                    default = Some(self.type_annotation()?);
                }
                associated_types.push(AssociatedTypeDecl {
                    name: assoc_name,
                    constraints,
                    default,
                });
            } else {
                methods.push(self.trait_method()?);
            }
            self.skip_newlines();
        }
        let end = self.current_span();
        self.expect_block_end(delimiter, "expected end of trait definition")?;
        Some(Spanned::new(
            DeclKind::TraitDef(TraitDef {
                public,
                name,
                doc,
                type_params,
                supertraits,
                fundeps,
                associated_types,
                methods,
            }),
            start.merge(end),
        ))
    }

    fn parse_trait_fundep_side(&mut self) -> Option<Vec<Spanned<String>>> {
        if self.match_token(&TokenKind::LParen) {
            self.skip_newlines();
            let mut names = Vec::new();
            if !self.check(&TokenKind::RParen) {
                loop {
                    self.skip_newlines();
                    names.push(self.expect_type_param_name(
                        "expected type parameter name in functional dependency",
                    )?);
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                }
            }
            self.expect(
                &TokenKind::RParen,
                "expected ')' in functional dependency parameter list",
            )?;
            return Some(names);
        }
        Some(vec![self.expect_type_param_name(
            "expected type parameter name in functional dependency",
        )?])
    }

    fn parse_trait_fundeps(&mut self) -> Option<Vec<FunctionalDependencyDecl>> {
        if !self.match_token(&TokenKind::Pipe) {
            return Some(Vec::new());
        }

        let mut fundeps = Vec::new();
        loop {
            self.skip_newlines();
            let from = self.parse_trait_fundep_side()?;
            self.skip_newlines();
            self.expect(
                &TokenKind::Arrow,
                "expected '->' in trait functional dependency",
            )?;
            self.skip_newlines();
            let to = self.parse_trait_fundep_side()?;
            fundeps.push(FunctionalDependencyDecl { from, to });
            self.skip_newlines();
            if !self.match_token(&TokenKind::Comma) {
                break;
            }
        }
        Some(fundeps)
    }

    fn kind_annotation(&mut self) -> Option<KindAnnotation> {
        let kind = self.kind_atom()?;
        self.skip_newlines();
        if self.check(&TokenKind::Arrow) {
            self.error_at_current(
                "higher-kinded kind arrows are not supported in Kea v0; use `*`",
            );
            return None;
        }
        Some(kind)
    }

    fn kind_atom(&mut self) -> Option<KindAnnotation> {
        if self.match_token(&TokenKind::Star) {
            return Some(KindAnnotation::Star);
        }
        if self.match_token(&TokenKind::LParen) {
            self.skip_newlines();
            let inner = self.kind_annotation()?;
            self.skip_newlines();
            self.expect(&TokenKind::RParen, "expected ')' in kind annotation")?;
            return Some(inner);
        }
        self.error_at_current("expected kind annotation (`*` or parenthesized kind)");
        None
    }

    fn trait_method(&mut self) -> Option<TraitMethod> {
        let method_start = self.current_span();
        let doc = self.consume_doc_comment_block();
        self.expect(&TokenKind::Fn, "expected 'fn' in trait method")?;
        let name = self.expect_ident("expected method name")?;
        self.expect(&TokenKind::LParen, "expected '(' after method name")?;

        let params = self.param_list()?;
        self.expect(&TokenKind::RParen, "expected ')' after method parameters")?;

        let effect_annotation = self.parse_required_return_arrow_effect(
            "trait methods require a return type: add `-> Type` or `-[effect]> Type` after the parameter list",
        )?;
        let return_annotation = Some(self.type_annotation()?);
        let where_clause = self.where_clause()?;

        self.skip_newlines();

        // Optional default body
        let default_body = if self.check(&TokenKind::Indent) {
            Some(self.parse_block_expr("expected trait method default body block")?)
        } else {
            None
        };

        let method_end = self.current_span();
        Some(TraitMethod {
            name,
            params,
            return_annotation,
            effect_annotation,
            where_clause,
            default_body,
            doc,
            span: method_start.merge(method_end),
        })
    }

    fn impl_block(&mut self, start: Span) -> Option<Decl> {
        // impl Trait for Type { methods }
        let trait_name = self.expect_upper_ident("expected trait name after 'impl'")?;
        self.skip_newlines();

        if !matches!(self.peek_kind(), Some(TokenKind::Ident(s)) if s == "for") {
            self.error_at_current(
                "expected `for` in impl header (use `impl Trait for Type { ... }`)",
            );
            return None;
        }
        self.advance(); // consume 'for'
        self.skip_newlines();
        let type_name = self.expect_upper_ident("expected type name after 'for'")?;
        self.skip_newlines();

        // Optional type parameters in impl header:
        // impl Show for List(t) where t: Show { ... }
        let type_params = if self.match_token(&TokenKind::LParen) {
            let mut params = Vec::new();
            loop {
                self.skip_newlines();
                let param = self.expect_ident("expected type parameter in impl header")?;
                params.push(param);
                self.skip_newlines();
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(
                &TokenKind::RParen,
                "expected ')' after impl type parameters",
            )?;
            params
        } else {
            Vec::new()
        };

        // Parse optional where clause: `where Source = String, schema: Deserialize`
        self.skip_newlines();
        let mut impl_where_clause: Vec<WhereItem> = Vec::new();
        if self.check(&TokenKind::Where) {
            self.advance(); // consume 'where'
            loop {
                self.skip_newlines();
                // Disambiguate: UpperIdent '=' is TypeAssignment, lowercase ':' is TraitBound
                if let Some(TokenKind::UpperIdent(_)) = self.peek_kind() {
                    let name = self.expect_upper_ident("expected name in where clause")?;
                    self.skip_newlines();
                    if self.match_token(&TokenKind::Eq) {
                        self.skip_newlines();
                        let ty = self.type_annotation()?;
                        impl_where_clause.push(WhereItem::TypeAssignment { name, ty });
                    } else if self.match_token(&TokenKind::Colon) {
                        let trait_name =
                            self.expect_upper_ident("expected trait name in where clause")?;
                        impl_where_clause.push(WhereItem::TraitBound(TraitBound {
                            type_var: name,
                            trait_name,
                        }));
                    } else {
                        self.error_at_current("expected '=' or ':' after name in where clause");
                        return None;
                    }
                } else {
                    // lowercase ident: trait bound
                    let type_var = self.expect_ident("expected name in where clause")?;
                    self.expect(
                        &TokenKind::Colon,
                        "expected ':' after type variable in where clause",
                    )?;
                    let trait_name =
                        self.expect_upper_ident("expected trait name in where clause")?;
                    impl_where_clause.push(WhereItem::TraitBound(TraitBound {
                        type_var,
                        trait_name,
                    }));
                }
                self.skip_newlines();
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
        }

        let delimiter = self.expect_block_start("expected impl body block after impl header")?;
        let mut methods: Vec<FnDecl> = Vec::new();
        self.skip_newlines();

        // Resolve Actor control type from where-clause assignment only.
        let control_type = impl_where_clause.iter().find_map(|item| match item {
            WhereItem::TypeAssignment { name, ty } if name.node == "Control" => Some(ty.clone()),
            _ => None,
        });

        while !self.at_block_end(delimiter) && !self.at_eof() {
            let method_start = self.current_span();
            let method_doc = self.consume_doc_comment_block();
            let method_public = self.match_token(&TokenKind::Pub);
            if !self.match_token(&TokenKind::Fn) {
                self.error_at_current("expected 'fn' in impl block");
                return None;
            }
            if let Some(decl) = self.fn_decl(method_public, method_start, method_doc, vec![])
                && let DeclKind::Function(new_fn) = decl.node
            {
                methods.push(new_fn);
            }
            self.skip_newlines();
        }
        let end = self.current_span();
        self.expect_block_end(delimiter, "expected end of impl block")?;

        Some(Spanned::new(
            DeclKind::ImplBlock(ImplBlock {
                trait_name,
                type_name,
                type_params,
                methods,
                control_type,
                where_clause: impl_where_clause,
            }),
            start.merge(end),
        ))
    }

    /// Parse an optional `where T: Trait, U: Other` clause.
    fn where_clause(&mut self) -> Option<Vec<TraitBound>> {
        if !self.match_token(&TokenKind::Where) {
            return Some(Vec::new());
        }
        let mut bounds = Vec::new();
        loop {
            self.skip_newlines();
            let type_var = match self.peek_kind() {
                Some(TokenKind::Ident(_)) => {
                    self.expect_ident("expected type variable in where clause")?
                }
                Some(TokenKind::UpperIdent(_)) => {
                    self.expect_upper_ident("expected type variable in where clause")?
                }
                _ => {
                    self.error_at_current("expected type variable in where clause");
                    return None;
                }
            };
            self.expect(
                &TokenKind::Colon,
                "expected ':' after type variable in where clause",
            )?;
            let trait_name = self.expect_upper_ident("expected trait name in where clause")?;
            bounds.push(TraitBound {
                type_var,
                trait_name,
            });
            self.skip_newlines();
            if !self.match_token(&TokenKind::Comma) {
                break;
            }
        }
        Some(bounds)
    }

    fn parse_effect_row_name(&mut self, msg: &str) -> Option<String> {
        match self.peek_kind() {
            Some(TokenKind::Ident(name)) | Some(TokenKind::UpperIdent(name)) => {
                let name = name.clone();
                self.advance();
                Some(name)
            }
            _ => {
                self.error_at_current(msg);
                None
            }
        }
    }

    fn parse_effect_row_item(&mut self, msg: &str) -> Option<EffectRowItem> {
        let name = self.parse_effect_row_name(msg)?;
        self.skip_newlines();
        let payload = match self.peek_kind() {
            Some(TokenKind::Ident(payload)) | Some(TokenKind::UpperIdent(payload)) => {
                let payload = payload.clone();
                self.advance();
                Some(payload)
            }
            _ => None,
        };
        Some(EffectRowItem { name, payload })
    }

    fn parse_effect_term(
        &mut self,
        missing_msg: &str,
        invalid_msg: &str,
    ) -> Option<Spanned<EffectAnnotation>> {
        let start = self.current_span();
        if self.match_token(&TokenKind::Pipe) {
            self.skip_newlines();
            let rest = Some(self.parse_effect_row_name(
                "expected tail effect variable after '|' in effect row",
            )?);
            self.skip_newlines();
            if !matches!(self.peek_kind(), Some(TokenKind::RBracket)) {
                self.error_at_current("expected ] in effect arrow");
                return None;
            }
            let end = self.current_span();
            return Some(Spanned::new(
                EffectAnnotation::Row(EffectRowAnnotation {
                    effects: Vec::new(),
                    rest,
                }),
                start.merge(end),
            ));
        }
        let (first_name, first_is_ident) = match self.peek_kind() {
            Some(TokenKind::Ident(name)) => {
                let name = name.clone();
                self.advance();
                (name, true)
            }
            Some(TokenKind::UpperIdent(name)) => {
                let name = name.clone();
                self.advance();
                (name, false)
            }
            Some(TokenKind::RBracket) => {
                self.error_at_current(missing_msg);
                return None;
            }
            _ => {
                self.error_at_current(invalid_msg);
                return None;
            }
        };
        let mut effects = Vec::new();
        self.skip_newlines();
        let mut legacy_candidate = true;
        let first_payload = match self.peek_kind() {
            Some(TokenKind::Ident(payload)) | Some(TokenKind::UpperIdent(payload)) => {
                legacy_candidate = false;
                let payload = payload.clone();
                self.advance();
                Some(payload)
            }
            _ => None,
        };
        effects.push(EffectRowItem {
            name: first_name.clone(),
            payload: first_payload,
        });

        self.skip_newlines();
        while self.match_token(&TokenKind::Comma) {
            legacy_candidate = false;
            self.skip_newlines();
            let item = self.parse_effect_row_item("expected effect name after ',' in effect row")?;
            effects.push(item);
            self.skip_newlines();
        }

        let rest = if self.match_token(&TokenKind::Pipe) {
            legacy_candidate = false;
            self.skip_newlines();
            Some(self.parse_effect_row_name(
                "expected tail effect variable after '|' in effect row",
            )?)
        } else {
            None
        };

        self.skip_newlines();
        if !matches!(self.peek_kind(), Some(TokenKind::RBracket)) {
            if matches!(self.peek_kind(), Some(TokenKind::Gt)) {
                self.error_at_current("expected ] in effect arrow");
            } else {
                self.error_at_current("expected ',' or '|' or ']' in effect row");
            }
            return None;
        }

        let annotation = if legacy_candidate && rest.is_none() && effects.len() == 1 {
            match first_name.as_str() {
                "pure" => EffectAnnotation::Pure,
                "volatile" => EffectAnnotation::Volatile,
                "impure" => EffectAnnotation::Impure,
                _ if first_is_ident => EffectAnnotation::Var(first_name),
                _ => EffectAnnotation::Row(EffectRowAnnotation { effects, rest }),
            }
        } else {
            EffectAnnotation::Row(EffectRowAnnotation { effects, rest })
        };
        let end = self.current_span();
        Some(Spanned::new(annotation, start.merge(end)))
    }

    /// Parse required return arrow syntax:
    /// - `->` (no explicit effect annotation)
    /// - `-[effect]>` (explicit effect annotation)
    fn parse_required_return_arrow_effect(
        &mut self,
        missing_msg: &str,
    ) -> Option<Option<Spanned<EffectAnnotation>>> {
        if self.match_token(&TokenKind::Arrow) {
            return Some(None);
        }

        if !self.match_token(&TokenKind::Minus) {
            self.error_at_current(missing_msg);
            return None;
        }

        let start = self.current_span();
        self.expect(
            &TokenKind::LBracket,
            "expected '[' after '-' in effect arrow",
        )?;
        self.skip_newlines();
        let effect = self.parse_effect_term(
            "expected effect after -[",
            "expected pure|volatile|impure or effect variable",
        )?;
        self.skip_newlines();
        self.expect(&TokenKind::RBracket, "expected ] in effect arrow")?;
        self.skip_newlines();
        self.expect(&TokenKind::Gt, "expected > to complete effect arrow")?;
        let end = self.current_span();

        Some(Some(Spanned::new(effect.node, start.merge(end))))
    }

    fn fn_decl(
        &mut self,
        public: bool,
        start: Span,
        doc: Option<String>,
        annotations: Vec<Annotation>,
    ) -> Option<Decl> {
        // fn name(params) [-> RetType] [where T: Trait] { body }
        let name = self.expect_ident("expected function name")?;
        self.expect(&TokenKind::LParen, "expected '(' after function name")?;
        let params = self.param_list()?;
        self.expect(&TokenKind::RParen, "expected ')' after parameters")?;
        let effect_annotation = self.parse_required_return_arrow_effect(
            "fn declarations require a return type: add `-> Type` or `-[effect]> Type` after the parameter list",
        )?;
        let return_annotation = Some(self.type_annotation()?);
        let where_clause = self.where_clause()?;

        let body = self.parse_block_expr("expected function body block")?;
        let (testing, testing_tags) = if self.check(&TokenKind::Testing) {
            let (tags, block) = self.testing_block()?;
            (Some(Box::new(block)), tags)
        } else {
            (None, vec![])
        };
        let end = self.current_span();

        Some(Spanned::new(
            DeclKind::Function(FnDecl {
                public,
                name,
                doc,
                annotations,
                params,
                return_annotation,
                effect_annotation,
                body,
                testing,
                testing_tags,
                span: start.merge(end),
                where_clause,
            }),
            start.merge(end),
        ))
    }

    /// Parse an `expr` declaration: `expr name(params) [-> RetType] [where ...] { body }`.
    /// Same syntax as `fn` — the MIR body restriction is enforced after parsing.
    fn expr_fn_decl(
        &mut self,
        public: bool,
        start: Span,
        doc: Option<String>,
        annotations: Vec<Annotation>,
    ) -> Option<Decl> {
        let name = self.expect_ident("expected expression function name")?;
        self.expect(&TokenKind::LParen, "expected '(' after expr function name")?;
        let params = self.param_list()?;
        self.expect(&TokenKind::RParen, "expected ')' after parameters")?;

        let effect_annotation = self.parse_required_return_arrow_effect(
            "expr declarations require a return type: add `-> Type` or `-[effect]> Type` after the parameter list",
        )?;
        let return_annotation = Some(self.type_annotation()?);
        let where_clause = self.where_clause()?;

        let body = self.parse_block_expr("expected expr body block")?;
        let (testing, testing_tags) = if self.check(&TokenKind::Testing) {
            let (tags, block) = self.testing_block()?;
            (Some(Box::new(block)), tags)
        } else {
            (None, vec![])
        };
        let end = self.current_span();

        Some(Spanned::new(
            DeclKind::ExprFn(ExprDecl {
                public,
                name,
                doc,
                annotations,
                params,
                return_annotation,
                effect_annotation,
                body,
                testing,
                testing_tags,
                span: start.merge(end),
                where_clause,
            }),
            start.merge(end),
        ))
    }

    fn testing_block(&mut self) -> Option<(Vec<Spanned<String>>, Expr)> {
        self.expect(&TokenKind::Testing, "expected `testing`")?;
        let tags = self.parse_optional_tags_clause()?;
        let body = self.parse_block_expr("expected testing block body")?;
        Some((tags, body))
    }

    fn test_decl(&mut self, start: Span) -> Option<Decl> {
        // test ["property"] ["(" iterations: <int> ")"] "name" { body }
        let is_property = self.match_token(&TokenKind::Property);

        let iterations = if self.match_token(&TokenKind::LParen) {
            self.skip_newlines();
            let key = self.expect_ident("expected `iterations` in test options")?;
            if key.node != "iterations" {
                self.error_at_current("expected `iterations` in test options");
                return None;
            }
            self.expect(&TokenKind::Colon, "expected ':' after `iterations`")?;
            self.skip_newlines();
            let n = match self.peek_kind() {
                Some(TokenKind::Int(v)) if *v >= 1 => {
                    let out = *v as usize;
                    self.advance();
                    out
                }
                Some(TokenKind::Int(_)) => {
                    self.error_at_current("iterations must be >= 1");
                    return None;
                }
                _ => {
                    self.error_at_current("expected integer literal for iterations");
                    return None;
                }
            };
            self.skip_newlines();
            self.expect(&TokenKind::RParen, "expected ')' after test options")?;
            Some(n)
        } else {
            None
        };

        let name = match self.peek_kind() {
            Some(TokenKind::String(s)) => {
                let span = self.current_span();
                let text = s.clone();
                self.advance();
                Spanned::new(text, span)
            }
            _ => {
                self.error_at_current("expected test name string after `test`");
                return None;
            }
        };

        let tags = self.parse_optional_tags_clause()?;
        let body = self.parse_block_expr("expected test body block")?;
        let end = self.current_span();

        Some(Spanned::new(
            DeclKind::Test(TestDecl {
                name,
                body,
                is_property,
                iterations,
                tags,
                span: start.merge(end),
            }),
            start.merge(end),
        ))
    }

    fn parse_optional_tags_clause(&mut self) -> Option<Vec<Spanned<String>>> {
        let has_tags = matches!(self.peek_kind(), Some(TokenKind::Ident(name)) if name == "tags");
        if !has_tags {
            return Some(vec![]);
        }
        self.advance(); // consume `tags`
        self.skip_newlines();
        self.expect(&TokenKind::LBracket, "expected '[' after `tags`")?;
        self.skip_newlines();

        let mut tags = Vec::new();
        if !self.check(&TokenKind::RBracket) {
            loop {
                self.expect(&TokenKind::Colon, "expected ':' before tag atom")?;
                let tag = self.expect_ident("expected tag name after ':'")?;
                tags.push(tag);
                self.skip_newlines();
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
                self.skip_newlines();
                if self.check(&TokenKind::RBracket) {
                    break;
                }
            }
        }
        self.expect(&TokenKind::RBracket, "expected ']' after tag list")?;
        Some(tags)
    }

    /// Parse function/trait parameters with optional labels/defaults.
    fn param_list(&mut self) -> Option<Vec<Param>> {
        let mut params = Vec::new();
        let mut seen_labeled = false;
        let mut seen_default = false;
        self.skip_newlines();
        if self.check(&TokenKind::RParen) {
            return Some(params);
        }
        loop {
            self.skip_newlines();
            let param = self.param_decl()?;

            let is_positional = matches!(param.label, ParamLabel::Positional);
            if is_positional && seen_labeled {
                self.error_at_current(
                    "positional parameters (`_`) must come before labeled parameters",
                );
            }
            if !is_positional {
                seen_labeled = true;
            }
            if is_positional && param.default.is_some() {
                self.error_at_current("positional parameters (`_`) cannot have default values");
            }
            if seen_default && param.default.is_none() {
                self.error_at_current(
                    "once a parameter has a default, all subsequent parameters must have defaults",
                );
            }
            if param.default.is_some() {
                seen_default = true;
            }

            params.push(param);
            self.skip_newlines();
            if !self.match_token(&TokenKind::Comma) {
                break;
            }
        }
        Some(params)
    }

    fn param_decl(&mut self) -> Option<Param> {
        let label = if matches!(self.peek_kind(), Some(TokenKind::Ident(s)) if s == "_") {
            self.advance();
            self.skip_newlines();
            ParamLabel::Positional
        } else if let (
            Some(TokenKind::Ident(first)),
            Some(TokenKind::Ident(_)),
            Some(TokenKind::Colon),
        ) = (
            self.peek_kind(),
            self.peek_at(1).map(|t| &t.kind),
            self.peek_at(2).map(|t| &t.kind),
        ) {
            if first != "_" {
                let label = self.expect_ident("expected parameter label")?;
                self.skip_newlines();
                ParamLabel::Label(label)
            } else {
                ParamLabel::Implicit
            }
        } else {
            ParamLabel::Implicit
        };

        let pattern = self.pattern()?;
        let annotation = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.type_annotation()?)
        } else {
            None
        };
        let default = if self.match_token(&TokenKind::Eq) {
            self.skip_newlines();
            Some(self.expression()?)
        } else {
            None
        };

        Some(Param {
            label,
            pattern,
            annotation,
            default,
        })
    }

    fn call_arg_list(&mut self) -> Option<Vec<Argument>> {
        let mut args = Vec::new();
        let mut seen_labeled = false;
        self.skip_newlines();
        if self.check(&TokenKind::RParen) {
            return Some(args);
        }
        loop {
            self.skip_newlines();
            // Allow trailing commas in call arguments: f(1, 2,)
            if self.check(&TokenKind::RParen) {
                break;
            }
            let label = if let (Some(TokenKind::Ident(_)), Some(TokenKind::Colon)) =
                (self.peek_kind(), self.peek_at(1).map(|t| &t.kind))
            {
                seen_labeled = true;
                let label = self.expect_ident("expected argument label")?;
                self.advance();
                Some(label)
            } else {
                if seen_labeled {
                    self.error_at_current(
                        "positional arguments must come before labeled arguments",
                    );
                }
                None
            };

            let value = self.expression()?;
            args.push(Argument { label, value });
            self.skip_newlines();
            if !self.match_token(&TokenKind::Comma) {
                break;
            }
        }
        Some(args)
    }

    fn type_annotation(&mut self) -> Option<Spanned<TypeAnnotation>> {
        let start = self.current_span();
        if self.match_token(&TokenKind::Forall) {
            self.skip_newlines();
            let mut type_vars = Vec::new();
            loop {
                let type_var = self.expect_ident("expected type variable after `forall`")?;
                type_vars.push(type_var.node);
                self.skip_newlines();
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
                self.skip_newlines();
            }
            self.expect(&TokenKind::Dot, "expected '.' after forall type variables")?;
            self.skip_newlines();
            let inner = self.type_annotation()?.node;
            let end = self.current_span();
            return Some(Spanned::new(
                TypeAnnotation::Forall {
                    type_vars,
                    ty: Box::new(inner),
                },
                start.merge(end),
            ));
        }
        if self.match_token(&TokenKind::Fn) {
            self.expect(
                &TokenKind::LParen,
                "expected '(' after `fn` in type annotation",
            )?;
            let mut params = Vec::new();
            self.skip_newlines();
            if !self.check(&TokenKind::RParen) {
                loop {
                    self.skip_newlines();
                    params.push(self.type_annotation()?.node);
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                }
            }
            self.expect(
                &TokenKind::RParen,
                "expected ')' in function type annotation",
            )?;
            let effect_annotation = if self.match_token(&TokenKind::Arrow) {
                None
            } else if self.match_token(&TokenKind::Minus) {
                let start = self.current_span();
                self.expect(
                    &TokenKind::LBracket,
                    "expected '[' after '-' in effect arrow",
                )?;
                self.skip_newlines();
                let effect = self.parse_effect_term(
                    "expected effect after -[",
                    "expected pure|volatile|impure or effect variable",
                )?;
                self.skip_newlines();
                self.expect(&TokenKind::RBracket, "expected ] in effect arrow")?;
                self.skip_newlines();
                self.expect(&TokenKind::Gt, "expected > to complete effect arrow")?;
                let end = self.current_span();
                Some(Spanned::new(effect.node, start.merge(end)))
            } else {
                self.expect(
                    &TokenKind::Arrow,
                    "expected '->' or '-[effect]>' in function type annotation",
                )?;
                None
            };
            self.skip_newlines();
            let ret = self.type_annotation()?.node;
            let end = self.current_span();
            return Some(Spanned::new(
                if let Some(effect) = effect_annotation {
                    TypeAnnotation::FunctionWithEffect(params, effect, Box::new(ret))
                } else {
                    TypeAnnotation::Function(params, Box::new(ret))
                },
                start.merge(end),
            ));
        }
        if self.match_token(&TokenKind::LBracket) {
            self.skip_newlines();
            let mut effects = Vec::new();
            let mut rest = None;

            if self.match_token(&TokenKind::Pipe) {
                self.skip_newlines();
                rest = Some(self.parse_effect_row_name(
                    "expected tail effect variable after '|' in effect row annotation",
                )?);
                self.skip_newlines();
            } else if !self.check(&TokenKind::RBracket) {
                let first = self.parse_effect_row_item("expected effect name in effect row annotation")?;
                effects.push(first);
                self.skip_newlines();
                while self.match_token(&TokenKind::Comma) {
                    self.skip_newlines();
                    let item = self.parse_effect_row_item(
                        "expected effect name after ',' in effect row annotation",
                    )?;
                    effects.push(item);
                    self.skip_newlines();
                }
                if self.match_token(&TokenKind::Pipe) {
                    self.skip_newlines();
                    rest = Some(self.parse_effect_row_name(
                        "expected tail effect variable after '|' in effect row annotation",
                    )?);
                    self.skip_newlines();
                }
            }

            self.expect(&TokenKind::RBracket, "expected ']' in effect row annotation")?;
            let end = self.current_span();
            return Some(Spanned::new(
                TypeAnnotation::EffectRow(EffectRowAnnotation { effects, rest }),
                start.merge(end),
            ));
        }
        // Simple: Named or Applied
        if let Some(name) = self.try_ident() {
            let name_str = name.node.clone();
            if name_str == "any" {
                let mut bounds: Vec<String> = Vec::new();
                if self.match_token(&TokenKind::LParen) {
                    self.skip_newlines();
                    loop {
                        self.skip_newlines();
                        let bound =
                            self.expect_upper_ident("expected trait name in existential")?;
                        bounds.push(bound.node);
                        self.skip_newlines();
                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(
                        &TokenKind::RParen,
                        "expected ')' after existential trait bounds",
                    )?;
                } else {
                    let bound = self.expect_upper_ident("expected trait name after `any`")?;
                    bounds.push(bound.node);
                }

                let mut associated_types: Vec<(String, TypeAnnotation)> = Vec::new();
                if self.match_token(&TokenKind::Where) {
                    loop {
                        self.skip_newlines();
                        let assoc_name = self
                            .expect_upper_ident("expected associated type name in where clause")?;
                        self.skip_newlines();
                        self.expect(
                            &TokenKind::Eq,
                            "expected '=' in existential associated type constraint",
                        )?;
                        self.skip_newlines();
                        let assoc_ty = self.type_annotation()?.node;
                        associated_types.push((assoc_name.node, assoc_ty));
                        self.skip_newlines();
                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                    }
                }

                let end = self.current_span();
                return Some(Spanned::new(
                    TypeAnnotation::Existential {
                        bounds,
                        associated_types,
                    },
                    start.merge(end),
                ));
            }
            if self.match_token(&TokenKind::LParen) {
                // Applied: List(Int), Result(T, E)
                let mut args = Vec::new();
                self.skip_newlines();
                if !self.check(&TokenKind::RParen) {
                    loop {
                        self.skip_newlines();
                        args.push(self.type_application_arg_annotation()?);
                        self.skip_newlines();
                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                    }
                }
                let end_span = self.current_span();
                self.expect(&TokenKind::RParen, "expected ')' in type application")?;
                Some(Spanned::new(
                    TypeAnnotation::Applied(name_str, args),
                    start.merge(end_span),
                ))
            } else if self.match_token(&TokenKind::Question) {
                let end = self.current_span();
                Some(Spanned::new(
                    TypeAnnotation::Optional(Box::new(TypeAnnotation::Named(name_str))),
                    start.merge(end),
                ))
            } else {
                Some(Spanned::new(TypeAnnotation::Named(name_str), name.span))
            }
        } else if let Some(name) = self.try_upper_ident() {
            let name_str = name.node.clone();
            // Self.Name → Projection type (associated type access)
            if name_str == "Self" && self.check(&TokenKind::Dot) {
                self.advance(); // consume Dot
                if let Some(assoc_name) = self.try_upper_ident() {
                    let end = assoc_name.span;
                    Some(Spanned::new(
                        TypeAnnotation::Projection {
                            base: "Self".to_string(),
                            name: assoc_name.node,
                        },
                        start.merge(end),
                    ))
                } else {
                    self.error_at_current("expected associated type name after 'Self.'");
                    None
                }
            } else if self.match_token(&TokenKind::LParen) {
                let mut args = Vec::new();
                self.skip_newlines();
                if !self.check(&TokenKind::RParen) {
                    loop {
                        self.skip_newlines();
                        args.push(self.type_application_arg_annotation()?);
                        self.skip_newlines();
                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                    }
                }
                let end_span = self.current_span();
                self.expect(&TokenKind::RParen, "expected ')' in type application")?;
                Some(Spanned::new(
                    TypeAnnotation::Applied(name_str, args),
                    start.merge(end_span),
                ))
            } else if self.match_token(&TokenKind::Question) {
                let end = self.current_span();
                Some(Spanned::new(
                    TypeAnnotation::Optional(Box::new(TypeAnnotation::Named(name_str))),
                    start.merge(end),
                ))
            } else {
                Some(Spanned::new(TypeAnnotation::Named(name_str), name.span))
            }
        } else if self.match_token(&TokenKind::HashParen) {
            // Tuple type: #(A, B, C)
            let mut elems = Vec::new();
            self.skip_newlines();
            if !self.check(&TokenKind::RParen) {
                loop {
                    self.skip_newlines();
                    elems.push(self.type_annotation()?.node);
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                }
            }
            let end_span = self.current_span();
            self.expect(&TokenKind::RParen, "expected ')' in tuple type")?;
            Some(Spanned::new(
                TypeAnnotation::Tuple(elems),
                start.merge(end_span),
            ))
        } else {
            self.error_at_current("expected type annotation");
            None
        }
    }

    fn type_application_arg_annotation(&mut self) -> Option<TypeAnnotation> {
        // Integer literals in type-application positions produce DimLiteral nodes.
        // The type checker validates whether the constructor accepts dimension parameters.
        if let Some(TokenKind::Int(n)) = self.peek_kind() {
            let n = *n;
            self.advance();
            return Some(TypeAnnotation::DimLiteral(n));
        }
        Some(self.type_annotation()?.node)
    }

    // -- Expression parsing --

    fn expression(&mut self) -> Option<Expr> {
        // Bare lambda: ident -> expr
        // Must be checked here (not in primary) so it doesn't fire inside
        // binary-op RHS parsing — e.g. `cond { x > hi -> hi }` would
        // otherwise parse `hi -> hi` as a lambda.
        if let Some(TokenKind::Ident(name)) = self.peek_kind() {
            let name = name.clone();
            if self.peek_at(1).is_some_and(|t| t.kind == TokenKind::Arrow) {
                let start = self.current_span();
                return self.lambda_bare(name, start);
            }
        }
        self.pratt_expr(0)
    }

    /// Pratt-style precedence climbing.
    fn pratt_expr(&mut self, min_bp: u8) -> Option<Expr> {
        let mut lhs = self.unary_or_primary()?;

        loop {
            self.skip_newlines_if_continuation();

            // Postfix: `.field`, `(args)`, `as Type`
            if let Some(postfix_bp) = self.postfix_bp() {
                if postfix_bp < min_bp {
                    break;
                }
                lhs = self.parse_postfix(lhs)?;
                continue;
            }

            // Infix binary operators (including pipe ops and `when` guards)
            let Some((l_bp, r_bp)) = self.infix_bp() else {
                break;
            };
            if l_bp < min_bp {
                break;
            }

            // Handle compound `not in` (two tokens) vs single-token operators.
            let (op_token, is_not_in) = if matches!(self.peek_kind(), Some(TokenKind::Not))
                && self.peek_at(1).is_some_and(|t| t.kind == TokenKind::In)
            {
                let not_tok = self.advance(); // consume `not`
                self.advance(); // consume `in`
                (not_tok, true)
            } else {
                (self.advance(), false)
            };

            self.skip_newlines();
            let rhs = self.pratt_expr(r_bp)?;

            let span = lhs.span.merge(rhs.span);
            lhs = if is_not_in {
                Spanned::new(
                    ExprKind::BinaryOp {
                        op: Spanned::new(BinOp::NotIn, op_token.span),
                        left: Box::new(lhs),
                        right: Box::new(rhs),
                    },
                    span,
                )
            } else {
                match token_to_binop(&op_token.kind) {
                    Some(op) => Spanned::new(
                        ExprKind::BinaryOp {
                            op: Spanned::new(op, op_token.span),
                            left: Box::new(lhs),
                            right: Box::new(rhs),
                        },
                        span,
                    ),
                    None if matches!(op_token.kind, TokenKind::DotDot | TokenKind::DotDotEq) => {
                        Spanned::new(
                            ExprKind::Range {
                                start: Box::new(lhs),
                                end: Box::new(rhs),
                                inclusive: matches!(op_token.kind, TokenKind::DotDotEq),
                            },
                            span,
                        )
                    }
                    None if matches!(op_token.kind, TokenKind::When) => Spanned::new(
                        ExprKind::WhenGuard {
                            body: Box::new(lhs),
                            condition: Box::new(rhs),
                        },
                        span,
                    ),
                    _ => unreachable!(),
                }
            };
        }

        Some(lhs)
    }

    fn unary_or_primary(&mut self) -> Option<Expr> {
        let start = self.current_span();

        // Unary prefix: - and not
        if self.check(&TokenKind::Minus) {
            let op_token = self.advance();
            let operand = self.pratt_expr(15)?; // unary BP
            let span = start.merge(operand.span);
            return Some(Spanned::new(
                ExprKind::UnaryOp {
                    op: Spanned::new(UnaryOp::Neg, op_token.span),
                    operand: Box::new(operand),
                },
                span,
            ));
        }
        if self.check(&TokenKind::Not) {
            let op_token = self.advance();
            let operand = self.pratt_expr(15)?;
            let span = start.merge(operand.span);
            return Some(Spanned::new(
                ExprKind::UnaryOp {
                    op: Spanned::new(UnaryOp::Not, op_token.span),
                    operand: Box::new(operand),
                },
                span,
            ));
        }

        self.primary()
    }

    fn primary(&mut self) -> Option<Expr> {
        let start = self.current_span();

        // Int literal
        if let Some(TokenKind::Int(n)) = self.peek_kind() {
            let n = *n;
            self.advance();
            return Some(Spanned::new(ExprKind::Lit(Lit::Int(n)), start));
        }

        // Float literal
        if let Some(TokenKind::Float(f)) = self.peek_kind() {
            let f = *f;
            self.advance();
            return Some(Spanned::new(ExprKind::Lit(Lit::Float(f)), start));
        }

        // String literal
        if let Some(TokenKind::String(s)) = self.peek_kind() {
            let s = s.clone();
            self.advance();
            return Some(Spanned::new(ExprKind::Lit(Lit::String(s)), start));
        }

        // String interpolation
        if let Some(TokenKind::StringInterp(parts)) = self.peek_kind() {
            let parts = parts.clone();
            self.advance();
            let mut interp_parts = Vec::new();
            for part in parts {
                match part {
                    crate::token::StringPart::Literal(s) => {
                        interp_parts.push(StringInterpPart::Literal(s));
                    }
                    crate::token::StringPart::Expr(src) => {
                        let tokens = match crate::lexer::lex_layout(&src, self.file) {
                            Ok((t, _warnings)) => t,
                            Err(diags) => {
                                self.errors.extend(diags);
                                return None;
                            }
                        };
                        let mut sub = Parser::new(tokens, self.file);
                        let expr = sub.expression();
                        if !sub.errors.is_empty() {
                            self.errors.extend(sub.errors);
                            return None;
                        }
                        match expr {
                            Some(e) => {
                                interp_parts.push(StringInterpPart::Expr(Box::new(e)));
                            }
                            None => {
                                self.error_at_current(
                                    "expected expression in string interpolation",
                                );
                                return None;
                            }
                        }
                    }
                }
            }
            return Some(Spanned::new(ExprKind::StringInterp(interp_parts), start));
        }

        // Bool literals
        if self.check(&TokenKind::True) {
            self.advance();
            return Some(Spanned::new(ExprKind::Lit(Lit::Bool(true)), start));
        }
        if self.check(&TokenKind::False) {
            self.advance();
            return Some(Spanned::new(ExprKind::Lit(Lit::Bool(false)), start));
        }

        // None
        if self.check(&TokenKind::NoneKw) {
            self.advance();
            return Some(Spanned::new(ExprKind::None, start));
        }

        // Let binding
        if self.check(&TokenKind::Let) {
            return self.let_binding();
        }

        // If expression
        if self.check(&TokenKind::If) {
            return self.if_expr();
        }

        // Case expression
        if self.check(&TokenKind::Case) {
            return self.case_expr();
        }

        // Cond expression
        if self.check(&TokenKind::Cond) {
            return self.cond_expr();
        }

        // For comprehension: for x in xs, x > 0 { x * 2 } [into Set]
        if self.check_ident("for") {
            return self.for_expr();
        }

        // Use expression: use pattern <- expr / use <- expr
        if self.check(&TokenKind::Use) {
            return self.use_expr();
        }

        // Kea v0 does not include frame literals.
        if self.check_ident("frame")
            && self
                .peek_at(1)
                .is_some_and(|t| matches!(t.kind, TokenKind::LBrace))
        {
            self.error_at_current("`frame` literals are not supported in Kea v0");
            return None;
        }

        // Kea v0 does not include embedded SQL blocks.
        if self.check(&TokenKind::Sql) {
            self.error_at_current("`sql { ... }` blocks are not supported in Kea v0");
            return None;
        }

        // Kea v0 does not include embedded html/markdown template blocks.
        if self.check(&TokenKind::Html) {
            self.error_at_current("`html { ... }` blocks are not supported in Kea v0");
            return None;
        }
        if self.check(&TokenKind::Markdown) {
            self.error_at_current("`markdown { ... }` blocks are not supported in Kea v0");
            return None;
        }

        // Spawn expression: spawn <expr>
        if self.check(&TokenKind::Spawn) {
            return self.spawn_expr();
        }

        // Await expression: await expr / await? expr
        if self.check(&TokenKind::Await) {
            return self.await_expr();
        }

        // Stream generator block: stream { ... } [with { buffer: N }]
        if self.check(&TokenKind::Stream) {
            return self.stream_block_expr();
        }

        // Yield expressions (only valid in stream blocks at type-check time).
        if self.check(&TokenKind::Yield) {
            return self.yield_expr();
        }
        if self.check(&TokenKind::YieldFrom) {
            return self.yield_from_expr();
        }

        // Tuple: #(exprs)
        if self.check(&TokenKind::HashParen) {
            return self.tuple_expr();
        }

        // Anonymous record: #{field: val, ...}
        if self.check(&TokenKind::HashBrace) {
            return self.anon_record_expr();
        }

        // Map literal: %{key => value, ...}
        if self.check(&TokenKind::PercentBrace) {
            return self.map_literal();
        }

        // List: [exprs]
        if self.check(&TokenKind::LBracket) {
            return self.list_expr();
        }

        // Parenthesized expression, unit literal, or lambda: () -> expr, (params) -> expr
        if self.check(&TokenKind::LParen) {
            if self.is_paren_lambda_start() {
                return self.lambda_paren(start);
            }
            self.advance();
            self.skip_newlines();
            if self.match_token(&TokenKind::RParen) {
                let end = self.current_span();
                return Some(Spanned::new(ExprKind::Lit(Lit::Unit), start.merge(end)));
            }
            let inner = self.expression()?;
            self.skip_newlines();
            self.expect(&TokenKind::RParen, "expected ')'")?;
            return Some(inner);
        }

        // Upper identifier: named record construction or constructor (Some, Ok, Err)
        if let Some(TokenKind::UpperIdent(name)) = self.peek_kind() {
            let name = name.clone();
            self.advance();
            let name_spanned = Spanned::new(name, start);
            // Named record construction: Name { field: val, ... }
            // In case scrutinee position, disambiguate with look-ahead:
            // `Green { Red -> ... }` is case body, not named record.
            // `User { name: "alice" } { ... }` is named record then case body.
            if self.check(&TokenKind::LBrace)
                && (!self.restrict_struct_literals || self.looks_like_record_after_brace())
            {
                return self.named_record_expr(name_spanned, start);
            }
            // Check for constructor args: Name(args)
            if self.check(&TokenKind::LParen) {
                self.advance();
                let args = self.call_arg_list()?;
                let end = self.current_span();
                self.expect(&TokenKind::RParen, "expected ')' after constructor args")?;
                return Some(Spanned::new(
                    ExprKind::Constructor {
                        name: name_spanned,
                        args,
                    },
                    start.merge(end),
                ));
            }
            // Constructor with no args — treat as variable
            return Some(Spanned::new(
                ExprKind::Constructor {
                    name: name_spanned,
                    args: vec![],
                },
                start,
            ));
        }

        if self.check(&TokenKind::Assert)
            || self.check(&TokenKind::AssertEq)
            || self.check(&TokenKind::AssertNe)
            || self.check(&TokenKind::AssertFrameEqual)
            || self.check(&TokenKind::AssertSnapshot)
            || self.check(&TokenKind::AssertOk)
            || self.check(&TokenKind::AssertError)
        {
            return self.assert_expr();
        }

        // Actor send/call/try_send
        if let Some(TokenKind::Ident(name)) = self.peek_kind()
            && (name == "send" || name == "call" || name == "try_send")
            && (self.peek_is(|k| matches!(k, TokenKind::LParen))
                || (self
                    .peek_at(1)
                    .is_some_and(|t| t.kind == TokenKind::Question)
                    && self.peek_at(2).is_some_and(|t| t.kind == TokenKind::LParen)))
        {
            return self.actor_send_or_call();
        }

        // Actor control_send: control_send(actor, signal)
        if let Some(TokenKind::Ident(name)) = self.peek_kind()
            && name == "control_send"
            && self.peek_is(|k| matches!(k, TokenKind::LParen))
        {
            return self.control_send();
        }

        // Atom literal: :name
        if self.check(&TokenKind::Colon) {
            // Peek ahead: if next token is an identifier, it's an atom expression.
            if let Some(TokenKind::Ident(_)) = self.tokens.get(self.pos + 1).map(|t| &t.kind) {
                self.advance(); // consume ':'
                let name = match self.peek_kind() {
                    Some(TokenKind::Ident(n)) => n.clone(),
                    _ => unreachable!(),
                };
                let end_tok = self.advance();
                return Some(Spanned::new(
                    ExprKind::Atom(name),
                    start.merge(end_tok.span),
                ));
            }
        }

        if self.check(&TokenKind::Dollar) {
            let tok = self.advance();
            self.errors.push(
                Diagnostic::error(
                    Category::Syntax,
                    "`$` placeholder expressions are not supported",
                )
                .at(SourceLocation {
                    file_id: self.file.0,
                    start: tok.span.start,
                    end: tok.span.end,
                }),
            );
            return None;
        }

        // Lowercase identifier: variable
        if let Some(TokenKind::Ident(name)) = self.peek_kind() {
            let name = name.clone();
            self.advance();
            return Some(Spanned::new(ExprKind::Var(name), start));
        }

        self.error_at_current("expected expression");
        None
    }

    /// Parse `:name` — colon followed by a lowercase identifier.
    fn expect_atom(&mut self, msg: &str) -> Option<Spanned<String>> {
        let start = self.current_span();
        if !self.match_token(&TokenKind::Colon) {
            self.error_at_current(msg);
            return None;
        }
        if let Some(TokenKind::Ident(name)) = self.peek_kind() {
            let name = name.clone();
            let end_tok = self.advance();
            Some(Spanned::new(name, start.merge(end_tok.span)))
        } else {
            self.error_at_current("expected column name after ':'");
            None
        }
    }

    // -- Let, if, case, etc. --

    fn let_binding(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume 'let'

        let pattern = self.pattern()?;
        let annotation = if self.match_token(&TokenKind::Colon) {
            Some(self.type_annotation()?)
        } else {
            None
        };
        self.expect(&TokenKind::Eq, "expected '=' in let binding")?;
        self.skip_newlines();
        let value = self.expression()?;
        let span = start.merge(value.span);

        Some(Spanned::new(
            ExprKind::Let {
                pattern,
                annotation,
                value: Box::new(value),
            },
            span,
        ))
    }

    fn if_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume 'if'

        let condition = self.expression()?;
        let then_branch = self.parse_block_expr("expected block after if condition")?;

        self.skip_newlines();
        if !self.match_token(&TokenKind::Else) {
            self.error_at_current("`if` requires an `else` branch");
            return None;
        }
        self.skip_newlines();
        let else_branch = if self.check(&TokenKind::If) {
            // else if
            Box::new(self.if_expr()?)
        } else {
            Box::new(self.parse_block_expr("expected block after else")?)
        };

        let end = else_branch.span;

        Some(Spanned::new(
            ExprKind::If {
                condition: Box::new(condition),
                then_branch: Box::new(then_branch),
                else_branch: Some(else_branch),
            },
            start.merge(end),
        ))
    }

    fn case_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume 'case'
        // Restrict struct literals in scrutinee position to avoid ambiguity:
        // `case Green { ... }` is a case over constructor Green, not a named record.
        let prev = self.restrict_struct_literals;
        self.restrict_struct_literals = true;
        let scrutinee = self.expression()?;
        self.restrict_struct_literals = prev;
        let delimiter = self.expect_block_start("expected block after case scrutinee")?;

        let mut arms = Vec::new();
        self.skip_newlines();
        while !self.at_block_end(delimiter) && !self.at_eof() {
            arms.push(self.case_arm()?);
            self.skip_newlines();
            let _ = self.match_token(&TokenKind::Comma);
            self.skip_newlines();
        }
        let end = self.current_span();
        self.expect_block_end(delimiter, "expected end of case block")?;

        Some(Spanned::new(
            ExprKind::Case {
                scrutinee: Box::new(scrutinee),
                arms,
            },
            start.merge(end),
        ))
    }

    fn cond_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume 'cond'
        let delimiter = self.expect_block_start("expected block after cond")?;

        let mut arms = Vec::new();
        self.skip_newlines();
        while !self.at_block_end(delimiter) && !self.at_eof() {
            arms.push(self.cond_arm()?);
            self.skip_newlines();
            let _ = self.match_token(&TokenKind::Comma);
            self.skip_newlines();
        }
        let end = self.current_span();
        self.expect_block_end(delimiter, "expected end of cond block")?;

        Some(Spanned::new(ExprKind::Cond { arms }, start.merge(end)))
    }

    fn cond_arm(&mut self) -> Option<CondArm> {
        let start = self.current_span();
        let condition = if let Some(TokenKind::Ident(name)) = self.peek_kind() {
            if name == "_" {
                let tok = self.advance();
                Spanned::new(ExprKind::Wildcard, tok.span)
            } else {
                self.expression()?
            }
        } else {
            self.expression()?
        };
        self.expect(&TokenKind::Arrow, "expected '->' after cond arm condition")?;
        self.skip_newlines();
        let body = if self.check(&TokenKind::Indent) {
            self.parse_block_expr("expected cond arm body block or expression")?
        } else {
            self.expression()?
        };
        let span = start.merge(body.span);
        Some(CondArm {
            condition: Box::new(condition),
            body: Box::new(body),
            span,
        })
    }

    fn for_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume `for`
        self.skip_newlines();

        let first_clause = self.parse_for_generator_clause()?;
        let (first_clause, first_guard) = split_for_generator_when_guard(first_clause);
        let mut clauses = vec![first_clause];
        if let Some(guard) = first_guard {
            clauses.push(ForClause::Guard(Box::new(guard)));
        } else {
            self.skip_newlines();
            if self.match_token(&TokenKind::When) {
                self.skip_newlines();
                clauses.push(ForClause::Guard(Box::new(self.expression()?)));
            }
        }

        loop {
            self.skip_newlines();
            if !self.match_token(&TokenKind::Comma) {
                break;
            }
            self.skip_newlines();

            // Allow trailing comma before the body block.
            if self.check(&TokenKind::Indent) {
                break;
            }

            if let Some(generator) = self.try_parse_for_generator_clause() {
                let (generator, inline_guard) = split_for_generator_when_guard(generator);
                clauses.push(generator);
                if let Some(guard) = inline_guard {
                    clauses.push(ForClause::Guard(Box::new(guard)));
                } else {
                    self.skip_newlines();
                    if self.match_token(&TokenKind::When) {
                        self.skip_newlines();
                        clauses.push(ForClause::Guard(Box::new(self.expression()?)));
                    }
                }
                continue;
            }

            if self.match_token(&TokenKind::When) {
                self.skip_newlines();
                clauses.push(ForClause::Guard(Box::new(self.expression()?)));
                continue;
            }

            self.error_at_current("expected generator clause or `when` guard in for comprehension");
            return None;
        }

        let body = self.parse_block_expr("expected block before for-comprehension body")?;
        let mut end = body.span;

        self.skip_newlines();
        let into_type = if self.check_ident("into") {
            self.advance(); // consume `into`
            self.skip_newlines();
            let ann = self.type_annotation()?;
            end = ann.span;
            Some(ann)
        } else {
            None
        };

        Some(Spanned::new(
            ExprKind::For(ForExpr {
                clauses,
                body: Box::new(body),
                into_type,
            }),
            start.merge(end),
        ))
    }

    fn use_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume `use`
        self.skip_newlines();

        let pattern = if self.match_token(&TokenKind::LeftArrow) {
            None
        } else {
            let pattern = self.pattern()?;
            self.skip_newlines();
            self.expect(&TokenKind::LeftArrow, "expected '<-' in use expression")?;
            Some(pattern)
        };

        self.skip_newlines();
        let rhs = self.expression()?;
        let end = rhs.span;

        Some(Spanned::new(
            ExprKind::Use(UseExpr {
                pattern,
                rhs: Box::new(rhs),
            }),
            start.merge(end),
        ))
    }

    fn try_parse_for_generator_clause(&mut self) -> Option<ForClause> {
        let save_pos = self.pos;
        let save_errors = self.errors.len();
        let parsed = self.parse_for_generator_clause();
        if parsed.is_some() {
            return parsed;
        }
        self.pos = save_pos;
        self.errors.truncate(save_errors);
        None
    }

    fn parse_for_generator_clause(&mut self) -> Option<ForClause> {
        let pattern = self.pattern()?;
        self.skip_newlines();
        if !self.check(&TokenKind::In) {
            self.error_at_current("expected `in` in for generator clause");
            return None;
        }
        self.advance(); // consume `in`
        self.skip_newlines();
        let source = self.expression()?;
        Some(ForClause::Generator {
            pattern,
            source: Box::new(source),
        })
    }

    fn case_arm(&mut self) -> Option<CaseArm> {
        let pattern = self.pattern()?;
        let guard = if self.match_token(&TokenKind::When) {
            Some(Box::new(self.expression()?))
        } else {
            None
        };
        self.expect(&TokenKind::Arrow, "expected '->' after pattern")?;
        self.skip_newlines();
        let body = if self.check(&TokenKind::Indent) {
            self.parse_block_expr("expected case arm body block or expression")?
        } else {
            self.expression()?
        };
        Some(CaseArm {
            pattern,
            guard,
            body,
        })
    }

    /// Parse a pattern including as-patterns and or-patterns.
    fn pattern(&mut self) -> Option<Pattern> {
        let mut pat = self.pattern_atom()?;

        // As-pattern: pattern as name
        if self.check_ident("as") {
            self.advance();
            let name = self.expect_ident("expected variable name after 'as' in pattern")?;
            let span = pat.span.merge(name.span);
            pat = Spanned::new(
                PatternKind::As {
                    pattern: Box::new(pat),
                    name,
                },
                span,
            );
        }

        // Or-pattern: pattern | pattern | ...
        if self.check(&TokenKind::Pipe) {
            let mut alternatives = vec![pat];
            while self.match_token(&TokenKind::Pipe) {
                let mut alt = self.pattern_atom()?;
                // Allow `as` in each or-alternative
                if self.check_ident("as") {
                    self.advance();
                    let name = self.expect_ident("expected variable name after 'as' in pattern")?;
                    let span = alt.span.merge(name.span);
                    alt = Spanned::new(
                        PatternKind::As {
                            pattern: Box::new(alt),
                            name,
                        },
                        span,
                    );
                }
                alternatives.push(alt);
            }
            let span = alternatives
                .first()
                .unwrap()
                .span
                .merge(alternatives.last().unwrap().span);
            pat = Spanned::new(PatternKind::Or(alternatives), span);
        }

        Some(pat)
    }

    fn pattern_atom(&mut self) -> Option<Pattern> {
        let start = self.current_span();

        // Wildcard: _
        if let Some(TokenKind::Ident(name)) = self.peek_kind()
            && name == "_"
        {
            self.advance();
            return Some(Spanned::new(PatternKind::Wildcard, start));
        }

        // Literal patterns: int, float, string, bool
        if let Some(TokenKind::Int(n)) = self.peek_kind() {
            let n = *n;
            self.advance();
            return Some(Spanned::new(PatternKind::Lit(Lit::Int(n)), start));
        }
        if let Some(TokenKind::Float(f)) = self.peek_kind() {
            let f = *f;
            self.advance();
            return Some(Spanned::new(PatternKind::Lit(Lit::Float(f)), start));
        }
        if let Some(TokenKind::String(s)) = self.peek_kind() {
            let s = s.clone();
            self.advance();
            return Some(Spanned::new(PatternKind::Lit(Lit::String(s)), start));
        }
        if self.check(&TokenKind::True) {
            self.advance();
            return Some(Spanned::new(PatternKind::Lit(Lit::Bool(true)), start));
        }
        if self.check(&TokenKind::False) {
            self.advance();
            return Some(Spanned::new(PatternKind::Lit(Lit::Bool(false)), start));
        }

        // None keyword → Constructor("None", [])
        if self.check(&TokenKind::NoneKw) {
            self.advance();
            return Some(Spanned::new(
                PatternKind::Constructor {
                    name: "None".to_string(),
                    qualifier: None,
                    args: vec![],
                    rest: false,
                },
                start,
            ));
        }

        // Constructor or named record pattern: UpperIdent
        // Qualified constructor pattern: Type.Variant or Type.Variant(args)
        if let Some(TokenKind::UpperIdent(name)) = self.peek_kind() {
            let name = name.clone();
            self.advance();
            // Check for qualified constructor: Name.Variant
            let (name, qualifier) =
                if self.check(&TokenKind::Dot)
                    && matches!(self.peek_at(1).map(|t| &t.kind), Some(TokenKind::UpperIdent(_)))
                {
                    self.advance(); // consume '.'
                    if let Some(TokenKind::UpperIdent(variant)) = self.peek_kind() {
                        let variant = variant.clone();
                        self.advance();
                        (variant, Some(name))
                    } else {
                        unreachable!()
                    }
                } else {
                    (name, None)
                };
            // Named record pattern: Name { field, field: pat, .. }
            if self.match_token(&TokenKind::LBrace) {
                let mut fields = Vec::new();
                let mut rest = false;
                self.skip_newlines();
                if !self.check(&TokenKind::RBrace) {
                    loop {
                        self.skip_newlines();
                        if self.match_token(&TokenKind::DotDot) {
                            rest = true;
                            self.skip_newlines();
                            break;
                        }
                        let field_name =
                            self.expect_ident("expected field name in record pattern")?;
                        let pat = if self.match_token(&TokenKind::Colon) {
                            self.skip_newlines();
                            self.pattern()?
                        } else {
                            // Shorthand: Name { x } means Name { x: x }
                            Spanned::new(PatternKind::Var(field_name.node.clone()), field_name.span)
                        };
                        fields.push((field_name.node, pat));
                        self.skip_newlines();
                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                    }
                }
                self.skip_newlines();
                let end = self.current_span();
                self.expect(&TokenKind::RBrace, "expected '}' to close record pattern")?;
                return Some(Spanned::new(
                    PatternKind::Record { name, fields, rest },
                    start.merge(end),
                ));
            }
            // Constructor with args: Name(args)
            if self.match_token(&TokenKind::LParen) {
                enum RawCtorPat {
                    Plain(Pattern),
                    Named(Spanned<String>, Pattern),
                }

                let mut raw_args = Vec::new();
                let mut rest = false;
                self.skip_newlines();
                if !self.check(&TokenKind::RParen) {
                    loop {
                        self.skip_newlines();
                        if self.match_token(&TokenKind::DotDot) {
                            if rest {
                                self.error_at_current("duplicate `..` in constructor pattern");
                            }
                            rest = true;
                            self.skip_newlines();
                            if self.match_token(&TokenKind::Comma) {
                                self.error_at_current(
                                    "`..` must be the last item in a constructor pattern",
                                );
                                continue;
                            }
                            break;
                        }

                        if let (Some(TokenKind::Ident(_)), Some(TokenKind::Colon)) =
                            (self.peek_kind(), self.peek_at(1).map(|tok| &tok.kind))
                        {
                            let field_name =
                                self.expect_ident("expected field name in constructor pattern")?;
                            self.advance(); // :
                            self.skip_newlines();
                            let pat = self.pattern()?;
                            raw_args.push(RawCtorPat::Named(field_name, pat));
                        } else {
                            raw_args.push(RawCtorPat::Plain(self.pattern()?));
                        }

                        self.skip_newlines();
                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                    }
                }
                let end = self.current_span();
                self.expect(&TokenKind::RParen, "expected ')' after constructor pattern")?;

                let named_mode = rest
                    || raw_args
                        .iter()
                        .any(|arg| matches!(arg, RawCtorPat::Named(_, _)));
                let mut args = Vec::with_capacity(raw_args.len());
                for raw in raw_args {
                    match raw {
                        RawCtorPat::Named(field, pattern) => args.push(ConstructorFieldPattern {
                            name: Some(field),
                            pattern,
                        }),
                        RawCtorPat::Plain(pattern) if named_mode => {
                            if let PatternKind::Var(var_name) = &pattern.node {
                                args.push(ConstructorFieldPattern {
                                    name: Some(Spanned::new(var_name.clone(), pattern.span)),
                                    pattern,
                                });
                            } else {
                                self.error_at_current(
                                    "named constructor patterns require `field: pattern` or identifier punning",
                                );
                                args.push(ConstructorFieldPattern {
                                    name: None,
                                    pattern,
                                });
                            }
                        }
                        RawCtorPat::Plain(pattern) => args.push(ConstructorFieldPattern {
                            name: None,
                            pattern,
                        }),
                    }
                }

                return Some(Spanned::new(
                    PatternKind::Constructor {
                        name,
                        qualifier: qualifier.clone(),
                        args,
                        rest,
                    },
                    start.merge(end),
                ));
            }
            // Constructor with no args
            return Some(Spanned::new(
                PatternKind::Constructor {
                    name,
                    qualifier,
                    args: vec![],
                    rest: false,
                },
                start,
            ));
        }

        // List pattern: [], [x], [x, y], [head, ..tail]
        if self.check(&TokenKind::LBracket) {
            self.advance(); // consume [
            let mut elements = Vec::new();
            let mut rest = None;
            self.skip_newlines();
            if !self.check(&TokenKind::RBracket) {
                loop {
                    self.skip_newlines();
                    // Check for ..rest pattern
                    if self.check(&TokenKind::DotDot) {
                        self.advance(); // consume ..
                        let rest_pat = self.pattern_atom()?;
                        rest = Some(Box::new(rest_pat));
                        self.skip_newlines();
                        break;
                    }
                    let elem = self.pattern()?;
                    elements.push(elem);
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                    self.skip_newlines();
                    // Check for ..rest after comma
                    if self.check(&TokenKind::DotDot) {
                        self.advance(); // consume ..
                        let rest_pat = self.pattern_atom()?;
                        rest = Some(Box::new(rest_pat));
                        self.skip_newlines();
                        break;
                    }
                }
            }
            let end = self.current_span();
            self.expect(&TokenKind::RBracket, "expected ']' to close list pattern")?;
            return Some(Spanned::new(
                PatternKind::List { elements, rest },
                start.merge(end),
            ));
        }

        // Tuple pattern: #(p1, p2, ...)
        if self.check(&TokenKind::HashParen) {
            self.advance(); // consume #(
            let mut pats = Vec::new();
            self.skip_newlines();
            if !self.check(&TokenKind::RParen) {
                loop {
                    self.skip_newlines();
                    pats.push(self.pattern()?);
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                }
            }
            let end = self.current_span();
            self.expect(&TokenKind::RParen, "expected ')' to close tuple pattern")?;
            return Some(Spanned::new(PatternKind::Tuple(pats), start.merge(end)));
        }

        // Anonymous record pattern: #{ name, age } or #{ name: pat, .. }
        if self.check(&TokenKind::HashBrace) {
            self.advance(); // consume #{
            let mut fields = Vec::new();
            let mut rest = false;
            self.skip_newlines();
            if !self.check(&TokenKind::RBrace) {
                loop {
                    self.skip_newlines();
                    if self.match_token(&TokenKind::DotDot) {
                        rest = true;
                        self.skip_newlines();
                        break;
                    }
                    let field_name = self.expect_ident("expected field name in record pattern")?;
                    let pat = if self.match_token(&TokenKind::Colon) {
                        self.skip_newlines();
                        self.pattern()?
                    } else {
                        // Shorthand: #{ name } means #{ name: name }
                        Spanned::new(PatternKind::Var(field_name.node.clone()), field_name.span)
                    };
                    fields.push((field_name.node, pat));
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                }
            }
            self.skip_newlines();
            let end = self.current_span();
            self.expect(&TokenKind::RBrace, "expected '}' to close record pattern")?;
            return Some(Spanned::new(
                PatternKind::AnonRecord { fields, rest },
                start.merge(end),
            ));
        }

        // Variable pattern: lowercase ident
        if let Some(TokenKind::Ident(name)) = self.peek_kind() {
            let name = name.clone();
            self.advance();
            return Some(Spanned::new(PatternKind::Var(name), start));
        }

        // Unit pattern: ()
        if self.check(&TokenKind::LParen) {
            self.advance();
            if self.match_token(&TokenKind::RParen) {
                let end = self.current_span();
                return Some(Spanned::new(PatternKind::Lit(Lit::Unit), start.merge(end)));
            }
            self.error_at_current("expected ')' for unit pattern");
            return None;
        }

        self.error_at_current("expected pattern");
        None
    }

    /// Parse bare single-param lambda: `x -> expr`
    fn lambda_bare(&mut self, name: String, start: Span) -> Option<Expr> {
        self.advance(); // consume ident
        self.expect(&TokenKind::Arrow, "expected '->' in lambda")?;
        self.skip_newlines();
        let body = self.lambda_body()?;
        let pattern = Spanned::new(PatternKind::Var(name), start);
        let span = start.merge(body.span);
        Some(Spanned::new(
            ExprKind::Lambda {
                params: vec![Param {
                    label: ParamLabel::Implicit,
                    pattern,
                    annotation: None,
                    default: None,
                }],
                body: Box::new(body),
                return_annotation: None,
            },
            span,
        ))
    }

    /// Parse parenthesized lambda: `() -> expr` or `(params) -> expr`
    fn lambda_paren(&mut self, start: Span) -> Option<Expr> {
        self.advance(); // consume (
        self.skip_newlines();

        let mut params = Vec::new();
        if !self.check(&TokenKind::RParen) {
            loop {
                self.skip_newlines();
                let pattern = self.pattern()?;
                let annotation = if self.match_token(&TokenKind::Colon) {
                    Some(self.type_annotation()?)
                } else {
                    None
                };
                params.push(Param {
                    label: ParamLabel::Implicit,
                    pattern,
                    annotation,
                    default: None,
                });
                self.skip_newlines();
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
        }
        self.skip_newlines();
        self.expect(&TokenKind::RParen, "expected ')' after lambda params")?;
        self.expect(&TokenKind::Arrow, "expected '->' after lambda params")?;
        self.skip_newlines();
        let body = self.lambda_body()?;

        let span = start.merge(body.span);
        Some(Spanned::new(
            ExprKind::Lambda {
                params,
                body: Box::new(body),
                return_annotation: None,
            },
            span,
        ))
    }

    /// Parse a lambda body: either a block `{ ... }` or a single expression.
    fn lambda_body(&mut self) -> Option<Expr> {
        if self.check(&TokenKind::Indent) {
            self.parse_block_expr("expected lambda body block")
        } else {
            self.expression()
        }
    }

    fn tuple_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume #(
        let elems = self.expr_list(&TokenKind::RParen)?;
        let end = self.current_span();
        self.expect(&TokenKind::RParen, "expected ')' to close tuple")?;
        Some(Spanned::new(ExprKind::Tuple(elems), start.merge(end)))
    }

    fn anon_record_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume #{
        let mut fields = Vec::new();
        let mut spread = None;
        self.skip_newlines();
        if !self.check(&TokenKind::RBrace) {
            loop {
                self.skip_newlines();
                // Check for spread: ..expr
                if self.match_token(&TokenKind::DotDot) {
                    self.skip_newlines();
                    spread = Some(Box::new(self.expression()?));
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                    self.skip_newlines();
                    continue;
                }
                let field_name = self.expect_ident("expected field name")?;
                self.expect(&TokenKind::Colon, "expected ':' after field name")?;
                self.skip_newlines();
                let value = self.expression()?;
                fields.push((field_name, value));
                self.skip_newlines();
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
        }
        self.skip_newlines();
        let end = self.current_span();
        self.expect(&TokenKind::RBrace, "expected '}' to close record")?;
        Some(Spanned::new(
            ExprKind::AnonRecord { fields, spread },
            start.merge(end),
        ))
    }

    /// Parse `spawn <expr>` or `spawn <expr> with { key: val, ... }`.
    fn spawn_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume `spawn`
        let value = self.expression()?;
        let mut end = value.span;

        // Optionally parse `with { ... }` config block
        let config = if self.check_ident("with") {
            self.advance(); // consume `with`
            let delimiter = self.expect_block_start("expected config block after `with`")?;
            let config = self.parse_spawn_config(delimiter)?;
            end = self.current_span();
            self.expect_block_end(delimiter, "expected end of spawn config")?;
            Some(Box::new(config))
        } else {
            None
        };

        Some(Spanned::new(
            ExprKind::Spawn {
                value: Box::new(value),
                config,
            },
            start.merge(end),
        ))
    }

    /// Parse `stream { ... }` or `stream { ... } with { buffer: N }`.
    fn stream_block_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume `stream`
        let body = self.parse_block_expr("expected block after `stream`")?;
        let mut end = body.span;
        let mut buffer_size = 32usize;

        if self.check_ident("with") {
            self.advance(); // consume `with`
            let delimiter = self.expect_block_start("expected config block after `with`")?;
            buffer_size = self.parse_stream_config(delimiter)?;
            end = self.current_span();
            self.expect_block_end(delimiter, "expected end of stream config")?;
        }

        Some(Spanned::new(
            ExprKind::StreamBlock {
                body: Box::new(body),
                buffer_size,
            },
            start.merge(end),
        ))
    }

    /// Parse stream config inside `stream { ... } with { ... }`.
    /// Currently only supports `buffer: <int>`.
    fn parse_stream_config(&mut self, delimiter: BlockDelimiter) -> Option<usize> {
        let mut buffer_size: Option<usize> = None;
        self.skip_newlines();
        while !self.at_block_end(delimiter) && !self.at_eof() {
            let key_tok = self.advance();
            let key = match &key_tok.kind {
                TokenKind::Ident(s) => s.clone(),
                _ => {
                    self.error_at_current("expected stream config key (`buffer`)");
                    return None;
                }
            };
            self.expect(&TokenKind::Colon, "expected `:` after config key")?;

            match key.as_str() {
                "buffer" => match self.peek_kind() {
                    Some(TokenKind::Int(n)) if *n > 0 => {
                        buffer_size = Some(*n as usize);
                        self.advance();
                    }
                    _ => {
                        self.error_at_current("stream `buffer` must be a positive integer literal");
                        return None;
                    }
                },
                _ => {
                    self.errors.push(Diagnostic::error(
                        Category::Syntax,
                        format!("unknown stream config key `{key}` (expected: buffer)"),
                    ));
                    return None;
                }
            }

            let _ = self.match_token(&TokenKind::Comma);
            self.skip_newlines();
        }
        Some(buffer_size.unwrap_or(32))
    }

    fn yield_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume `yield`
        let value = self.expression()?;
        let span = start.merge(value.span);
        Some(Spanned::new(
            ExprKind::Yield {
                value: Box::new(value),
            },
            span,
        ))
    }

    fn yield_from_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume `yield_from`
        let source = self.expression()?;
        let span = start.merge(source.span);
        Some(Spanned::new(
            ExprKind::YieldFrom {
                source: Box::new(source),
            },
            span,
        ))
    }

    /// Parse the key-value pairs inside `spawn ... with { ... }`.
    /// Allowed keys: mailbox_size, supervision, max_restarts, call_timeout.
    fn parse_spawn_config(&mut self, delimiter: BlockDelimiter) -> Option<SpawnConfig> {
        let mut config = SpawnConfig {
            mailbox_size: None,
            supervision: None,
            max_restarts: None,
            call_timeout: None,
        };

        self.skip_newlines();
        while !self.at_block_end(delimiter) && !self.at_eof() {
            let key_tok = self.advance();
            let key = match &key_tok.kind {
                TokenKind::Ident(s) => s.clone(),
                _ => {
                    self.error_at_current(
                        "expected config key (mailbox_size, supervision, max_restarts, call_timeout)",
                    );
                    return None;
                }
            };
            self.expect(&TokenKind::Colon, "expected `:` after config key")?;
            let val = self.expression()?;
            match key.as_str() {
                "mailbox_size" => config.mailbox_size = Some(val),
                "supervision" => config.supervision = Some(val),
                "max_restarts" => config.max_restarts = Some(val),
                "call_timeout" => config.call_timeout = Some(val),
                "supervisor" => {
                    self.errors.push(Diagnostic::error(
                        Category::Syntax,
                        "spawn config key `supervisor` removed — use Kea.Supervisor for supervision trees".to_string(),
                    ));
                    return None;
                }
                _ => {
                    self.errors.push(Diagnostic::error(
                        Category::Syntax,
                        format!("unknown spawn config key `{key}` (expected: mailbox_size, supervision, max_restarts, call_timeout)"),
                    ));
                    return None;
                }
            }
            let _ = self.match_token(&TokenKind::Comma);
            self.skip_newlines();
        }
        Some(config)
    }

    /// Parse actor send/call (and legacy try_send alias).
    ///
    /// Supports:
    /// - Legacy method form: `send(actor, :method, args...)`
    /// - Message form: `send(actor, Message)` / `send?(actor, Message)` /
    ///   `call(actor, Message)` / `call?(actor, Message)` /
    ///   `try_send(actor, Message)` (legacy alias for `send?`)
    fn actor_send_or_call(&mut self) -> Option<Expr> {
        let start = self.current_span();
        let name_tok = self.advance(); // consume send/call/try_send
        let safe_suffix = self.match_token(&TokenKind::Question);
        let (is_send, safe_send, safe_call) = match &name_tok.kind {
            TokenKind::Ident(s) if s == "send" => (true, safe_suffix, false),
            TokenKind::Ident(s) if s == "try_send" => (true, true, false),
            TokenKind::Ident(s) if s == "call" => (false, false, safe_suffix),
            _ => unreachable!(),
        };
        self.expect(&TokenKind::LParen, "expected '(' after send/call/try_send")?;
        self.skip_newlines();

        // First arg: actor expression
        let actor = self.expression()?;
        self.skip_newlines();
        self.expect(&TokenKind::Comma, "expected ',' after actor expression")?;
        self.skip_newlines();

        // Legacy method form when second arg is an atom.
        let (method, args) = if self.check(&TokenKind::Colon) {
            let method = self.expect_atom("expected :method atom")?;
            self.skip_newlines();

            let mut args = Vec::new();
            while self.match_token(&TokenKind::Comma) {
                self.skip_newlines();
                if self.check(&TokenKind::RParen) {
                    break; // trailing comma
                }
                args.push(self.expression()?);
                self.skip_newlines();
            }
            (method, args)
        } else {
            // Message form desugars to handle(message).
            let message = self.expression()?;
            let method = Spanned::new("handle".to_string(), message.span);
            self.skip_newlines();
            if self.match_token(&TokenKind::Comma) {
                self.skip_newlines();
                if !self.check(&TokenKind::RParen) {
                    self.errors.push(Diagnostic::error(
                        Category::Syntax,
                            "message-style send/call/try_send takes exactly two arguments: actor and message".to_string(),
                    ));
                    return None;
                }
            }
            (method, vec![message])
        };

        let end = self.current_span();
        self.expect(
            &TokenKind::RParen,
            "expected ')' to close send/call/try_send",
        )?;

        let kind = if is_send {
            ExprKind::ActorSend {
                actor: Box::new(actor),
                method,
                args,
                safe: safe_send,
            }
        } else {
            ExprKind::ActorCall {
                actor: Box::new(actor),
                method,
                args,
                safe: safe_call,
            }
        };
        Some(Spanned::new(kind, start.merge(end)))
    }

    fn await_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // await
        let safe = self.match_token(&TokenKind::Question);
        self.skip_newlines();
        let expr = self.expression()?;
        let end = expr.span;
        Some(Spanned::new(
            ExprKind::Await {
                expr: Box::new(expr),
                safe,
            },
            start.merge(end),
        ))
    }

    fn assert_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        let tok = self.advance();
        let (func_name, min_args, max_args) = match tok.kind {
            TokenKind::Assert => ("assert", 1usize, 1usize),
            TokenKind::AssertEq => ("assert_eq", 2usize, 2usize),
            TokenKind::AssertNe => ("assert_ne", 2usize, 2usize),
            TokenKind::AssertFrameEqual => ("assert_frame_equal", 2usize, 2usize),
            TokenKind::AssertSnapshot => ("assert_snapshot", 1usize, 1usize),
            TokenKind::AssertOk => ("assert_ok", 1usize, 1usize),
            TokenKind::AssertError => ("assert_error", 1usize, 1usize),
            _ => unreachable!(),
        };

        let mut args = Vec::new();
        loop {
            self.skip_newlines();
            if self.check_newline()
                || self.check(&TokenKind::RBrace)
                || self.check(&TokenKind::Dedent)
                || self.at_eof()
            {
                break;
            }
            args.push(Argument {
                label: None,
                value: self.expression()?,
            });
            self.skip_newlines();
            if !self.match_token(&TokenKind::Comma) {
                break;
            }
        }

        if args.len() < min_args || args.len() > max_args {
            self.error_at_current(&format!("`{func_name}` expects {min_args} argument(s)"));
            return None;
        }

        let end = args.last().map(|a| a.value.span).unwrap_or(start);
        Some(Spanned::new(
            ExprKind::Call {
                func: Box::new(Spanned::new(ExprKind::Var(func_name.to_string()), start)),
                args,
            },
            start.merge(end),
        ))
    }

    /// Parse `control_send(actor, signal)`.
    fn control_send(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume `control_send`
        self.expect(&TokenKind::LParen, "expected '(' after control_send")?;
        self.skip_newlines();

        let actor = self.expression()?;
        self.skip_newlines();
        self.expect(&TokenKind::Comma, "expected ',' after actor expression")?;
        self.skip_newlines();

        let signal = self.expression()?;
        self.skip_newlines();

        let end = self.current_span();
        self.expect(&TokenKind::RParen, "expected ')' to close control_send")?;

        Some(Spanned::new(
            ExprKind::ControlSend {
                actor: Box::new(actor),
                signal: Box::new(signal),
            },
            start.merge(end),
        ))
    }

    fn named_record_expr(&mut self, name: Spanned<String>, start: Span) -> Option<Expr> {
        self.advance(); // consume {
        let mut fields = Vec::new();
        let mut spread = None;
        self.skip_newlines();
        if !self.check(&TokenKind::RBrace) {
            loop {
                self.skip_newlines();
                // Check for spread: ..expr
                if self.match_token(&TokenKind::DotDot) {
                    self.skip_newlines();
                    spread = Some(Box::new(self.expression()?));
                    self.skip_newlines();
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                    self.skip_newlines();
                    continue;
                }
                let field_name = self.expect_ident("expected field name")?;
                self.expect(&TokenKind::Colon, "expected ':' after field name")?;
                self.skip_newlines();
                let value = self.expression()?;
                fields.push((field_name, value));
                self.skip_newlines();
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
        }
        self.skip_newlines();
        let end = self.current_span();
        self.expect(&TokenKind::RBrace, "expected '}' to close record")?;
        Some(Spanned::new(
            ExprKind::Record {
                name,
                fields,
                spread,
            },
            start.merge(end),
        ))
    }

    fn list_expr(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume [
        let elems = self.expr_list(&TokenKind::RBracket)?;
        let end = self.current_span();
        self.expect(&TokenKind::RBracket, "expected ']' to close list")?;
        Some(Spanned::new(ExprKind::List(elems), start.merge(end)))
    }

    fn map_literal(&mut self) -> Option<Expr> {
        let start = self.current_span();
        self.advance(); // consume %{
        let mut pairs = Vec::new();
        self.skip_newlines();
        if !self.check(&TokenKind::RBrace) {
            loop {
                self.skip_newlines();
                let key = self.expression()?;
                self.expect(&TokenKind::FatArrow, "expected '=>' in map literal")?;
                let value = self.expression()?;
                pairs.push((key, value));
                self.skip_newlines();
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
        }
        self.skip_newlines();
        let end = self.current_span();
        self.expect(&TokenKind::RBrace, "expected '}' to close map literal")?;
        Some(Spanned::new(ExprKind::MapLiteral(pairs), start.merge(end)))
    }

    fn expr_list(&mut self, close: &TokenKind) -> Option<Vec<Expr>> {
        let mut exprs = Vec::new();
        self.skip_newlines();
        if self.check(close) {
            return Some(exprs);
        }
        loop {
            self.skip_newlines();
            // Allow trailing commas in expression lists:
            // f(1, 2,), [1, 2,], Some(x,), #(1, 2,)
            if self.check(close) {
                break;
            }
            exprs.push(self.expression()?);
            self.skip_newlines();
            if !self.match_token(&TokenKind::Comma) {
                break;
            }
        }
        self.skip_newlines();
        Some(exprs)
    }

    fn expect_block_start(&mut self, expected_msg: &str) -> Option<BlockDelimiter> {
        self.skip_newlines();
        if self.match_token(&TokenKind::Indent) {
            Some(BlockDelimiter::Indent)
        } else {
            self.error_at_current(expected_msg);
            None
        }
    }

    fn at_block_end(&self, delimiter: BlockDelimiter) -> bool {
        match delimiter {
            BlockDelimiter::Indent => self.check(&TokenKind::Dedent),
        }
    }

    fn expect_block_end(&mut self, delimiter: BlockDelimiter, expected_msg: &str) -> Option<()> {
        match delimiter {
            BlockDelimiter::Indent => {
                self.expect(&TokenKind::Dedent, expected_msg)?;
            }
        }
        Some(())
    }

    fn parse_block_expr(&mut self, expected_msg: &str) -> Option<Expr> {
        let delimiter = self.expect_block_start(expected_msg)?;
        self.block_body(delimiter)
    }

    fn block_body(&mut self, delimiter: BlockDelimiter) -> Option<Expr> {
        let start = self.current_span();
        let mut exprs = Vec::new();
        self.skip_newlines();

        while !self.at_block_end(delimiter) && !self.at_eof() {
            let expr = self.expression()?;
            exprs.push(expr);
            // Expressions inside blocks are newline-delimited.
            self.skip_newlines();
        }

        let end = self.current_span();
        self.expect_block_end(delimiter, "expected end of block")?;

        let span = start.merge(end);
        match exprs.len() {
            0 => Some(Spanned::new(ExprKind::Lit(Lit::Unit), span)),
            1 => Some(exprs.into_iter().next().unwrap()),
            _ => Some(Spanned::new(ExprKind::Block(exprs), span)),
        }
    }

    // -- Postfix operations --

    fn parse_postfix(&mut self, lhs: Expr) -> Option<Expr> {
        if self.check(&TokenKind::Dot) {
            self.advance();
            let member = self.expect_any_ident("expected field name after '.'")?;
            let receiver = match lhs.node {
                // Allow namespaced module-style access like `List.map` even though
                // bare `List` parses as a nullary constructor elsewhere.
                ExprKind::Constructor { name, args } if args.is_empty() => {
                    Spanned::new(ExprKind::Var(name.node), lhs.span)
                }
                _ => lhs,
            };

            let span = receiver.span.merge(member.span);
            return Some(Spanned::new(
                ExprKind::FieldAccess {
                    expr: Box::new(receiver),
                    field: member,
                },
                span,
            ));
        }
        if self.check(&TokenKind::LParen) {
            let lhs_span = lhs.span;
            self.advance();
            let args = self.call_arg_list()?;
            let end = self.current_span();
            self.expect(&TokenKind::RParen, "expected ')' after arguments")?;
            return Some(Spanned::new(
                ExprKind::Call {
                    func: Box::new(lhs),
                    args,
                },
                lhs_span.merge(end),
            ));
        }
        if self.check_ident("as") {
            self.advance();
            self.skip_newlines();
            let annotation = self.type_annotation()?;
            let span = lhs.span.merge(annotation.span);
            return Some(Spanned::new(
                ExprKind::As {
                    expr: Box::new(lhs),
                    annotation,
                },
                span,
            ));
        }
        // Should not reach here if postfix_bp returned Some
        unreachable!()
    }

    // -- Binding power tables --

    fn infix_bp(&self) -> Option<(u8, u8)> {
        match self.peek_kind()? {
            TokenKind::When => Some((2, 3)),
            TokenKind::Or => Some((3, 4)),
            TokenKind::And => Some((5, 6)),
            // `in` and `not in` — compound `not in` detected via peek_at(1)
            TokenKind::In => Some((7, 8)),
            TokenKind::Not if self.peek_at(1).is_some_and(|t| t.kind == TokenKind::In) => {
                Some((7, 8))
            }
            TokenKind::EqEq | TokenKind::BangEq => Some((9, 10)),
            TokenKind::Lt | TokenKind::LtEq | TokenKind::Gt | TokenKind::GtEq => Some((11, 12)),
            TokenKind::DotDot | TokenKind::DotDotEq => Some((12, 13)),
            TokenKind::Plus
            | TokenKind::PlusPlus
            | TokenKind::DiamondOp
            | TokenKind::Minus => Some((13, 14)),
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent => Some((15, 16)),
            _ => None,
        }
    }

    fn postfix_bp(&self) -> Option<u8> {
        match self.peek_kind()? {
            TokenKind::Dot | TokenKind::LParen => Some(19),
            TokenKind::Ident(s) if s == "as" => Some(2),
            _ => None,
        }
    }

    // -- Lambda detection --

    /// Lookahead to detect `( ... ) ->` lambda syntax (including `() ->`).
    ///
    /// Heuristic: starting at `(`, check if the content looks like a param list
    /// rather than a parenthesized expression. Signals:
    /// - `() ->` — zero-arg lambda
    /// - `( ident , ` — multiple params
    /// - `( ident : ` — annotated param
    /// - `( ident ) ->` — single-param lambda
    /// - `( #( ` or `( #{ ` — destructuring param
    /// - `( _ ` — wildcard param
    fn is_paren_lambda_start(&self) -> bool {
        let mut i = self.pos + 1; // past the opening (

        // Skip newlines
        while self
            .tokens
            .get(i)
            .is_some_and(|t| t.kind == TokenKind::Newline)
        {
            i += 1;
        }

        // `() ->` — zero-arg lambda
        if self
            .tokens
            .get(i)
            .is_some_and(|t| t.kind == TokenKind::RParen)
        {
            return self
                .tokens
                .get(i + 1)
                .is_some_and(|t| t.kind == TokenKind::Arrow);
        }

        // Destructuring patterns: `( #( ...` or `( #{ ...`
        if self
            .tokens
            .get(i)
            .is_some_and(|t| matches!(t.kind, TokenKind::HashParen | TokenKind::HashBrace))
        {
            return true;
        }

        // Wildcard `( _ ,` or `( _ )` or `( _ :`
        if let Some(TokenKind::Ident(name)) = self.tokens.get(i).map(|t| &t.kind)
            && name == "_"
        {
            return true;
        }

        // `( ident ...` — check what follows the ident
        if let Some(TokenKind::Ident(_) | TokenKind::UpperIdent(_)) =
            self.tokens.get(i).map(|t| &t.kind)
        {
            i += 1;
            // Skip newlines
            while self
                .tokens
                .get(i)
                .is_some_and(|t| t.kind == TokenKind::Newline)
            {
                i += 1;
            }
            match self.tokens.get(i).map(|t| &t.kind) {
                // `( ident ,` — multiple params
                Some(TokenKind::Comma) => return true,
                // `( ident :` — type annotation
                Some(TokenKind::Colon) => return true,
                // `( ident ) ->` — single-param lambda
                Some(TokenKind::RParen) => {
                    return self
                        .tokens
                        .get(i + 1)
                        .is_some_and(|t| t.kind == TokenKind::Arrow);
                }
                _ => {}
            }
        }

        false
    }

    // -- Token stream helpers --

    fn peek_kind(&self) -> Option<&TokenKind> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    /// Peek at a token relative to the current position.
    fn peek_at(&self, offset: usize) -> Option<&Token> {
        self.tokens.get(self.pos + offset)
    }

    /// Check whether the next token (at pos+1) satisfies a predicate.
    fn peek_is(&self, pred: impl FnOnce(&TokenKind) -> bool) -> bool {
        self.tokens.get(self.pos + 1).is_some_and(|t| pred(&t.kind))
    }

    fn current_span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|t| t.span)
            .unwrap_or(Span::new(self.file, 0, 0))
    }

    fn at_eof(&self) -> bool {
        matches!(self.peek_kind(), Some(TokenKind::Eof) | None)
    }

    /// Look-ahead to decide if `{` starts a named record literal or case body.
    /// Called when `restrict_struct_literals` is true and we've seen `UpperIdent` at current pos
    /// with `{` at `self.pos`. Returns true if content looks like record fields.
    fn looks_like_record_after_brace(&self) -> bool {
        let t1 = self.tokens.get(self.pos + 1).map(|t| &t.kind);
        let t2 = self.tokens.get(self.pos + 2).map(|t| &t.kind);
        match (t1, t2) {
            // `{ }` — empty record
            (Some(TokenKind::RBrace), _) => true,
            // `{ .. }` — spread
            (Some(TokenKind::DotDot), _) => true,
            // `{ ident: ... }` — explicit field assignment
            (Some(TokenKind::Ident(_)), Some(TokenKind::Colon)) => true,
            // `{ ident, ... }` or `{ ident }` — shorthand field
            (Some(TokenKind::Ident(name)), Some(TokenKind::Comma | TokenKind::RBrace))
                if name != "_" =>
            {
                true
            }
            // Otherwise: case arms (e.g. `{ Red -> ...`, `{ _ -> ...`, `{ x -> ...`)
            _ => false,
        }
    }

    fn check(&self, kind: &TokenKind) -> bool {
        self.peek_kind()
            .is_some_and(|k| std::mem::discriminant(k) == std::mem::discriminant(kind))
    }

    fn check_newline(&self) -> bool {
        matches!(self.peek_kind(), Some(TokenKind::Newline))
    }

    /// Check if the next token is a specific identifier (not a keyword).
    fn check_ident(&self, name: &str) -> bool {
        matches!(self.peek_kind(), Some(TokenKind::Ident(s)) if s == name)
    }

    fn match_token(&mut self, kind: &TokenKind) -> bool {
        if self.check(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn advance(&mut self) -> Token {
        let tok = self.tokens[self.pos].clone();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        tok
    }

    fn skip_newlines(&mut self) {
        while self.check_newline() {
            self.pos += 1;
        }
    }

    /// Consume a leading `--|` doc-comment block and return normalized text.
    fn consume_doc_comment_block(&mut self) -> Option<String> {
        let mut lines = Vec::new();
        while let Some(TokenKind::DocComment(line)) = self.peek_kind() {
            lines.push(line.clone());
            self.advance();
            self.skip_newlines();
        }
        if lines.is_empty() {
            None
        } else {
            Some(lines.join("\n"))
        }
    }

    /// Skip newlines only when the next non-newline token would continue the expression
    /// (i.e., it's an infix or postfix operator).
    fn skip_newlines_if_continuation(&mut self) {
        let saved = self.pos;
        self.skip_newlines();
        // If the next token isn't an infix/postfix operator, restore position
        if self.infix_bp().is_none() && self.postfix_bp().is_none() {
            self.pos = saved;
        }
    }

    fn expect(&mut self, kind: &TokenKind, msg: &str) -> Option<Token> {
        if self.check(kind) {
            Some(self.advance())
        } else {
            self.error_at_current(msg);
            None
        }
    }

    fn expect_ident(&mut self, msg: &str) -> Option<Spanned<String>> {
        if let Some(TokenKind::Ident(name)) = self.peek_kind() {
            let name = name.clone();
            let tok = self.advance();
            Some(Spanned::new(name, tok.span))
        } else {
            self.error_at_current(msg);
            None
        }
    }

    /// Accept either a lowercase Ident or an UpperIdent.
    /// Used in field access position where the "field" may be a qualified
    /// constructor name (e.g. `SumType.Variant`).
    fn expect_any_ident(&mut self, msg: &str) -> Option<Spanned<String>> {
        match self.peek_kind() {
            Some(TokenKind::Ident(name)) | Some(TokenKind::UpperIdent(name)) => {
                let name = name.clone();
                let tok = self.advance();
                Some(Spanned::new(name, tok.span))
            }
            _ => {
                self.error_at_current(msg);
                None
            }
        }
    }

    fn expect_upper_ident(&mut self, msg: &str) -> Option<Spanned<String>> {
        if let Some(TokenKind::UpperIdent(name)) = self.peek_kind() {
            let name = name.clone();
            let tok = self.advance();
            Some(Spanned::new(name, tok.span))
        } else {
            self.error_at_current(msg);
            None
        }
    }

    fn try_ident(&mut self) -> Option<Spanned<String>> {
        if let Some(TokenKind::Ident(name)) = self.peek_kind() {
            let name = name.clone();
            let tok = self.advance();
            Some(Spanned::new(name, tok.span))
        } else {
            None
        }
    }

    fn try_upper_ident(&mut self) -> Option<Spanned<String>> {
        if let Some(TokenKind::UpperIdent(name)) = self.peek_kind() {
            let name = name.clone();
            let tok = self.advance();
            Some(Spanned::new(name, tok.span))
        } else {
            None
        }
    }

    fn expect_type_param_name(&mut self, msg: &str) -> Option<Spanned<String>> {
        match self.peek_kind() {
            Some(TokenKind::Ident(name)) => {
                let name = name.clone();
                let tok = self.advance();
                Some(Spanned::new(name, tok.span))
            }
            Some(TokenKind::UpperIdent(name)) => {
                let name = name.clone();
                let tok = self.advance();
                Some(Spanned::new(name, tok.span))
            }
            _ => {
                self.error_at_current(msg);
                None
            }
        }
    }

    fn error_at_current(&mut self, msg: &str) {
        let span = self.current_span();
        self.errors
            .push(Diagnostic::error(Category::Syntax, msg).at(SourceLocation {
                file_id: self.file.0,
                start: span.start,
                end: span.end,
            }));
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn token_to_binop(kind: &TokenKind) -> Option<BinOp> {
    match kind {
        TokenKind::Plus => Some(BinOp::Add),
        TokenKind::PlusPlus => Some(BinOp::Concat),
        TokenKind::Minus => Some(BinOp::Sub),
        TokenKind::Star => Some(BinOp::Mul),
        TokenKind::Slash => Some(BinOp::Div),
        TokenKind::Percent => Some(BinOp::Mod),
        TokenKind::DiamondOp => Some(BinOp::Combine),
        TokenKind::EqEq => Some(BinOp::Eq),
        TokenKind::BangEq => Some(BinOp::Neq),
        TokenKind::Lt => Some(BinOp::Lt),
        TokenKind::LtEq => Some(BinOp::Lte),
        TokenKind::Gt => Some(BinOp::Gt),
        TokenKind::GtEq => Some(BinOp::Gte),
        TokenKind::And => Some(BinOp::And),
        TokenKind::Or => Some(BinOp::Or),
        TokenKind::In => Some(BinOp::In),
        // NotIn is handled in the pratt loop (two-token compound)
        _ => None,
    }
}

fn split_for_generator_when_guard(clause: ForClause) -> (ForClause, Option<Expr>) {
    match clause {
        ForClause::Generator { pattern, source } => match source.node {
            ExprKind::WhenGuard { body, condition } => (
                ForClause::Generator {
                    pattern,
                    source: body,
                },
                Some(*condition),
            ),
            _ => (ForClause::Generator { pattern, source }, None),
        },
        other => (other, None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex_layout;

    fn parse(source: &str) -> Expr {
        let tokens = lex_layout(source, FileId(0)).expect("lex failed").0;
        parse_expr(tokens, FileId(0)).expect("parse failed")
    }

    fn parse_err(source: &str) -> Vec<Diagnostic> {
        let tokens = lex_layout(source, FileId(0)).expect("lex failed").0;
        parse_expr(tokens, FileId(0)).unwrap_err()
    }

    // -- Literals --

    #[test]
    fn parse_int() {
        let expr = parse("42");
        assert_eq!(expr.node, ExprKind::Lit(Lit::Int(42)));
    }

    #[test]
    fn parse_float() {
        let expr = parse("1.5");
        assert_eq!(expr.node, ExprKind::Lit(Lit::Float(1.5)));
    }

    #[test]
    fn parse_string() {
        let expr = parse(r#""hello""#);
        assert_eq!(expr.node, ExprKind::Lit(Lit::String("hello".into())));
    }

    #[test]
    fn parse_string_interp_multiline_expr() {
        let expr = parse("\"sum = ${1 +\n 2}\"");
        match &expr.node {
            ExprKind::StringInterp(parts) => {
                assert!(matches!(parts[0], StringInterpPart::Literal(_)));
                assert!(matches!(parts[1], StringInterpPart::Expr(_)));
            }
            other => panic!("expected StringInterp, got {other:?}"),
        }
    }

    #[test]
    fn parse_bool() {
        assert_eq!(parse("true").node, ExprKind::Lit(Lit::Bool(true)));
        assert_eq!(parse("false").node, ExprKind::Lit(Lit::Bool(false)));
    }

    #[test]
    fn parse_unit() {
        assert_eq!(parse("()").node, ExprKind::Lit(Lit::Unit));
    }

    #[test]
    fn parse_none() {
        assert_eq!(parse("None").node, ExprKind::None);
    }

    // -- Variables --

    #[test]
    fn parse_var() {
        assert_eq!(parse("foo").node, ExprKind::Var("foo".into()));
    }

    // -- Binary operators + precedence --

    #[test]
    fn parse_add() {
        let expr = parse("1 + 2");
        match &expr.node {
            ExprKind::BinaryOp { op, left, right } => {
                assert_eq!(op.node, BinOp::Add);
                assert_eq!(left.node, ExprKind::Lit(Lit::Int(1)));
                assert_eq!(right.node, ExprKind::Lit(Lit::Int(2)));
            }
            _ => panic!("expected BinaryOp, got {:?}", expr.node),
        }
    }

    #[test]
    fn precedence_mul_over_add() {
        // 1 + 2 * 3 should parse as 1 + (2 * 3)
        let expr = parse("1 + 2 * 3");
        match &expr.node {
            ExprKind::BinaryOp { op, right, .. } => {
                assert_eq!(op.node, BinOp::Add);
                match &right.node {
                    ExprKind::BinaryOp { op, .. } => assert_eq!(op.node, BinOp::Mul),
                    _ => panic!("expected nested BinaryOp"),
                }
            }
            _ => panic!("expected BinaryOp"),
        }
    }

    #[test]
    fn precedence_comparison() {
        // x == 1 + 2 should parse as x == (1 + 2)
        let expr = parse("x == 1 + 2");
        match &expr.node {
            ExprKind::BinaryOp { op, .. } => {
                assert_eq!(op.node, BinOp::Eq);
            }
            _ => panic!("expected BinaryOp"),
        }
    }

    #[test]
    fn left_associativity() {
        // 1 - 2 - 3 should parse as (1 - 2) - 3
        let expr = parse("1 - 2 - 3");
        match &expr.node {
            ExprKind::BinaryOp { op, left, right } => {
                assert_eq!(op.node, BinOp::Sub);
                assert_eq!(right.node, ExprKind::Lit(Lit::Int(3)));
                match &left.node {
                    ExprKind::BinaryOp { op, .. } => assert_eq!(op.node, BinOp::Sub),
                    _ => panic!("expected nested BinaryOp"),
                }
            }
            _ => panic!("expected BinaryOp"),
        }
    }

    #[test]
    fn parse_range_exclusive() {
        let expr = parse("1..10");
        match &expr.node {
            ExprKind::Range {
                start,
                end,
                inclusive,
            } => {
                assert_eq!(start.node, ExprKind::Lit(Lit::Int(1)));
                assert_eq!(end.node, ExprKind::Lit(Lit::Int(10)));
                assert!(!inclusive);
            }
            other => panic!("expected Range, got {other:?}"),
        }
    }

    #[test]
    fn parse_range_inclusive() {
        let expr = parse("1..=10");
        match &expr.node {
            ExprKind::Range {
                start,
                end,
                inclusive,
            } => {
                assert_eq!(start.node, ExprKind::Lit(Lit::Int(1)));
                assert_eq!(end.node, ExprKind::Lit(Lit::Int(10)));
                assert!(*inclusive);
            }
            other => panic!("expected Range, got {other:?}"),
        }
    }

    #[test]
    fn range_precedence_between_add_and_comparison() {
        let expr = parse("x in 1..n+1");
        match &expr.node {
            ExprKind::BinaryOp { op, right, .. } => {
                assert_eq!(op.node, BinOp::In);
                match &right.node {
                    ExprKind::Range { end, .. } => match &end.node {
                        ExprKind::BinaryOp { op, .. } => assert_eq!(op.node, BinOp::Add),
                        other => panic!("expected add in range end, got {other:?}"),
                    },
                    other => panic!("expected Range on rhs of in, got {other:?}"),
                }
            }
            other => panic!("expected BinaryOp, got {other:?}"),
        }
    }

    // -- Unary operators --

    #[test]
    fn parse_negate() {
        let expr = parse("-42");
        match &expr.node {
            ExprKind::UnaryOp { op, operand } => {
                assert_eq!(op.node, UnaryOp::Neg);
                assert_eq!(operand.node, ExprKind::Lit(Lit::Int(42)));
            }
            _ => panic!("expected UnaryOp"),
        }
    }

    #[test]
    fn parse_not() {
        let expr = parse("not x");
        match &expr.node {
            ExprKind::UnaryOp { op, operand } => {
                assert_eq!(op.node, UnaryOp::Not);
                assert_eq!(operand.node, ExprKind::Var("x".into()));
            }
            _ => panic!("expected UnaryOp"),
        }
    }

    // -- Postfix: calls, field access, try --

    #[test]
    fn parse_call() {
        let expr = parse("f(1, 2)");
        match &expr.node {
            ExprKind::Call { func, args } => {
                assert_eq!(func.node, ExprKind::Var("f".into()));
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Call"),
        }
    }

    #[test]
    fn parse_call_with_trailing_comma() {
        let expr = parse("f(1, 2,)");
        match &expr.node {
            ExprKind::Call { func, args } => {
                assert_eq!(func.node, ExprKind::Var("f".into()));
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Call"),
        }
    }

    #[test]
    fn parse_field_access() {
        let expr = parse("r.name");
        match &expr.node {
            ExprKind::FieldAccess { expr, field } => {
                assert_eq!(expr.node, ExprKind::Var("r".into()));
                assert_eq!(field.node, "name");
            }
            _ => panic!("expected FieldAccess"),
        }
    }

    #[test]
    fn parse_dot_call() {
        let expr = parse("r.name()");
        match &expr.node {
            ExprKind::Call { func, args } => {
                assert!(args.is_empty());
                match &func.node {
                    ExprKind::FieldAccess { expr, field } => {
                        assert_eq!(expr.node, ExprKind::Var("r".into()));
                        assert_eq!(field.node, "name");
                    }
                    other => panic!("expected FieldAccess callee, got {other:?}"),
                }
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn parse_namespaced_upper_ident_field_access() {
        let expr = parse("List.map");
        match &expr.node {
            ExprKind::FieldAccess { expr, field } => {
                assert_eq!(expr.node, ExprKind::Var("List".into()));
                assert_eq!(field.node, "map");
            }
            _ => panic!("expected FieldAccess"),
        }
    }

    #[test]
    fn parse_namespaced_upper_ident_dot_call() {
        let expr = parse("List.map(xs, f)");
        match &expr.node {
            ExprKind::Call { func, args } => {
                assert_eq!(args.len(), 2);
                match &func.node {
                    ExprKind::FieldAccess { expr, field } => {
                        assert_eq!(expr.node, ExprKind::Var("List".into()));
                        assert_eq!(field.node, "map");
                    }
                    other => panic!("expected FieldAccess callee, got {other:?}"),
                }
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn parse_try_operator_is_error() {
        let errs = parse_err("x?");
        assert!(!errs.is_empty());
    }

    #[test]
    fn chained_dot_calls_parse() {
        let expr = parse("x.foo().bar(1)");
        assert!(matches!(expr.node, ExprKind::Call { .. }));
    }

    // -- Pipe operator removal --

    #[test]
    fn parse_pipe_operator_is_error() {
        let errors = parse_err("x |> f");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("unexpected token after expression")),
            "expected pipe parse failure, got {errors:?}"
        );
    }

    #[test]
    fn parse_ascription() {
        let expr = parse("x as Int");
        match &expr.node {
            ExprKind::As {
                expr: inner,
                annotation,
            } => {
                assert_eq!(inner.node, ExprKind::Var("x".into()));
                assert_eq!(annotation.node, TypeAnnotation::Named("Int".into()));
            }
            other => panic!("expected As, got {other:?}"),
        }
    }

    #[test]
    fn ascription_binds_looser_than_add() {
        let expr = parse("1 + 2 as Int");
        match &expr.node {
            ExprKind::As { expr: inner, .. } => match &inner.node {
                ExprKind::BinaryOp { op, .. } => assert_eq!(op.node, BinOp::Add),
                other => panic!("expected BinaryOp under As, got {other:?}"),
            },
            other => panic!("expected As at top-level, got {other:?}"),
        }
    }

    #[test]
    fn ascription_with_pipe_operator_is_error() {
        let errors = parse_err("x |> f as Int");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("unexpected token after expression")),
            "expected pipe parse failure, got {errors:?}"
        );
    }

    // -- Let bindings --

    #[test]
    fn parse_let() {
        let expr = parse("let x = 42");
        match &expr.node {
            ExprKind::Let { pattern, value, .. } => {
                assert_eq!(pattern.node.as_var(), Some("x"));
                assert_eq!(value.node, ExprKind::Lit(Lit::Int(42)));
            }
            _ => panic!("expected Let"),
        }
    }

    #[test]
    fn parse_let_with_annotation() {
        let expr = parse("let x: Int = 42");
        match &expr.node {
            ExprKind::Let {
                pattern,
                annotation,
                value,
            } => {
                assert_eq!(pattern.node.as_var(), Some("x"));
                assert!(annotation.is_some());
                assert_eq!(value.node, ExprKind::Lit(Lit::Int(42)));
            }
            _ => panic!("expected Let"),
        }
    }

    // -- If/else --

    #[test]
    fn parse_if_else() {
        let expr = parse("if true\n  1\nelse\n  2");
        match &expr.node {
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                assert_eq!(condition.node, ExprKind::Lit(Lit::Bool(true)));
                assert_eq!(then_branch.node, ExprKind::Lit(Lit::Int(1)));
                assert!(else_branch.is_some());
            }
            _ => panic!("expected If"),
        }
    }

    #[test]
    fn parse_if_else_indented() {
        let expr = parse("if true\n  1\nelse\n  2");
        match &expr.node {
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                assert_eq!(condition.node, ExprKind::Lit(Lit::Bool(true)));
                assert_eq!(then_branch.node, ExprKind::Lit(Lit::Int(1)));
                assert!(matches!(
                    else_branch.as_deref().map(|e| &e.node),
                    Some(ExprKind::Lit(Lit::Int(2)))
                ));
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    #[test]
    fn parse_if_no_else() {
        let errors = parse_err("if x\n  42");
        assert!(!errors.is_empty());
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("`if` requires an `else` branch")),
            "expected missing-else error, got {errors:?}"
        );
    }

    #[test]
    fn parse_case_arm_when_guard() {
        let expr = parse("case x\n  n when n > 0 -> n\n  _ -> 0");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 2);
                assert!(
                    arms[0].guard.is_some(),
                    "expected `when` guard on first arm"
                );
                assert!(arms[1].guard.is_none(), "expected no guard on wildcard arm");
            }
            other => panic!("expected Case, got {other:?}"),
        }
    }

    #[test]
    fn parse_case_indented_arms() {
        let expr = parse("case x\n  Some(v) -> v\n  _ -> 0");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 2);
            }
            other => panic!("expected Case, got {other:?}"),
        }
    }

    #[test]
    fn parse_case_indented_arm_multiline_body() {
        let expr = parse("case x\n  Some(v) ->\n    let y = v + 1\n    y\n  _ -> 0");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 2);
                match &arms[0].body.node {
                    ExprKind::Block(exprs) => assert_eq!(exprs.len(), 2),
                    other => panic!("expected first arm block body, got {other:?}"),
                }
            }
            other => panic!("expected Case, got {other:?}"),
        }
    }

    // -- Lambda --

    #[test]
    fn parse_lambda() {
        let expr = parse("x -> x + 1");
        match &expr.node {
            ExprKind::Lambda { params, body, .. } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].name().unwrap(), "x");
                match &body.node {
                    ExprKind::BinaryOp { op, .. } => assert_eq!(op.node, BinOp::Add),
                    _ => panic!("expected BinaryOp in lambda body"),
                }
            }
            _ => panic!("expected Lambda"),
        }
    }

    #[test]
    fn parse_multi_param_lambda() {
        let expr = parse("(x, y) -> x + y");
        match &expr.node {
            ExprKind::Lambda { params, .. } => {
                assert_eq!(params.len(), 2);
                assert_eq!(params[0].name().unwrap(), "x");
                assert_eq!(params[1].name().unwrap(), "y");
            }
            _ => panic!("expected Lambda"),
        }
    }

    #[test]
    fn parse_lambda_with_existential_annotation() {
        let expr = parse("(x: any (Show, Eq) where Item = Int) -> x");
        match &expr.node {
            ExprKind::Lambda { params, .. } => {
                assert_eq!(params.len(), 1);
                let ann = params[0].annotation.as_ref().expect("annotation");
                match &ann.node {
                    TypeAnnotation::Existential {
                        bounds,
                        associated_types,
                    } => {
                        assert_eq!(bounds, &vec!["Show".to_string(), "Eq".to_string()]);
                        assert_eq!(associated_types.len(), 1);
                        assert_eq!(associated_types[0].0, "Item");
                    }
                    other => panic!("expected Existential, got {other:?}"),
                }
            }
            _ => panic!("expected Lambda"),
        }
    }

    #[test]
    fn parse_lambda_with_indented_block_body() {
        let expr = parse("x ->\n  let y = x + 1\n  y");
        match &expr.node {
            ExprKind::Lambda { body, .. } => {
                assert!(matches!(body.node, ExprKind::Block(_)));
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    // -- Tuple, list, anon record --

    #[test]
    fn parse_tuple() {
        let expr = parse("#(1, 2, 3)");
        match &expr.node {
            ExprKind::Tuple(elems) => assert_eq!(elems.len(), 3),
            _ => panic!("expected Tuple"),
        }
    }

    #[test]
    fn parse_tuple_with_trailing_comma() {
        let expr = parse("#(1, 2, 3,)");
        match &expr.node {
            ExprKind::Tuple(elems) => assert_eq!(elems.len(), 3),
            _ => panic!("expected Tuple"),
        }
    }

    #[test]
    fn parse_list() {
        let expr = parse("[1, 2, 3]");
        match &expr.node {
            ExprKind::List(elems) => assert_eq!(elems.len(), 3),
            _ => panic!("expected List"),
        }
    }

    #[test]
    fn parse_list_with_trailing_comma() {
        let expr = parse("[1, 2, 3,]");
        match &expr.node {
            ExprKind::List(elems) => assert_eq!(elems.len(), 3),
            _ => panic!("expected List"),
        }
    }

    #[test]
    fn parse_anon_record() {
        let expr = parse("#{ name: \"alice\", age: 30 }");
        match &expr.node {
            ExprKind::AnonRecord { fields, spread } => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0.node, "name");
                assert_eq!(fields[1].0.node, "age");
                assert!(spread.is_none());
            }
            _ => panic!("expected AnonRecord"),
        }
    }

    #[test]
    fn parse_anon_record_with_spread() {
        let expr = parse("#{ ..row, margin: row.rev - row.cost }");
        match &expr.node {
            ExprKind::AnonRecord { fields, spread } => {
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0.node, "margin");
                assert!(spread.is_some());
                match &spread.as_ref().unwrap().node {
                    ExprKind::Var(name) => assert_eq!(name, "row"),
                    other => panic!("expected Var for spread, got {:?}", other),
                }
            }
            _ => panic!("expected AnonRecord"),
        }
    }

    #[test]
    fn parse_anon_record_spread_only() {
        let expr = parse("#{ ..base }");
        match &expr.node {
            ExprKind::AnonRecord { fields, spread } => {
                assert_eq!(fields.len(), 0);
                assert!(spread.is_some());
            }
            _ => panic!("expected AnonRecord"),
        }
    }

    #[test]
    fn parse_anon_record_spread_before_fields() {
        let expr = parse("#{ ..base, x: 1, y: 2 }");
        match &expr.node {
            ExprKind::AnonRecord { fields, spread } => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0.node, "x");
                assert_eq!(fields[1].0.node, "y");
                assert!(spread.is_some());
            }
            _ => panic!("expected AnonRecord"),
        }
    }

    // -- Constructors --

    #[test]
    fn parse_constructor_with_args() {
        let expr = parse("Some(42)");
        match &expr.node {
            ExprKind::Constructor { name, args } => {
                assert_eq!(name.node, "Some");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("expected Constructor"),
        }
    }

    #[test]
    fn parse_constructor_with_trailing_comma() {
        let expr = parse("Some(42,)");
        match &expr.node {
            ExprKind::Constructor { name, args } => {
                assert_eq!(name.node, "Some");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("expected Constructor"),
        }
    }

    #[test]
    fn parse_constructor_no_args() {
        let expr = parse("Nil");
        match &expr.node {
            ExprKind::Constructor { name, args } => {
                assert_eq!(name.node, "Nil");
                assert_eq!(args.len(), 0);
            }
            _ => panic!("expected Constructor"),
        }
    }

    // -- Blocks --

    #[test]
    fn parse_block() {
        let errors = parse_err("{\n  let x = 1\n  x + 2\n}");
        assert!(!errors.is_empty(), "brace blocks should be rejected");
    }

    #[test]
    fn parse_single_expr_block() {
        let errors = parse_err("{ 42 }");
        assert!(!errors.is_empty(), "brace blocks should be rejected");
    }

    // -- Grouping --

    #[test]
    fn parse_grouping() {
        let expr = parse("(1 + 2) * 3");
        match &expr.node {
            ExprKind::BinaryOp { op, left, .. } => {
                assert_eq!(op.node, BinOp::Mul);
                match &left.node {
                    ExprKind::BinaryOp { op, .. } => assert_eq!(op.node, BinOp::Add),
                    _ => panic!("expected grouped add"),
                }
            }
            _ => panic!("expected BinaryOp"),
        }
    }

    // -- Record declarations --

    fn parse_mod(source: &str) -> Module {
        let tokens = lex_layout(source, FileId(0)).unwrap().0;
        parse_module(tokens, FileId(0)).unwrap()
    }

    fn parse_mod_err(source: &str) -> Vec<Diagnostic> {
        let tokens = lex_layout(source, FileId(0)).unwrap().0;
        parse_module(tokens, FileId(0)).unwrap_err()
    }

    #[test]
    fn parse_record_def() {
        let module = parse_mod("record User\n  name: String\n  age: Int");
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert!(!def.public);
                assert_eq!(def.name.node, "User");
                assert_eq!(def.fields.len(), 2);
                assert_eq!(def.fields[0].0.node, "name");
                assert_eq!(def.fields[1].0.node, "age");
            }
            _ => panic!("expected RecordDef"),
        }
    }

    #[test]
    fn parse_fn_declaration_annotations() {
        let module = parse_mod("@deprecated(\"use new_api\") fn old(x: Int) -> Int\n  x");
        match &module.declarations[0].node {
            DeclKind::Function(def) => {
                assert_eq!(def.annotations.len(), 1);
                assert_eq!(def.annotations[0].name.node, "deprecated");
                assert_eq!(def.annotations[0].args.len(), 1);
            }
            other => panic!("expected function declaration, got {other:?}"),
        }
    }

    #[test]
    fn parse_record_field_annotations() {
        let module = parse_mod(
            "record User\n  @rename(\"user_name\") name: String\n  @default(30) age: Int",
        );
        match &module.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert_eq!(def.field_annotations.len(), 2);
                assert_eq!(def.field_annotations[0].len(), 1);
                assert_eq!(def.field_annotations[0][0].name.node, "rename");
                assert_eq!(def.field_annotations[1].len(), 1);
                assert_eq!(def.field_annotations[1][0].name.node, "default");
            }
            other => panic!("expected record declaration, got {other:?}"),
        }
    }

    #[test]
    fn parse_type_and_variant_annotations() {
        let module =
            parse_mod("@tagged(style: :internal) type Message = | @rename(\"txt\") Text(String)");
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert_eq!(def.annotations.len(), 1);
                assert_eq!(def.annotations[0].name.node, "tagged");
                assert_eq!(def.variants.len(), 1);
                assert_eq!(def.variants[0].annotations.len(), 1);
                assert_eq!(def.variants[0].annotations[0].name.node, "rename");
            }
            other => panic!("expected type declaration, got {other:?}"),
        }
    }

    #[test]
    fn parse_named_variant_field_annotations() {
        let module = parse_mod(
            "type Event = | User(@rename(\"user_id\") id: Int, @default(\"anon\") name: String)",
        );
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert_eq!(def.variants.len(), 1);
                let fields = &def.variants[0].fields;
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].annotations.len(), 1);
                assert_eq!(fields[0].annotations[0].name.node, "rename");
                assert_eq!(fields[1].annotations.len(), 1);
                assert_eq!(fields[1].annotations[0].name.node, "default");
            }
            other => panic!("expected type declaration, got {other:?}"),
        }
    }

    #[test]
    fn parse_pub_record_def() {
        let module = parse_mod("pub record Point\n  x: Float\n  y: Float");
        match &module.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert!(def.public);
                assert_eq!(def.name.node, "Point");
                assert_eq!(def.fields.len(), 2);
            }
            _ => panic!("expected RecordDef"),
        }
    }

    #[test]
    fn parse_record_def_with_type_params() {
        let module = parse_mod("record Box(t)\n  value: t");
        match &module.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert_eq!(def.name.node, "Box");
                assert_eq!(def.params, vec!["t".to_string()]);
                assert_eq!(def.fields.len(), 1);
            }
            _ => panic!("expected RecordDef"),
        }
    }

    #[test]
    fn parse_alias_decl() {
        let module = parse_mod("alias UserId = Int");
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::AliasDecl(def) => {
                assert!(!def.public);
                assert_eq!(def.name.node, "UserId");
                assert!(def.params.is_empty());
                assert!(matches!(def.target.node, TypeAnnotation::Named(ref n) if n == "Int"));
            }
            _ => panic!("expected AliasDecl"),
        }
    }

    #[test]
    fn parse_effect_row_alias_decl() {
        let module = parse_mod("alias DbEffects = [IO, Fail DbError | e]");
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::AliasDecl(def) => match &def.target.node {
                TypeAnnotation::EffectRow(row) => {
                    assert_eq!(row.effects.len(), 2);
                    assert_eq!(row.effects[0].name, "IO");
                    assert_eq!(row.effects[0].payload, None);
                    assert_eq!(row.effects[1].name, "Fail");
                    assert_eq!(row.effects[1].payload.as_deref(), Some("DbError"));
                    assert_eq!(row.rest.as_deref(), Some("e"));
                }
                other => panic!("expected effect row alias target, got {other:?}"),
            },
            _ => panic!("expected AliasDecl"),
        }
    }

    #[test]
    fn parse_alias_annotations_not_supported() {
        let diags = parse_mod_err("@deprecated alias UserId = Int");
        assert!(
            diags.iter().any(|d| d
                .message
                .contains("annotations are not supported on alias declarations")),
            "expected unsupported-alias-annotation diagnostic, got: {diags:?}"
        );
    }

    #[test]
    fn parse_pub_parametric_alias_decl() {
        let module = parse_mod("pub alias Handler(t) = fn(Request) -> Result(t, AppError)");
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::AliasDecl(def) => {
                assert!(def.public);
                assert_eq!(def.name.node, "Handler");
                assert_eq!(def.params, vec!["t".to_string()]);
            }
            _ => panic!("expected AliasDecl"),
        }
    }

    #[test]
    fn parse_opaque_decl() {
        let module = parse_mod("opaque UserId = Int");
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::OpaqueTypeDef(def) => {
                assert!(!def.public);
                assert_eq!(def.name.node, "UserId");
                assert!(def.params.is_empty());
                assert!(matches!(def.target.node, TypeAnnotation::Named(ref n) if n == "Int"));
                assert!(def.derives.is_empty());
            }
            _ => panic!("expected OpaqueTypeDef"),
        }
    }

    #[test]
    fn parse_pub_parametric_opaque_with_deriving() {
        let module = parse_mod("pub opaque Boxed(t) = List(t) deriving Eq, Display");
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::OpaqueTypeDef(def) => {
                assert!(def.public);
                assert_eq!(def.name.node, "Boxed");
                assert_eq!(def.params, vec!["t".to_string()]);
                assert_eq!(def.derives.len(), 2);
                assert_eq!(def.derives[0].node, "Eq");
                assert_eq!(def.derives[1].node, "Display");
            }
            _ => panic!("expected OpaqueTypeDef"),
        }
    }

    #[test]
    fn parse_record_def_with_derive() {
        let module = parse_mod("record Point\n  x: Int\n  y: Int\nderiving Eq, Hash");
        match &module.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert_eq!(def.name.node, "Point");
                assert_eq!(def.derives.len(), 2);
                assert_eq!(def.derives[0].node, "Eq");
                assert_eq!(def.derives[1].node, "Hash");
            }
            _ => panic!("expected RecordDef"),
        }
    }

    #[test]
    fn parse_record_single_field() {
        let module = parse_mod("record Wrapper\n  value: Int");
        match &module.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert_eq!(def.fields.len(), 1);
                assert_eq!(def.fields[0].0.node, "value");
            }
            _ => panic!("expected RecordDef"),
        }
    }

    #[test]
    fn parse_record_trailing_comma() {
        let module = parse_mod("record Pair\n  a: Int,\n  b: String,");
        match &module.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert_eq!(def.fields.len(), 2);
            }
            _ => panic!("expected RecordDef"),
        }
    }

    #[test]
    fn parse_record_with_fn() {
        let module = parse_mod("record Point\n  x: Float\n  y: Float\nfn origin() -> Int\n  0");
        assert_eq!(module.declarations.len(), 2);
        assert!(matches!(
            module.declarations[0].node,
            DeclKind::RecordDef(_)
        ));
        assert!(matches!(module.declarations[1].node, DeclKind::Function(_)));
    }

    #[test]
    fn parse_record_multiline() {
        let module = parse_mod("record User\n  name: String,\n  age: Int,\n  active: Bool");
        match &module.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert_eq!(def.fields.len(), 3);
            }
            _ => panic!("expected RecordDef"),
        }
    }

    #[test]
    fn parse_record_multiline_indented() {
        let module = parse_mod("record User\n  name: String\n  age: Int\n  active: Bool");
        match &module.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert_eq!(def.fields.len(), 3);
            }
            _ => panic!("expected RecordDef"),
        }
    }

    #[test]
    fn parse_record_missing_brace() {
        let errors = parse_mod_err("record User { name: String");
        assert!(!errors.is_empty());
    }

    // -- Fn declarations --

    #[test]
    fn parse_fn_decl() {
        let source = "fn add(x, y) -> Int\n  x + y";
        let tokens = lex_layout(source, FileId(0)).unwrap().0;
        let module = parse_module(tokens, FileId(0)).unwrap();
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::Function(f) => {
                assert!(!f.public);
                assert_eq!(f.name.node, "add");
                assert!(f.doc.is_none());
                assert_eq!(f.params.len(), 2);
                assert!(f.testing.is_none());
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_decl_with_indented_body() {
        let module = parse_mod("fn add(x, y) -> Int\n  x + y");
        match &module.declarations[0].node {
            DeclKind::Function(f) => {
                assert_eq!(f.name.node, "add");
                assert_eq!(f.params.len(), 2);
                assert!(matches!(f.body.node, ExprKind::BinaryOp { .. }));
            }
            other => panic!("expected Function, got {other:?}"),
        }
    }

    #[test]
    fn parse_fn_decl_with_postfix_testing_block() {
        let module = parse_mod("fn double(x: Int) -> Int\n  x + x\ntesting\n  assert_eq double(3), 6");
        match &module.declarations[0].node {
            DeclKind::Function(f) => {
                assert!(f.testing.is_some(), "expected postfix testing block");
                assert!(f.testing_tags.is_empty());
            }
            other => panic!("expected Function, got {other:?}"),
        }
    }

    #[test]
    fn parse_fn_decl_with_postfix_testing_tags() {
        let module = parse_mod(
            "fn double(x: Int) -> Int\n  x + x\ntesting tags [:fast, :unit]\n  assert_eq double(3), 6",
        );
        match &module.declarations[0].node {
            DeclKind::Function(f) => {
                assert_eq!(f.testing_tags.len(), 2);
                assert_eq!(f.testing_tags[0].node, "fast");
                assert_eq!(f.testing_tags[1].node, "unit");
            }
            other => panic!("expected Function, got {other:?}"),
        }
    }

    #[test]
    fn parse_fn_doc_comment() {
        let module = parse_mod("--| Adds two numbers.\nfn add(x, y) -> Int\n  x + y");
        match &module.declarations[0].node {
            DeclKind::Function(f) => {
                assert_eq!(f.name.node, "add");
                assert_eq!(f.doc.as_deref(), Some("Adds two numbers."));
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_multiline_doc_comment() {
        let module = parse_mod("--| Summary.\n--|\n--| Details.\nfn f() -> Int\n  1");
        match &module.declarations[0].node {
            DeclKind::Function(f) => {
                assert_eq!(f.doc.as_deref(), Some("Summary.\n\nDetails."));
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_doc_comments_for_type_record_trait() {
        let module = parse_mod(
            "--| T docs\ntype T = A\n--| R docs\nrecord R\n  x: Int\n--| Tr docs\ntrait Tr\n  fn m() -> Int\n    0",
        );
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => assert_eq!(def.doc.as_deref(), Some("T docs")),
            _ => panic!("expected TypeDef"),
        }
        match &module.declarations[1].node {
            DeclKind::RecordDef(def) => assert_eq!(def.doc.as_deref(), Some("R docs")),
            _ => panic!("expected RecordDef"),
        }
        match &module.declarations[2].node {
            DeclKind::TraitDef(def) => assert_eq!(def.doc.as_deref(), Some("Tr docs")),
            _ => panic!("expected TraitDef"),
        }
    }

    #[test]
    fn parse_doc_comment_before_import_reports_error() {
        let errors = parse_mod_err("--| doc\nimport Kea.IO");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("doc comments can only be attached")),
            "expected doc attachment error, got {errors:?}"
        );
    }

    #[test]
    fn parse_pub_fn() {
        let module = parse_mod("pub fn hello() -> Int\n  42");
        match &module.declarations[0].node {
            DeclKind::Function(f) => {
                assert!(f.public);
                assert_eq!(f.name.node, "hello");
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_with_return_type() {
        let module = parse_mod("fn id(x: Int) -> Int\n  x");
        match &module.declarations[0].node {
            DeclKind::Function(f) => {
                assert!(f.params[0].annotation.is_some());
                assert!(f.return_annotation.is_some());
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_with_effect_clause() {
        let module = parse_mod("fn id(x: Int) -[pure]> Int\n  x");
        match &module.declarations[0].node {
            DeclKind::Function(f) => {
                assert!(matches!(
                    f.effect_annotation.as_ref().map(|e| &e.node),
                    Some(EffectAnnotation::Pure)
                ));
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_with_effect_row_clause() {
        let module = parse_mod("fn id(x: Int) -[IO, Fail DbError | e]> Int\n  x");
        match &module.declarations[0].node {
            DeclKind::Function(f) => match f.effect_annotation.as_ref().map(|e| &e.node) {
                Some(EffectAnnotation::Row(row)) => {
                    assert_eq!(row.effects.len(), 2);
                    assert_eq!(row.effects[0].name, "IO");
                    assert_eq!(row.effects[0].payload, None);
                    assert_eq!(row.effects[1].name, "Fail");
                    assert_eq!(row.effects[1].payload.as_deref(), Some("DbError"));
                    assert_eq!(row.rest.as_deref(), Some("e"));
                }
                other => panic!("expected row effect annotation, got {other:?}"),
            },
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_with_tail_only_effect_row_clause() {
        let module = parse_mod("fn id(x: Int) -[| e]> Int\n  x");
        match &module.declarations[0].node {
            DeclKind::Function(f) => match f.effect_annotation.as_ref().map(|e| &e.node) {
                Some(EffectAnnotation::Row(row)) => {
                    assert!(row.effects.is_empty());
                    assert_eq!(row.rest.as_deref(), Some("e"));
                }
                other => panic!("expected row effect annotation, got {other:?}"),
            },
            _ => panic!("expected Function"),
        }
    }

    // -- Error cases --

    #[test]
    fn error_missing_close_paren() {
        let errors = parse_err("f(1, 2");
        assert!(!errors.is_empty());
    }

    #[test]
    fn error_unexpected_token() {
        let errors = parse_err("+ 1");
        assert!(!errors.is_empty());
    }

    // -- Newline handling --

    #[test]
    fn newline_continuation_after_operator() {
        // Binary op followed by newline should continue the expression
        let expr = parse("1 +\n  2");
        match &expr.node {
            ExprKind::BinaryOp { op, .. } => assert_eq!(op.node, BinOp::Add),
            _ => panic!("expected BinaryOp"),
        }
    }

    // -- Case expressions --

    #[test]
    fn parse_case_simple() {
        let expr = parse("case x\n  1 -> \"one\"\n  _ -> \"other\"");
        match &expr.node {
            ExprKind::Case { scrutinee, arms } => {
                assert_eq!(scrutinee.node, ExprKind::Var("x".into()));
                assert_eq!(arms.len(), 2);
                assert!(matches!(
                    arms[0].pattern.node,
                    PatternKind::Lit(Lit::Int(1))
                ));
                assert!(matches!(arms[1].pattern.node, PatternKind::Wildcard));
            }
            _ => panic!("expected Case, got {:?}", expr.node),
        }
    }

    #[test]
    fn parse_case_constructor() {
        let expr = parse("case x\n  Some(v) -> v\n  None -> 0");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 2);
                match &arms[0].pattern.node {
                    PatternKind::Constructor { name, args, .. } => {
                        assert_eq!(name, "Some");
                        assert_eq!(args.len(), 1);
                        assert!(matches!(args[0].pattern.node, PatternKind::Var(_)));
                    }
                    _ => panic!("expected Constructor pattern"),
                }
                match &arms[1].pattern.node {
                    PatternKind::Constructor { name, args, .. } => {
                        assert_eq!(name, "None");
                        assert!(args.is_empty());
                    }
                    _ => panic!("expected None constructor pattern"),
                }
            }
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn parse_case_tuple() {
        let expr = parse("case p\n  #(0, y) -> y\n  #(x, _) -> x");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 2);
                match &arms[0].pattern.node {
                    PatternKind::Tuple(pats) => {
                        assert_eq!(pats.len(), 2);
                        assert!(matches!(pats[0].node, PatternKind::Lit(Lit::Int(0))));
                        assert!(matches!(pats[1].node, PatternKind::Var(_)));
                    }
                    _ => panic!("expected Tuple pattern"),
                }
            }
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn parse_case_nested() {
        let expr = parse("case x\n  Some(#(a, b)) -> a + b\n  _ -> 0");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 2);
                match &arms[0].pattern.node {
                    PatternKind::Constructor { name, args, .. } => {
                        assert_eq!(name, "Some");
                        assert_eq!(args.len(), 1);
                        assert!(matches!(args[0].pattern.node, PatternKind::Tuple(_)));
                    }
                    _ => panic!("expected nested Constructor pattern"),
                }
            }
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn parse_case_no_arms() {
        let errors = parse_err("case x");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("expected block after case scrutinee")),
            "expected missing-case-block diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_case_wildcard() {
        let expr = parse("case x\n  _ -> 42");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 1);
                assert!(matches!(arms[0].pattern.node, PatternKind::Wildcard));
                assert_eq!(arms[0].body.node, ExprKind::Lit(Lit::Int(42)));
            }
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn parse_case_var_binding() {
        let expr = parse("case x\n  n -> n + 1");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern.node {
                    PatternKind::Var(name) => assert_eq!(name, "n"),
                    _ => panic!("expected Var pattern"),
                }
            }
            _ => panic!("expected Case"),
        }
    }

    // -- Named record expressions --

    #[test]
    fn parse_named_record_expr() {
        let expr = parse("User { name: \"alice\", age: 30 }");
        match &expr.node {
            ExprKind::Record {
                name,
                fields,
                spread,
            } => {
                assert_eq!(name.node, "User");
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0.node, "name");
                assert_eq!(fields[1].0.node, "age");
                assert!(spread.is_none());
            }
            _ => panic!("expected Record, got {:?}", expr.node),
        }
    }

    #[test]
    fn parse_named_record_with_spread() {
        let expr = parse("User { age: 31, ..base }");
        match &expr.node {
            ExprKind::Record {
                name,
                fields,
                spread,
            } => {
                assert_eq!(name.node, "User");
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0.node, "age");
                assert!(spread.is_some());
            }
            _ => panic!("expected Record, got {:?}", expr.node),
        }
    }

    #[test]
    fn parse_named_record_with_spread_first() {
        let expr = parse("User { ..base, age: 31 }");
        match &expr.node {
            ExprKind::Record {
                name,
                fields,
                spread,
            } => {
                assert_eq!(name.node, "User");
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0.node, "age");
                assert!(spread.is_some());
            }
            _ => panic!("expected Record, got {:?}", expr.node),
        }
    }

    #[test]
    fn parse_named_record_empty() {
        let expr = parse("Empty { }");
        match &expr.node {
            ExprKind::Record {
                name,
                fields,
                spread,
            } => {
                assert_eq!(name.node, "Empty");
                assert!(fields.is_empty());
                assert!(spread.is_none());
            }
            _ => panic!("expected Record, got {:?}", expr.node),
        }
    }

    // -- Named record patterns --

    #[test]
    fn parse_named_record_pattern() {
        let expr = parse("case x\n  User { name, age } -> name");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 1);
                match &arms[0].pattern.node {
                    PatternKind::Record { name, fields, rest } => {
                        assert_eq!(name, "User");
                        assert_eq!(fields.len(), 2);
                        assert_eq!(fields[0].0, "name");
                        assert_eq!(fields[1].0, "age");
                        assert!(!rest);
                    }
                    _ => panic!("expected Record pattern, got {:?}", arms[0].pattern.node),
                }
            }
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn parse_named_record_pattern_with_rest() {
        let expr = parse("case x\n  User { name, .. } -> name");
        match &expr.node {
            ExprKind::Case { arms, .. } => match &arms[0].pattern.node {
                PatternKind::Record { name, fields, rest } => {
                    assert_eq!(name, "User");
                    assert_eq!(fields.len(), 1);
                    assert!(*rest);
                }
                _ => panic!("expected Record pattern"),
            },
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn parse_named_record_pattern_with_subpattern() {
        let expr = parse("case x\n  User { name: n } -> n");
        match &expr.node {
            ExprKind::Case { arms, .. } => match &arms[0].pattern.node {
                PatternKind::Record { fields, .. } => {
                    assert_eq!(fields[0].0, "name");
                    assert!(matches!(fields[0].1.node, PatternKind::Var(ref v) if v == "n"));
                }
                _ => panic!("expected Record pattern"),
            },
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn parse_case_bool_pattern() {
        let expr = parse("case x\n  true -> 1\n  false -> 0");
        match &expr.node {
            ExprKind::Case { arms, .. } => {
                assert_eq!(arms.len(), 2);
                assert!(matches!(
                    arms[0].pattern.node,
                    PatternKind::Lit(Lit::Bool(true))
                ));
                assert!(matches!(
                    arms[1].pattern.node,
                    PatternKind::Lit(Lit::Bool(false))
                ));
            }
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn parse_cond_simple() {
        let expr = parse("cond\n  1 > 2 -> \"no\"\n  _ -> \"yes\"");
        match &expr.node {
            ExprKind::Cond { arms } => {
                assert_eq!(arms.len(), 2);
                assert!(matches!(arms[0].condition.node, ExprKind::BinaryOp { .. }));
                assert!(matches!(arms[1].condition.node, ExprKind::Wildcard));
                assert!(matches!(arms[1].body.node, ExprKind::Lit(Lit::String(_))));
            }
            _ => panic!("expected Cond"),
        }
    }

    #[test]
    fn parse_cond_simple_indented() {
        let expr = parse("cond\n  1 > 2 -> \"no\"\n  _ -> \"yes\"");
        match &expr.node {
            ExprKind::Cond { arms } => {
                assert_eq!(arms.len(), 2);
            }
            other => panic!("expected Cond, got {other:?}"),
        }
    }

    #[test]
    fn parse_cond_indented_arm_multiline_body() {
        let expr = parse("cond\n  x > 0 ->\n    let y = x\n    y\n  _ -> 0");
        match &expr.node {
            ExprKind::Cond { arms } => {
                assert_eq!(arms.len(), 2);
                match &arms[0].body.node {
                    ExprKind::Block(exprs) => assert_eq!(exprs.len(), 2),
                    other => panic!("expected first arm block body, got {other:?}"),
                }
            }
            other => panic!("expected Cond, got {other:?}"),
        }
    }

    // -- Trait parsing --

    #[test]
    fn parse_trait_empty() {
        let errors = parse_mod_err("trait Additive");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("expected trait body block after trait name")),
            "expected missing-trait-body diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_trait_with_methods() {
        let m = parse_mod(
            "trait Additive\n  fn zero() -> Self\n  fn add(self, other: Self) -> Self",
        );
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert!(td.supertraits.is_empty());
                assert!(td.fundeps.is_empty());
                assert!(td.type_params.is_empty());
                assert_eq!(td.methods.len(), 2);
                assert_eq!(td.methods[0].name.node, "zero");
                assert!(td.methods[0].params.is_empty());
                assert!(td.methods[0].return_annotation.is_some());
                assert!(td.methods[0].where_clause.is_empty());
                assert_eq!(td.methods[1].name.node, "add");
                assert_eq!(td.methods[1].params.len(), 2);
                assert_eq!(td.methods[1].params[0].name().unwrap(), "self");
                assert!(td.methods[1].where_clause.is_empty());
            }
            _ => panic!("expected TraitDef"),
        }
    }

    #[test]
    fn parse_trait_with_methods_indented() {
        let m = parse_mod("trait Additive\n  fn zero() -> Self\n  fn add(self, other: Self) -> Self");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert_eq!(td.methods.len(), 2);
            }
            _ => panic!("expected TraitDef"),
        }
    }

    #[test]
    fn parse_trait_method_with_where_clause() {
        let m = parse_mod(
            "trait Traversable(T: *)\n  fn traverse(value: T, f: fn(a) -> F(b)) -> F(T) where F: Applicative",
        );
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert_eq!(td.methods.len(), 1);
                let method = &td.methods[0];
                assert_eq!(method.name.node, "traverse");
                assert_eq!(method.where_clause.len(), 1);
                assert_eq!(method.where_clause[0].type_var.node, "F");
                assert_eq!(method.where_clause[0].trait_name.node, "Applicative");
            }
            other => panic!("expected TraitDef, got {other:?}"),
        }
    }

    #[test]
    fn parse_trait_method_with_effect_clause() {
        let m = parse_mod("trait TaskLike\n  fn run(self) -[impure]> Int");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                let method = &td.methods[0];
                assert!(matches!(
                    method.effect_annotation.as_ref().map(|e| &e.node),
                    Some(EffectAnnotation::Impure)
                ));
            }
            other => panic!("expected TraitDef, got {other:?}"),
        }
    }

    #[test]
    fn parse_pub_trait() {
        let m = parse_mod("pub trait Show\n  fn show(self) -> String");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert!(td.public);
                assert_eq!(td.name.node, "Show");
                assert!(td.type_params.is_empty());
                assert!(td.supertraits.is_empty());
                assert!(td.fundeps.is_empty());
                assert_eq!(td.methods.len(), 1);
            }
            _ => panic!("expected TraitDef"),
        }
    }

    #[test]
    fn parse_trait_with_supertraits() {
        let m = parse_mod("trait Orderable: Eq + Display\n  fn compare(self, other: Self) -> Int");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert_eq!(td.name.node, "Orderable");
                assert!(td.type_params.is_empty());
                assert_eq!(td.supertraits.len(), 2);
                assert_eq!(td.supertraits[0].node, "Eq");
                assert_eq!(td.supertraits[1].node, "Display");
                assert!(td.fundeps.is_empty());
                assert_eq!(td.methods.len(), 1);
            }
            _ => panic!("expected TraitDef"),
        }
    }

    #[test]
    fn parse_trait_with_fundep() {
        let m = parse_mod("trait Collection(C: *, E: *) | C -> E\n  fn empty() -> C");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert_eq!(td.fundeps.len(), 1);
                assert_eq!(td.fundeps[0].from.len(), 1);
                assert_eq!(td.fundeps[0].from[0].node, "C");
                assert_eq!(td.fundeps[0].to.len(), 1);
                assert_eq!(td.fundeps[0].to[0].node, "E");
            }
            other => panic!("expected TraitDef, got {other:?}"),
        }
    }

    #[test]
    fn parse_trait_with_multi_param_fundep() {
        let m =
            parse_mod("trait Convert(A: *, B: *, C: *) | (A, B) -> C, C -> A\n  fn convert(a: A, b: B) -> C");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert_eq!(td.fundeps.len(), 2);
                assert_eq!(td.fundeps[0].from.len(), 2);
                assert_eq!(td.fundeps[0].from[0].node, "A");
                assert_eq!(td.fundeps[0].from[1].node, "B");
                assert_eq!(td.fundeps[0].to.len(), 1);
                assert_eq!(td.fundeps[0].to[0].node, "C");
                assert_eq!(td.fundeps[1].from[0].node, "C");
                assert_eq!(td.fundeps[1].to[0].node, "A");
                assert_eq!(td.methods.len(), 1);
            }
            other => panic!("expected TraitDef, got {other:?}"),
        }
    }

    #[test]
    fn parse_trait_with_hkt_kind_param_is_error() {
        let errors = parse_mod_err("trait Bind(F: * -> *)\n  fn bind(value: Int) -> Int");
        assert!(
            errors.iter().any(|d| {
                d.message
                    .contains("higher-kinded kind arrows are not supported in Kea v0")
            }),
            "expected HKT-kind diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_trait_method_with_default_body() {
        let m = parse_mod("trait Defaultable\n  fn value() -> Int\n    42");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert_eq!(td.methods.len(), 1);
                assert!(td.methods[0].default_body.is_some());
                match &td.methods[0].default_body.as_ref().unwrap().node {
                    ExprKind::Lit(Lit::Int(42)) => {}
                    other => panic!("expected Int(42) body, got {:?}", other),
                }
            }
            _ => panic!("expected TraitDef"),
        }
    }

    // -- Impl parsing --

    #[test]
    fn parse_impl_trait_for_type() {
        let m = parse_mod(
            "impl Additive for Int\n  fn zero() -> Int\n    0\n  fn add(self, other) -> Int\n    self + other",
        );
        assert_eq!(m.declarations.len(), 1);
        match &m.declarations[0].node {
            DeclKind::ImplBlock(ib) => {
                assert_eq!(ib.trait_name.node, "Additive");
                assert_eq!(ib.type_name.node, "Int");
                assert!(ib.type_params.is_empty());
                assert_eq!(ib.methods.len(), 2);
                assert_eq!(ib.methods[0].name.node, "zero");
                assert_eq!(ib.methods[1].name.node, "add");
            }
            _ => panic!("expected ImplBlock"),
        }
    }

    #[test]
    fn parse_impl_trait_for_type_indented() {
        let m = parse_mod(
            "impl Additive for Int\n  fn zero() -> Int\n    0\n  fn add(self, other) -> Int\n    self + other",
        );
        assert_eq!(m.declarations.len(), 1);
        match &m.declarations[0].node {
            DeclKind::ImplBlock(ib) => {
                assert_eq!(ib.methods.len(), 2);
                assert_eq!(ib.methods[0].name.node, "zero");
                assert_eq!(ib.methods[1].name.node, "add");
            }
            _ => panic!("expected ImplBlock"),
        }
    }

    #[test]
    fn parse_impl_with_type_params() {
        let m = parse_mod(
            "impl Show for List(t) where t: Show\n  fn show(self) -> String\n    \"list\"",
        );
        match &m.declarations[0].node {
            DeclKind::ImplBlock(ib) => {
                assert_eq!(ib.trait_name.node, "Show");
                assert_eq!(ib.type_name.node, "List");
                assert_eq!(ib.type_params.len(), 1);
                assert_eq!(ib.type_params[0].node, "t");
                assert_eq!(ib.where_clause.len(), 1);
                match &ib.where_clause[0] {
                    WhereItem::TraitBound(tb) => {
                        assert_eq!(tb.type_var.node, "t");
                        assert_eq!(tb.trait_name.node, "Show");
                    }
                    other => panic!("expected TraitBound, got {:?}", other),
                }
                assert_eq!(ib.methods.len(), 1);
            }
            _ => panic!("expected ImplBlock"),
        }
    }

    #[test]
    fn parse_impl_with_multiple_type_params() {
        let m = parse_mod(
            "impl Collectable for Map(k, v) where Element = Pair(k, v), k: Hashable\n  fn empty() -> Int\n    0",
        );
        match &m.declarations[0].node {
            DeclKind::ImplBlock(ib) => {
                assert_eq!(ib.trait_name.node, "Collectable");
                assert_eq!(ib.type_name.node, "Map");
                assert_eq!(ib.type_params.len(), 2);
                assert_eq!(ib.type_params[0].node, "k");
                assert_eq!(ib.type_params[1].node, "v");
                assert_eq!(ib.where_clause.len(), 2);
                match &ib.where_clause[0] {
                    WhereItem::TypeAssignment { name, ty } => {
                        assert_eq!(name.node, "Element");
                        match &ty.node {
                            TypeAnnotation::Applied(base, args) => {
                                assert_eq!(base, "Pair");
                                assert_eq!(args.len(), 2);
                            }
                            other => panic!("expected Applied(Pair, ...), got {:?}", other),
                        }
                    }
                    other => panic!("expected TypeAssignment, got {:?}", other),
                }
                match &ib.where_clause[1] {
                    WhereItem::TraitBound(tb) => {
                        assert_eq!(tb.type_var.node, "k");
                        assert_eq!(tb.trait_name.node, "Hashable");
                    }
                    other => panic!("expected TraitBound, got {:?}", other),
                }
            }
            _ => panic!("expected ImplBlock"),
        }
    }

    #[test]
    fn parse_inherent_impl_is_rejected() {
        let errs =
            parse_mod_err("impl Counter {\n  pub fn new(n) { n }\n  fn inc(self) { self + 1 }\n}");
        assert!(!errs.is_empty());
    }

    #[test]
    fn parse_impl_with_return_annotation() {
        let m = parse_mod("impl Show for Bool\n  fn show(self) -> String\n    \"bool\"");
        match &m.declarations[0].node {
            DeclKind::ImplBlock(ib) => {
                assert_eq!(ib.trait_name.node, "Show");
                assert!(ib.methods[0].return_annotation.is_some());
            }
            _ => panic!("expected ImplBlock"),
        }
    }

    #[test]
    fn parse_impl_separate_methods() {
        let m = parse_mod(
            "impl Show for Bool\n  fn show(self) -> String\n    \"bool\"\n  fn to_int(self) -> Int\n    0",
        );
        match &m.declarations[0].node {
            DeclKind::ImplBlock(ib) => {
                assert_eq!(ib.methods.len(), 2, "should have 2 separate methods");
                assert_eq!(ib.methods[0].name.node, "show");
                assert_eq!(ib.methods[1].name.node, "to_int");
            }
            _ => panic!("expected ImplBlock"),
        }
    }

    // -- Where clause parsing --

    #[test]
    fn parse_fn_with_where_clause() {
        let m = parse_mod("fn total(x) -> Int where x: Additive\n  x");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                assert_eq!(fd.where_clause.len(), 1);
                assert_eq!(fd.where_clause[0].type_var.node, "x");
                assert_eq!(fd.where_clause[0].trait_name.node, "Additive");
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_with_multiple_where_bounds() {
        let m = parse_mod("fn combine(a, b) -> T where a: Show, b: Additive\n  a");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                assert_eq!(fd.where_clause.len(), 2);
                assert_eq!(fd.where_clause[0].type_var.node, "a");
                assert_eq!(fd.where_clause[0].trait_name.node, "Show");
                assert_eq!(fd.where_clause[1].type_var.node, "b");
                assert_eq!(fd.where_clause[1].trait_name.node, "Additive");
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_with_uppercase_where_type_var() {
        let m = parse_mod("fn sequence(xs) -> Int where F: Applicative\n  xs");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                assert_eq!(fd.where_clause.len(), 1);
                assert_eq!(fd.where_clause[0].type_var.node, "F");
                assert_eq!(fd.where_clause[0].trait_name.node, "Applicative");
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_type_annotation_in_param() {
        let m = parse_mod("fn apply(xs, f: fn(Int) -> Option(Int)) -> Int\n  xs");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ann = fd.params[1]
                    .annotation
                    .as_ref()
                    .expect("second param should have annotation");
                match &ann.node {
                    TypeAnnotation::Function(params, ret) => {
                        assert_eq!(params.len(), 1);
                        assert!(matches!(params[0], TypeAnnotation::Named(ref n) if n == "Int"));
                        match ret.as_ref() {
                            TypeAnnotation::Applied(name, args) => {
                                assert_eq!(name, "Option");
                                assert_eq!(args.len(), 1);
                            }
                            other => panic!("expected Option(Int) return, got {other:?}"),
                        }
                    }
                    other => panic!("expected function type annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_type_annotation_with_effect_in_param() {
        let m = parse_mod("fn apply(f: fn(Int) -[pure]> Option(Int)) -> Int\n  0");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ann = fd.params[0]
                    .annotation
                    .as_ref()
                    .expect("param should have annotation");
                match &ann.node {
                    TypeAnnotation::FunctionWithEffect(params, effect, ret) => {
                        assert_eq!(params.len(), 1);
                        assert!(matches!(params[0], TypeAnnotation::Named(ref n) if n == "Int"));
                        assert!(matches!(effect.node, EffectAnnotation::Pure));
                        match ret.as_ref() {
                            TypeAnnotation::Applied(name, args) => {
                                assert_eq!(name, "Option");
                                assert_eq!(args.len(), 1);
                            }
                            other => panic!("expected Option(Int) return, got {other:?}"),
                        }
                    }
                    other => panic!("expected effectful function type annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_type_annotation_with_effect_row_in_param() {
        let m = parse_mod("fn apply(f: fn(Int) -[IO, Fail E | e]> Option(Int)) -> Int\n  0");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ann = fd.params[0]
                    .annotation
                    .as_ref()
                    .expect("param should have annotation");
                match &ann.node {
                    TypeAnnotation::FunctionWithEffect(params, effect, ret) => {
                        assert_eq!(params.len(), 1);
                        assert!(matches!(params[0], TypeAnnotation::Named(ref n) if n == "Int"));
                        match &effect.node {
                            EffectAnnotation::Row(row) => {
                                assert_eq!(row.effects.len(), 2);
                                assert_eq!(row.effects[0].name, "IO");
                                assert_eq!(row.effects[1].name, "Fail");
                                assert_eq!(row.effects[1].payload.as_deref(), Some("E"));
                                assert_eq!(row.rest.as_deref(), Some("e"));
                            }
                            other => panic!("expected row effect annotation, got {other:?}"),
                        }
                        match ret.as_ref() {
                            TypeAnnotation::Applied(name, args) => {
                                assert_eq!(name, "Option");
                                assert_eq!(args.len(), 1);
                            }
                            other => panic!("expected Option(Int) return, got {other:?}"),
                        }
                    }
                    other => panic!("expected effectful function type annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_type_annotation_with_tail_only_effect_row_in_param() {
        let m = parse_mod("fn apply(f: fn(Int) -[| e]> Option(Int)) -> Int\n  0");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ann = fd.params[0]
                    .annotation
                    .as_ref()
                    .expect("param should have annotation");
                match &ann.node {
                    TypeAnnotation::FunctionWithEffect(_, effect, _) => match &effect.node {
                        EffectAnnotation::Row(row) => {
                            assert!(row.effects.is_empty());
                            assert_eq!(row.rest.as_deref(), Some("e"));
                        }
                        other => panic!("expected row effect annotation, got {other:?}"),
                    },
                    other => panic!("expected effectful function type annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_decimal_type_annotation_arguments_allow_int_literals() {
        let m = parse_mod("fn as_money(x: Decimal(18, 2)) -> Decimal(18, 2)\n  x");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let param_ann = fd.params[0]
                    .annotation
                    .as_ref()
                    .expect("param should have annotation");
                match &param_ann.node {
                    TypeAnnotation::Applied(name, args) => {
                        assert_eq!(name, "Decimal");
                        assert_eq!(args.len(), 2);
                        assert!(matches!(&args[0], TypeAnnotation::DimLiteral(18)));
                        assert!(matches!(&args[1], TypeAnnotation::DimLiteral(2)));
                    }
                    other => panic!("expected Decimal(18, 2) annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_list_of_decimal_type_annotation_with_int_args() {
        let m = parse_mod("fn prices(xs: List(Decimal(18, 2))) -> List(Decimal(18, 2))\n  xs");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let param_ann = fd.params[0]
                    .annotation
                    .as_ref()
                    .expect("param should have annotation");
                match &param_ann.node {
                    TypeAnnotation::Applied(name, args) => {
                        assert_eq!(name, "List");
                        assert_eq!(args.len(), 1);
                        match &args[0] {
                            TypeAnnotation::Applied(inner_name, inner_args) => {
                                assert_eq!(inner_name, "Decimal");
                                assert_eq!(inner_args.len(), 2);
                                assert!(matches!(&inner_args[0], TypeAnnotation::DimLiteral(18)));
                                assert!(matches!(&inner_args[1], TypeAnnotation::DimLiteral(2)));
                            }
                            other => panic!("expected Decimal(...) inside List, got {other:?}"),
                        }
                    }
                    other => panic!("expected List(Decimal(...)) annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_int_literal_in_any_type_application_arg() {
        // Parser accepts int literals in any type application position.
        // Type checker validates whether the constructor accepts dim params.
        let m = parse_mod("fn f(xs: List(1)) -> Int\n  0");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let param_ann = fd.params[0]
                    .annotation
                    .as_ref()
                    .expect("param should have annotation");
                match &param_ann.node {
                    TypeAnnotation::Applied(name, args) => {
                        assert_eq!(name, "List");
                        assert_eq!(args.len(), 1);
                        assert!(matches!(&args[0], TypeAnnotation::DimLiteral(1)));
                    }
                    other => panic!("expected List(1) annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_rank2_forall_type_annotation_in_param() {
        let m = parse_mod("fn apply(f: forall a. fn(a) -> a, x: Int) -> Int\n  x");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ann = fd.params[0]
                    .annotation
                    .as_ref()
                    .expect("first param should have annotation");
                match &ann.node {
                    TypeAnnotation::Forall { type_vars, ty } => {
                        assert_eq!(type_vars, &vec!["a".to_string()]);
                        assert!(matches!(ty.as_ref(), TypeAnnotation::Function(_, _)));
                    }
                    other => panic!("expected forall type annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_rank2_forall_requires_dot() {
        let errors = parse_mod_err("fn bad(f: forall a fn(a) -> a) -> Int { 0 }");
        assert!(
            errors.iter().any(|d| d
                .message
                .contains("expected '.' after forall type variables")),
            "expected missing-dot diagnostic, got: {:?}",
            errors.iter().map(|d| d.message.clone()).collect::<Vec<_>>()
        );
    }

    #[test]
    fn parse_fn_without_where_clause() {
        let m = parse_mod("fn identity(x) -> Int\n  x");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                assert!(fd.where_clause.is_empty());
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_fn_with_return_and_where() {
        let m = parse_mod("fn total(xs) -> Int where xs: Additive\n  0");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                assert!(fd.return_annotation.is_some());
                assert_eq!(fd.where_clause.len(), 1);
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_tuple_type_annotation_in_return() {
        let m = parse_mod("fn swap(a: Int, b: String) -> #(String, Int)\n  #(b, a)");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ret = fd
                    .return_annotation
                    .as_ref()
                    .expect("should have return type");
                match &ret.node {
                    TypeAnnotation::Tuple(elems) => {
                        assert_eq!(elems.len(), 2);
                        assert!(matches!(&elems[0], TypeAnnotation::Named(n) if n == "String"));
                        assert!(matches!(&elems[1], TypeAnnotation::Named(n) if n == "Int"));
                    }
                    other => panic!("expected Tuple type annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_tuple_type_annotation_in_param() {
        let m = parse_mod("fn first(pair: #(Int, String)) -> Int\n  0");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ann = fd.params[0]
                    .annotation
                    .as_ref()
                    .expect("should have annotation");
                match &ann.node {
                    TypeAnnotation::Tuple(elems) => {
                        assert_eq!(elems.len(), 2);
                        assert!(matches!(&elems[0], TypeAnnotation::Named(n) if n == "Int"));
                        assert!(matches!(&elems[1], TypeAnnotation::Named(n) if n == "String"));
                    }
                    other => panic!("expected Tuple type annotation, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_nested_tuple_type_annotation() {
        let m = parse_mod("fn nested(x: #(#(Int, Bool), String)) -> #(#(Int, Bool), String)\n  x");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                // Check param annotation
                let ann = fd.params[0].annotation.as_ref().expect("param annotation");
                match &ann.node {
                    TypeAnnotation::Tuple(outer) => {
                        assert_eq!(outer.len(), 2);
                        assert!(
                            matches!(&outer[0], TypeAnnotation::Tuple(inner) if inner.len() == 2)
                        );
                    }
                    other => panic!("expected nested Tuple annotation, got {other:?}"),
                }
                // Check return annotation
                let ret = fd.return_annotation.as_ref().expect("return annotation");
                match &ret.node {
                    TypeAnnotation::Tuple(outer) => {
                        assert_eq!(outer.len(), 2);
                        assert!(
                            matches!(&outer[0], TypeAnnotation::Tuple(inner) if inner.len() == 2)
                        );
                    }
                    other => panic!("expected nested Tuple return, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_tuple_type_in_generic_position() {
        let m =
            parse_mod("fn wrap(x: List(#(Int, String))) -> Result(#(Int, String), Bool)\n  Ok(x)");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ann = fd.params[0].annotation.as_ref().expect("param annotation");
                match &ann.node {
                    TypeAnnotation::Applied(name, args) => {
                        assert_eq!(name, "List");
                        assert!(
                            matches!(&args[0], TypeAnnotation::Tuple(elems) if elems.len() == 2)
                        );
                    }
                    other => panic!("expected Applied(List, [Tuple]), got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    // -- Mixed declarations --

    #[test]
    fn parse_mixed_declarations() {
        let m = parse_mod(
            "record Point\n  x: Float\n  y: Float\ntrait Additive\n  fn zero() -> Self\nimpl Additive for Point\n  fn zero() -> Int\n    0\nfn main() -> Int\n  1",
        );
        assert_eq!(m.declarations.len(), 4);
        assert!(matches!(m.declarations[0].node, DeclKind::RecordDef(_)));
        assert!(matches!(m.declarations[1].node, DeclKind::TraitDef(_)));
        assert!(matches!(m.declarations[2].node, DeclKind::ImplBlock(_)));
        assert!(matches!(m.declarations[3].node, DeclKind::Function(_)));
    }

    // -- Expr declarations --

    #[test]
    fn parse_expr_basic() {
        let m = parse_mod("expr double(x: Int) -> Int\n  x + x");
        assert_eq!(m.declarations.len(), 1);
        match &m.declarations[0].node {
            DeclKind::ExprFn(ed) => {
                assert_eq!(ed.name.node, "double");
                assert!(!ed.public);
                assert_eq!(ed.params.len(), 1);
                assert_eq!(ed.params[0].name().unwrap(), "x");
                assert!(ed.return_annotation.is_some());
                assert!(ed.testing.is_none());
            }
            other => panic!("expected ExprFn, got {other:?}"),
        }
    }

    #[test]
    fn parse_expr_basic_indented_body() {
        let m = parse_mod("expr double(x: Int) -> Int\n  x + x");
        match &m.declarations[0].node {
            DeclKind::ExprFn(ed) => {
                assert_eq!(ed.name.node, "double");
                assert!(matches!(ed.body.node, ExprKind::BinaryOp { .. }));
            }
            other => panic!("expected ExprFn, got {other:?}"),
        }
    }

    #[test]
    fn parse_expr_with_postfix_testing_block() {
        let m = parse_mod("expr double(x: Int) -> Int\n  x + x\ntesting\n  assert_eq double(0), 0");
        match &m.declarations[0].node {
            DeclKind::ExprFn(ed) => {
                assert!(ed.testing.is_some(), "expected postfix testing block");
                assert!(ed.testing_tags.is_empty());
            }
            other => panic!("expected ExprFn, got {other:?}"),
        }
    }

    #[test]
    fn parse_test_decl_with_tags() {
        let m = parse_mod("test \"basic\" tags [:fast, :io]\n  assert true");
        match &m.declarations[0].node {
            DeclKind::Test(td) => {
                assert_eq!(td.tags.len(), 2);
                assert_eq!(td.tags[0].node, "fast");
                assert_eq!(td.tags[1].node, "io");
            }
            other => panic!("expected Test, got {other:?}"),
        }
    }

    #[test]
    fn parse_test_decl_with_tags_indented_body() {
        let m = parse_mod("test \"basic\" tags [:fast, :io]\n  assert true");
        match &m.declarations[0].node {
            DeclKind::Test(td) => {
                assert_eq!(td.tags.len(), 2);
                assert_eq!(td.tags[0].node, "fast");
                assert_eq!(td.tags[1].node, "io");
            }
            other => panic!("expected Test, got {other:?}"),
        }
    }

    #[test]
    fn parse_expr_with_effect_clause() {
        let m = parse_mod("expr double(x: Int) -[e]> Int\n  x + x");
        match &m.declarations[0].node {
            DeclKind::ExprFn(ed) => {
                assert!(matches!(
                    ed.effect_annotation.as_ref().map(|e| &e.node),
                    Some(EffectAnnotation::Var(name)) if name == "e"
                ));
            }
            other => panic!("expected ExprFn, got {other:?}"),
        }
    }

    #[test]
    fn parse_pub_expr() {
        let m = parse_mod("pub expr add(x: Int, y: Int) -> Int\n  x + y");
        match &m.declarations[0].node {
            DeclKind::ExprFn(ed) => {
                assert!(ed.public);
                assert_eq!(ed.name.node, "add");
                assert_eq!(ed.params.len(), 2);
            }
            other => panic!("expected ExprFn, got {other:?}"),
        }
    }

    #[test]
    fn parse_expr_with_doc_comment() {
        let m = parse_mod("--| Doubles an integer.\nexpr double(x: Int) -> Int\n  x + x");
        match &m.declarations[0].node {
            DeclKind::ExprFn(ed) => {
                assert_eq!(ed.doc.as_deref(), Some("Doubles an integer."));
            }
            other => panic!("expected ExprFn, got {other:?}"),
        }
    }

    #[test]
    fn parse_effect_arrow_missing_term_errors() {
        let errors = parse_mod_err("fn f() -[]> Int { 1 }");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("expected effect after -[")),
            "expected missing effect term diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_effect_arrow_missing_close_bracket_errors() {
        let errors = parse_mod_err("fn f() -[e> Int { 1 }");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("expected ] in effect arrow")),
            "expected missing ] diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_effect_arrow_missing_gt_errors() {
        let errors = parse_mod_err("fn f() -[e] Int { 1 }");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("expected > to complete effect arrow")),
            "expected missing > diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_effect_arrow_invalid_term_errors() {
        let errors = parse_mod_err("fn f() -[123]> Int { 1 }");
        assert!(
            errors.iter().any(|d| d
                .message
                .contains("expected pure|volatile|impure or effect variable")),
            "expected invalid effect term diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_expr_with_where_clause() {
        let m = parse_mod("expr total(x) -> Int where x: Additive\n  x");
        match &m.declarations[0].node {
            DeclKind::ExprFn(ed) => {
                assert_eq!(ed.where_clause.len(), 1);
                assert_eq!(ed.where_clause[0].trait_name.node, "Additive");
            }
            other => panic!("expected ExprFn, got {other:?}"),
        }
    }

    #[test]
    fn parse_expr_no_return_annotation() {
        let errs = parse_mod_err("expr id(x) { x }");
        assert!(
            errs.iter()
                .any(|d| d.message.contains("require a return type")),
            "expected return type error, got {errs:?}"
        );
    }

    #[test]
    fn parse_expr_in_mixed_declarations() {
        let m = parse_mod("fn regular(x) -> Int\n  x\nexpr pure(x: Int) -> Int\n  x + 1");
        assert_eq!(m.declarations.len(), 2);
        assert!(matches!(m.declarations[0].node, DeclKind::Function(_)));
        assert!(matches!(m.declarations[1].node, DeclKind::ExprFn(_)));
    }

    #[test]
    fn parse_expr_multiline_body() {
        let m = parse_mod("expr clamp(x: Int) -> Int\n  let y = x + 1\n  y");
        match &m.declarations[0].node {
            DeclKind::ExprFn(ed) => {
                assert_eq!(ed.name.node, "clamp");
            }
            other => panic!("expected ExprFn, got {other:?}"),
        }
    }

    #[test]
    fn parse_expr_cond_body() {
        let m = parse_mod("expr abs(x: Int) -> Int\n  cond\n    x >= 0 -> x\n    _ -> 0 - x");
        match &m.declarations[0].node {
            DeclKind::ExprFn(ed) => {
                assert_eq!(ed.name.node, "abs");
            }
            other => panic!("expected ExprFn, got {other:?}"),
        }
    }

    #[test]
    fn parse_derive_rejected_on_expr() {
        let errs = parse_mod_err("#[derive(Display)]\nexpr f(x: Int) -> Int { x }");
        assert!(!errs.is_empty());
    }

    // -- Error cases --

    #[test]
    fn parse_trait_missing_brace() {
        let errs = parse_mod_err("trait Additive fn zero()");
        assert!(!errs.is_empty());
    }

    #[test]
    fn parse_impl_missing_type_name() {
        let errs = parse_mod_err("impl { fn zero() { 0 } }");
        assert!(!errs.is_empty());
    }

    // -- Associated types and deriving --

    #[test]
    fn parse_trait_with_associated_type() {
        let m = parse_mod("trait From\n  type Source\n  fn from(value: Self.Source) -> Result(Self, String)");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert_eq!(td.name.node, "From");
                assert_eq!(td.associated_types.len(), 1);
                assert_eq!(td.associated_types[0].name.node, "Source");
                assert!(td.associated_types[0].constraints.is_empty());
                assert!(td.associated_types[0].default.is_none());
                assert_eq!(td.methods.len(), 1);
                assert_eq!(td.methods[0].name.node, "from");
                // Check Self.Source in parameter type (from(value: Self.Source) — value is params[0])
                let param_type = &td.methods[0].params[0].annotation.as_ref().unwrap();
                match &param_type.node {
                    TypeAnnotation::Projection { base, name } => {
                        assert_eq!(base, "Self");
                        assert_eq!(name, "Source");
                    }
                    other => panic!("expected Projection, got {:?}", other),
                }
            }
            _ => panic!("expected TraitDef"),
        }
    }

    #[test]
    fn parse_trait_with_constrained_associated_type() {
        let m = parse_mod(
            "trait Actor\n  type Message where Message: Sendable\n  fn handle(self, msg: Self.Message) -> Self",
        );
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert_eq!(td.associated_types.len(), 1);
                assert_eq!(td.associated_types[0].name.node, "Message");
                assert_eq!(td.associated_types[0].constraints.len(), 1);
                assert_eq!(td.associated_types[0].constraints[0].node, "Sendable");
                assert!(td.associated_types[0].default.is_none());
            }
            _ => panic!("expected TraitDef"),
        }
    }

    #[test]
    fn parse_trait_with_default_associated_type() {
        let m =
            parse_mod("trait Container\n  type Item = String\n  fn head(self) -> Self.Item");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                assert_eq!(td.associated_types.len(), 1);
                assert_eq!(td.associated_types[0].name.node, "Item");
                assert!(td.associated_types[0].constraints.is_empty());
                let Some(default) = &td.associated_types[0].default else {
                    panic!("expected associated type default");
                };
                assert!(matches!(default.node, TypeAnnotation::Named(ref n) if n == "String"));
            }
            _ => panic!("expected TraitDef"),
        }
    }

    #[test]
    fn parse_impl_with_where_clause() {
        let m = parse_mod("impl From for Int where Source = String\n  fn from(value) -> Int\n    0");
        match &m.declarations[0].node {
            DeclKind::ImplBlock(ib) => {
                assert_eq!(ib.trait_name.node, "From");
                assert_eq!(ib.type_name.node, "Int");
                assert_eq!(ib.where_clause.len(), 1);
                match &ib.where_clause[0] {
                    WhereItem::TypeAssignment { name, ty } => {
                        assert_eq!(name.node, "Source");
                        match &ty.node {
                            TypeAnnotation::Named(n) => assert_eq!(n, "String"),
                            other => panic!("expected Named(String), got {:?}", other),
                        }
                    }
                    other => panic!("expected TypeAssignment, got {:?}", other),
                }
                assert_eq!(ib.methods.len(), 1);
            }
            _ => panic!("expected ImplBlock"),
        }
    }

    #[test]
    fn parse_impl_with_body_associated_type_is_rejected() {
        let errs = parse_mod_err(
            "impl Actor for Counter {\n  type Control = Stop\n  fn handle(self) { self }\n}",
        );
        assert!(!errs.is_empty());
    }

    #[test]
    fn parse_record_deriving() {
        let m = parse_mod("record Point\n  x: Int\n  y: Int\nderiving Eq, Display");
        match &m.declarations[0].node {
            DeclKind::RecordDef(def) => {
                assert_eq!(def.name.node, "Point");
                assert_eq!(def.derives.len(), 2);
                assert_eq!(def.derives[0].node, "Eq");
                assert_eq!(def.derives[1].node, "Display");
                assert_eq!(def.fields.len(), 2);
            }
            _ => panic!("expected RecordDef"),
        }
    }

    #[test]
    fn parse_record_derive_attribute_is_rejected() {
        let errs = parse_mod_err("#[derive(Eq)]\nrecord Point { x: Int }");
        assert!(!errs.is_empty());
    }

    #[test]
    fn parse_record_pre_body_deriving_is_rejected() {
        let errs = parse_mod_err("record Point deriving Eq { x: Int }");
        assert!(!errs.is_empty());
    }

    #[test]
    fn parse_type_deriving() {
        let m = parse_mod("type Color = Red | Green | Blue deriving Eq");
        match &m.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert_eq!(def.name.node, "Color");
                assert_eq!(def.derives.len(), 1);
                assert_eq!(def.derives[0].node, "Eq");
                assert_eq!(def.variants.len(), 3);
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn parse_legacy_paren_deriving_is_rejected() {
        let errs = parse_mod_err("type Color = Red | Green | Blue deriving(Eq)");
        assert!(!errs.is_empty());
    }

    #[test]
    fn parse_type_pre_variants_deriving_is_rejected() {
        let errs = parse_mod_err("type Color deriving Eq = Red | Green | Blue");
        assert!(!errs.is_empty());
    }

    #[test]
    fn parse_self_dot_name_type_annotation() {
        let m = parse_mod("trait Convert\n  type Output\n  fn convert(self) -> Self.Output");
        match &m.declarations[0].node {
            DeclKind::TraitDef(td) => {
                let ret = td.methods[0].return_annotation.as_ref().unwrap();
                match &ret.node {
                    TypeAnnotation::Projection { base, name } => {
                        assert_eq!(base, "Self");
                        assert_eq!(name, "Output");
                    }
                    other => panic!("expected Projection, got {:?}", other),
                }
            }
            _ => panic!("expected TraitDef"),
        }
    }

    #[test]
    fn parse_existential_single_bound_annotation() {
        let m = parse_mod("fn f(x: any Show) -> Int\n  x");
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ann = fd.params[0].annotation.as_ref().expect("annotation");
                match &ann.node {
                    TypeAnnotation::Existential {
                        bounds,
                        associated_types,
                    } => {
                        assert_eq!(bounds, &vec!["Show".to_string()]);
                        assert!(associated_types.is_empty());
                    }
                    other => panic!("expected Existential, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn parse_existential_multi_bound_with_assoc_constraints() {
        let m = parse_mod(
            "fn f(x: any (Show, Eq) where Item = Int, Source = String) -> Int\n  x",
        );
        match &m.declarations[0].node {
            DeclKind::Function(fd) => {
                let ann = fd.params[0].annotation.as_ref().expect("annotation");
                match &ann.node {
                    TypeAnnotation::Existential {
                        bounds,
                        associated_types,
                    } => {
                        assert_eq!(bounds, &vec!["Show".to_string(), "Eq".to_string()]);
                        assert_eq!(associated_types.len(), 2);
                        assert_eq!(associated_types[0].0, "Item");
                        assert_eq!(associated_types[1].0, "Source");
                    }
                    other => panic!("expected Existential, got {other:?}"),
                }
            }
            _ => panic!("expected Function"),
        }
    }

    // -- frame literal --

    #[test]
    fn parse_frame_literal_is_error() {
        let errors = parse_err("frame { x: [1, 2, 3] }");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("`frame` literals are not supported in Kea v0")),
            "expected unsupported frame diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_frame_literal_multi_column_is_error() {
        let errors = parse_err("frame { name: [\"a\", \"b\"], age: [30, 25] }");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("`frame` literals are not supported in Kea v0")),
            "expected unsupported frame diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_frame_literal_empty_is_error() {
        let errors = parse_err("frame { }");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("`frame` literals are not supported in Kea v0")),
            "expected unsupported frame diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_frame_literal_trailing_comma_is_error() {
        let errors = parse_err("frame { x: [1, 2], y: [3, 4], }");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("`frame` literals are not supported in Kea v0")),
            "expected unsupported frame diagnostic, got {errors:?}"
        );
    }

    // -- Block arguments (sql, html, markdown) --

    #[test]
    fn parse_sql_block_is_error() {
        let errors = parse_err("sql { SELECT 1 AS x }");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("`sql { ... }` blocks are not supported in Kea v0")),
            "expected unsupported sql diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_html_block_is_error() {
        let errors = parse_err("html { <h1>${:name}</h1> }");
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("`html { ... }` blocks are not supported in Kea v0")),
            "expected unsupported html diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_markdown_block_is_error() {
        let errors = parse_err("markdown { # ${:title}\\n\\nCount: ${1} }");
        assert!(
            errors.iter().any(|d| d
                .message
                .contains("`markdown { ... }` blocks are not supported in Kea v0")),
            "expected unsupported markdown diagnostic, got {errors:?}"
        );
    }

    // -- Import declarations --

    #[test]
    fn parse_import_module() {
        let module = parse_mod("import Kea");
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::Import(decl) => {
                assert_eq!(decl.module.node, "Kea");
                assert_eq!(decl.items, ImportItems::Module);
            }
            other => panic!("expected Import, got {other:?}"),
        }
    }

    #[test]
    fn parse_import_dotted_module() {
        let module = parse_mod("import Kea.Core");
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::Import(decl) => {
                assert_eq!(decl.module.node, "Kea.Core");
                assert_eq!(decl.items, ImportItems::Module);
            }
            other => panic!("expected Import, got {other:?}"),
        }
    }

    #[test]
    fn parse_import_deeply_nested() {
        let module = parse_mod("import Kea.Core.IO");
        match &module.declarations[0].node {
            DeclKind::Import(decl) => {
                assert_eq!(decl.module.node, "Kea.Core.IO");
                assert_eq!(decl.items, ImportItems::Module);
            }
            other => panic!("expected Import, got {other:?}"),
        }
    }

    #[test]
    fn parse_import_glob_is_error() {
        let tokens = crate::lex("import Kea.Core.*", FileId(0))
            .expect("lex ok")
            .0;
        let result = crate::parse_module(tokens, FileId(0));
        assert!(result.is_err(), "glob import should produce a parse error");
    }

    #[test]
    fn parse_import_with_alias() {
        let module = parse_mod("import Kea.Math as M");
        match &module.declarations[0].node {
            DeclKind::Import(decl) => {
                assert_eq!(decl.module.node, "Kea.Math");
                assert_eq!(decl.items, ImportItems::Module);
                assert_eq!(decl.alias.as_ref().unwrap().node, "M");
            }
            other => panic!("expected Import, got {other:?}"),
        }
    }

    #[test]
    fn parse_import_named() {
        let module = parse_mod("import Kea.Core.{read_csv, write_csv}");
        match &module.declarations[0].node {
            DeclKind::Import(decl) => {
                assert_eq!(decl.module.node, "Kea.Core");
                match &decl.items {
                    ImportItems::Named(names) => {
                        assert_eq!(names.len(), 2);
                        assert_eq!(names[0].node, "read_csv");
                        assert_eq!(names[1].node, "write_csv");
                    }
                    other => panic!("expected Named, got {other:?}"),
                }
            }
            other => panic!("expected Import, got {other:?}"),
        }
    }

    #[test]
    fn parse_import_named_trailing_comma() {
        let module = parse_mod("import Kea.Core.{read_csv,}");
        match &module.declarations[0].node {
            DeclKind::Import(decl) => {
                assert_eq!(decl.module.node, "Kea.Core");
                match &decl.items {
                    ImportItems::Named(names) => {
                        assert_eq!(names.len(), 1);
                        assert_eq!(names[0].node, "read_csv");
                    }
                    other => panic!("expected Named, got {other:?}"),
                }
            }
            other => panic!("expected Import, got {other:?}"),
        }
    }

    #[test]
    fn parse_import_with_fn_decl() {
        let module = parse_mod("import Kea.Core\nfn add(x, y) -> Int\n  x + y");
        assert_eq!(module.declarations.len(), 2);
        assert!(matches!(module.declarations[0].node, DeclKind::Import(_)));
        assert!(matches!(module.declarations[1].node, DeclKind::Function(_)));
    }

    // -- Actor operations --

    #[test]
    fn parse_spawn() {
        let expr = parse("spawn x");
        match &expr.node {
            ExprKind::Spawn { value: inner, .. } => {
                assert!(matches!(&inner.node, ExprKind::Var(name) if name == "x"));
            }
            other => panic!("expected Spawn, got {other:?}"),
        }
    }

    #[test]
    fn parse_spawn_record() {
        let expr = parse("spawn Counter { count: 0 }");
        match &expr.node {
            ExprKind::Spawn { value: inner, .. } => {
                assert!(
                    matches!(&inner.node, ExprKind::Record { name, .. } if name.node == "Counter")
                );
            }
            other => panic!("expected Spawn, got {other:?}"),
        }
    }

    #[test]
    fn parse_spawn_with_config() {
        let expr = parse("spawn Counter { count: 0 } with\n  mailbox_size: 100, max_restarts: 5");
        match &expr.node {
            ExprKind::Spawn { value, config } => {
                assert!(
                    matches!(&value.node, ExprKind::Record { name, .. } if name.node == "Counter")
                );
                let cfg = config.as_ref().expect("config should be present");
                assert!(cfg.mailbox_size.is_some(), "mailbox_size should be set");
                assert!(cfg.max_restarts.is_some(), "max_restarts should be set");
                assert!(cfg.supervision.is_none());
                assert!(cfg.call_timeout.is_none());
            }
            other => panic!("expected Spawn, got {other:?}"),
        }
    }

    #[test]
    fn parse_spawn_without_config() {
        // Regression: spawn without `with` still works
        let expr = parse("spawn x");
        match &expr.node {
            ExprKind::Spawn { config, .. } => {
                assert!(config.is_none(), "config should be None without `with`");
            }
            other => panic!("expected Spawn, got {other:?}"),
        }
    }

    #[test]
    fn parse_spawn_config_all_keys() {
        let expr = parse(
            "spawn x with\n  mailbox_size: 50, supervision: :restart, max_restarts: 10, call_timeout: 5000",
        );
        match &expr.node {
            ExprKind::Spawn { config, .. } => {
                let cfg = config.as_ref().expect("config should be present");
                assert!(cfg.mailbox_size.is_some());
                assert!(cfg.supervision.is_some());
                assert!(cfg.max_restarts.is_some());
                assert!(cfg.call_timeout.is_some());
            }
            other => panic!("expected Spawn, got {other:?}"),
        }
    }

    #[test]
    fn parse_spawn_supervisor_key_errors() {
        let errors = parse_err("spawn x with\n  supervisor: parent");
        assert!(!errors.is_empty(), "supervisor key should produce error");
        let msg = format!("{:?}", errors);
        assert!(
            msg.contains("supervisor") && msg.contains("removed"),
            "should mention supervisor is removed, got: {msg}"
        );
    }

    #[test]
    fn parse_spawn_unknown_key_errors() {
        let errors = parse_err("spawn x with\n  bad_key: 1");
        assert!(!errors.is_empty(), "unknown key should produce error");
        let msg = format!("{:?}", errors);
        assert!(msg.contains("unknown spawn config key"), "got: {msg}");
    }

    #[test]
    fn parse_stream_block() {
        let expr = parse("stream\n  yield 1");
        match &expr.node {
            ExprKind::StreamBlock { body, buffer_size } => {
                assert_eq!(*buffer_size, 32);
                match &body.node {
                    ExprKind::Yield { value } => {
                        assert!(matches!(&value.node, ExprKind::Lit(Lit::Int(1))));
                    }
                    other => panic!("expected Yield body, got {other:?}"),
                }
            }
            other => panic!("expected StreamBlock, got {other:?}"),
        }
    }

    #[test]
    fn parse_stream_block_with_buffer_config() {
        let expr = parse("stream\n  yield 1\nwith\n  buffer: 128");
        match &expr.node {
            ExprKind::StreamBlock { buffer_size, .. } => {
                assert_eq!(*buffer_size, 128);
            }
            other => panic!("expected StreamBlock, got {other:?}"),
        }
    }

    #[test]
    fn parse_stream_yield_from() {
        let expr = parse("stream\n  yield_from other");
        match &expr.node {
            ExprKind::StreamBlock { body, .. } => match &body.node {
                ExprKind::YieldFrom { source } => {
                    assert!(matches!(&source.node, ExprKind::Var(name) if name == "other"));
                }
                other => panic!("expected YieldFrom body, got {other:?}"),
            },
            other => panic!("expected StreamBlock, got {other:?}"),
        }
    }

    #[test]
    fn parse_stream_unknown_key_errors() {
        let errors = parse_err("stream\n  yield 1\nwith\n  bad_key: 1");
        assert!(!errors.is_empty(), "unknown key should produce error");
        let msg = format!("{:?}", errors);
        assert!(msg.contains("unknown stream config key"), "got: {msg}");
    }

    #[test]
    fn parse_for_simple_generator() {
        let expr = parse("for x in [1, 2, 3]\n  x + 1");
        match &expr.node {
            ExprKind::For(f) => {
                assert_eq!(f.clauses.len(), 1);
                match &f.clauses[0] {
                    ForClause::Generator { pattern, source } => {
                        assert!(matches!(&pattern.node, PatternKind::Var(name) if name == "x"));
                        assert!(matches!(&source.node, ExprKind::List(_)));
                    }
                    other => panic!("expected generator clause, got {other:?}"),
                }
                assert!(f.into_type.is_none());
            }
            other => panic!("expected For expression, got {other:?}"),
        }
    }

    #[test]
    fn parse_for_simple_generator_indented_body() {
        let expr = parse("for x in [1, 2, 3]\n  x + 1");
        match &expr.node {
            ExprKind::For(f) => {
                assert_eq!(f.clauses.len(), 1);
                assert!(f.into_type.is_none());
            }
            other => panic!("expected For expression, got {other:?}"),
        }
    }

    #[test]
    fn parse_for_generators_guards_and_into() {
        let expr = parse("for x in xs when x > 0, y in ys when y != x\n  #(x, y)\ninto Set");
        match &expr.node {
            ExprKind::For(f) => {
                assert_eq!(f.clauses.len(), 4);
                assert!(matches!(f.clauses[0], ForClause::Generator { .. }));
                assert!(matches!(f.clauses[1], ForClause::Guard(_)));
                assert!(matches!(f.clauses[2], ForClause::Generator { .. }));
                assert!(matches!(f.clauses[3], ForClause::Guard(_)));
                let into = f.into_type.as_ref().expect("expected into type");
                assert!(matches!(&into.node, TypeAnnotation::Named(name) if name == "Set"));
            }
            other => panic!("expected For expression, got {other:?}"),
        }
    }

    #[test]
    fn parse_for_pattern_generator_clause() {
        let expr = parse("for Ok(x) in results\n  x");
        match &expr.node {
            ExprKind::For(f) => match &f.clauses[0] {
                ForClause::Generator { pattern, .. } => match &pattern.node {
                    PatternKind::Constructor { name, args, .. } => {
                        assert_eq!(name, "Ok");
                        assert_eq!(args.len(), 1);
                    }
                    other => panic!("expected constructor pattern, got {other:?}"),
                },
                other => panic!("expected generator clause, got {other:?}"),
            },
            other => panic!("expected For expression, got {other:?}"),
        }
    }

    #[test]
    fn parse_use_with_binding_pattern() {
        let expr = parse("use value <- load()");
        match &expr.node {
            ExprKind::Use(u) => {
                match u.pattern.as_ref() {
                    Some(pattern) => {
                        assert!(matches!(&pattern.node, PatternKind::Var(name) if name == "value"));
                    }
                    None => panic!("expected binding pattern"),
                }
                assert!(matches!(&u.rhs.node, ExprKind::Call { .. }));
            }
            other => panic!("expected Use expression, got {other:?}"),
        }
    }

    #[test]
    fn parse_use_without_binding() {
        let expr = parse("use <- lock()");
        match &expr.node {
            ExprKind::Use(u) => {
                assert!(u.pattern.is_none());
                assert!(matches!(&u.rhs.node, ExprKind::Call { .. }));
            }
            other => panic!("expected Use expression, got {other:?}"),
        }
    }

    #[test]
    fn parse_use_requires_left_arrow() {
        let errors = parse_err("use value = lock()");
        let msg = format!("{errors:?}");
        assert!(msg.contains("expected '<-' in use expression"), "got {msg}");
    }

    #[test]
    fn parse_send_basic() {
        let expr = parse("send(actor, :increment)");
        match &expr.node {
            ExprKind::ActorSend {
                actor,
                method,
                args,
                safe,
            } => {
                assert!(matches!(&actor.node, ExprKind::Var(name) if name == "actor"));
                assert_eq!(method.node, "increment");
                assert!(args.is_empty());
                assert!(!safe);
            }
            other => panic!("expected ActorSend, got {other:?}"),
        }
    }

    #[test]
    fn parse_send_with_args() {
        let expr = parse("send(actor, :add, 1, 2)");
        match &expr.node {
            ExprKind::ActorSend {
                actor,
                method,
                args,
                safe,
            } => {
                assert!(matches!(&actor.node, ExprKind::Var(name) if name == "actor"));
                assert_eq!(method.node, "add");
                assert_eq!(args.len(), 2);
                assert!(!safe);
            }
            other => panic!("expected ActorSend, got {other:?}"),
        }
    }

    #[test]
    fn parse_send_message_form_desugars_to_handle() {
        let expr = parse("send(actor, Inc)");
        match &expr.node {
            ExprKind::ActorSend {
                method, args, safe, ..
            } => {
                assert_eq!(method.node, "handle");
                assert_eq!(args.len(), 1);
                assert!(
                    matches!(&args[0].node, ExprKind::Constructor { name, .. } if name.node == "Inc")
                );
                assert!(!safe);
            }
            other => panic!("expected ActorSend, got {other:?}"),
        }
    }

    #[test]
    fn parse_try_send_basic() {
        let expr = parse("try_send(actor, :push, 1)");
        match &expr.node {
            ExprKind::ActorSend {
                actor,
                method,
                args,
                safe,
            } => {
                assert!(matches!(&actor.node, ExprKind::Var(name) if name == "actor"));
                assert_eq!(method.node, "push");
                assert_eq!(args.len(), 1);
                assert!(*safe);
            }
            other => panic!("expected ActorSend, got {other:?}"),
        }
    }

    #[test]
    fn parse_try_send_message_form_desugars_to_handle() {
        let expr = parse("try_send(actor, Ping)");
        match &expr.node {
            ExprKind::ActorSend {
                method, args, safe, ..
            } => {
                assert_eq!(method.node, "handle");
                assert_eq!(args.len(), 1);
                assert!(*safe);
            }
            other => panic!("expected ActorSend, got {other:?}"),
        }
    }

    #[test]
    fn parse_send_safe_suffix_sets_safe_flag() {
        let expr = parse("send?(actor, Ping)");
        match &expr.node {
            ExprKind::ActorSend {
                method, args, safe, ..
            } => {
                assert_eq!(method.node, "handle");
                assert_eq!(args.len(), 1);
                assert!(*safe);
            }
            other => panic!("expected ActorSend, got {other:?}"),
        }
    }

    #[test]
    fn parse_call_basic() {
        let expr = parse("call(actor, :get_count)");
        match &expr.node {
            ExprKind::ActorCall {
                actor,
                method,
                args,
                safe,
            } => {
                assert!(matches!(&actor.node, ExprKind::Var(name) if name == "actor"));
                assert_eq!(method.node, "get_count");
                assert!(args.is_empty());
                assert!(!safe);
            }
            other => panic!("expected ActorCall, got {other:?}"),
        }
    }

    #[test]
    fn parse_call_with_args() {
        let expr = parse("call(actor, :get, \"key\")");
        match &expr.node {
            ExprKind::ActorCall {
                actor,
                method,
                args,
                safe,
            } => {
                assert!(matches!(&actor.node, ExprKind::Var(name) if name == "actor"));
                assert_eq!(method.node, "get");
                assert_eq!(args.len(), 1);
                assert!(!safe);
            }
            other => panic!("expected ActorCall, got {other:?}"),
        }
    }

    #[test]
    fn parse_call_message_form_desugars_to_handle() {
        let expr = parse("call(actor, Get)");
        match &expr.node {
            ExprKind::ActorCall {
                method, args, safe, ..
            } => {
                assert_eq!(method.node, "handle");
                assert_eq!(args.len(), 1);
                assert!(
                    matches!(&args[0].node, ExprKind::Constructor { name, .. } if name.node == "Get")
                );
                assert!(!safe);
            }
            other => panic!("expected ActorCall, got {other:?}"),
        }
    }

    #[test]
    fn parse_call_safe_suffix_sets_safe_flag() {
        let expr = parse("call?(actor, Get)");
        match &expr.node {
            ExprKind::ActorCall {
                method, args, safe, ..
            } => {
                assert_eq!(method.node, "handle");
                assert_eq!(args.len(), 1);
                assert!(*safe);
            }
            other => panic!("expected ActorCall, got {other:?}"),
        }
    }

    #[test]
    fn parse_send_trailing_comma() {
        let expr = parse("send(actor, :push, 42,)");
        match &expr.node {
            ExprKind::ActorSend { args, safe, .. } => {
                assert_eq!(args.len(), 1);
                assert!(!safe);
            }
            other => panic!("expected ActorSend, got {other:?}"),
        }
    }

    // -- Actor error paths --

    #[test]
    fn parse_send_missing_method_errors() {
        // send(actor) — missing comma + :method
        let errs = parse_err("send(actor)");
        assert!(!errs.is_empty(), "send without method should fail");
    }

    #[test]
    fn parse_send_message_form_with_extra_args_errors() {
        let errs = parse_err("send(actor, Inc, 1)");
        assert!(
            !errs.is_empty(),
            "message-style send with extra args should fail"
        );
    }

    #[test]
    fn parse_try_send_message_form_with_extra_args_errors() {
        let errs = parse_err("try_send(actor, Inc, 1)");
        assert!(
            !errs.is_empty(),
            "message-style try_send with extra args should fail"
        );
    }

    #[test]
    fn parse_call_missing_method_errors() {
        // call(actor) — missing comma + :method
        let errs = parse_err("call(actor)");
        assert!(!errs.is_empty(), "call without method should fail");
    }

    #[test]
    fn parse_send_missing_actor_errors() {
        // send(:method) — atom where actor expr expected, then missing comma before next
        let errs = parse_err("send(, :method)");
        assert!(!errs.is_empty(), "send without actor should fail");
    }

    // -- Atom expressions --

    #[test]
    fn parse_atom_expression() {
        let expr = parse(":foo");
        assert_eq!(expr.node, ExprKind::Atom("foo".into()));
    }

    #[test]
    fn parse_atom_in_function_call() {
        let expr = parse("f(:foo)");
        match &expr.node {
            ExprKind::Call { func, args } => {
                assert!(matches!(&func.node, ExprKind::Var(n) if n == "f"));
                assert_eq!(args.len(), 1);
                assert_eq!(args[0].value.node, ExprKind::Atom("foo".into()));
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn parse_atom_in_let_binding() {
        let expr = parse("let x = :bar");
        match &expr.node {
            ExprKind::Let { pattern, value, .. } => {
                assert_eq!(pattern.node.as_var(), Some("x"));
                assert_eq!(value.node, ExprKind::Atom("bar".into()));
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    #[test]
    fn parse_atom_multiple_args() {
        let expr = parse("f(:a, :b, :c)");
        match &expr.node {
            ExprKind::Call { args, .. } => {
                assert_eq!(args.len(), 3);
                assert_eq!(args[0].value.node, ExprKind::Atom("a".into()));
                assert_eq!(args[1].value.node, ExprKind::Atom("b".into()));
                assert_eq!(args[2].value.node, ExprKind::Atom("c".into()));
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn parse_call_with_labeled_args() {
        let expr = parse("sort(df, by: [:revenue], descending: true)");
        match &expr.node {
            ExprKind::Call { args, .. } => {
                assert_eq!(args.len(), 3);
                assert!(args[0].label.is_none());
                assert_eq!(args[1].label.as_ref().map(|s| s.node.as_str()), Some("by"));
                assert_eq!(
                    args[2].label.as_ref().map(|s| s.node.as_str()),
                    Some("descending")
                );
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn parse_call_rejects_positional_after_labeled() {
        let errors = parse_err("sort(df, by: [:revenue], true)");
        assert!(
            errors.iter().any(|d| d
                .message
                .contains("positional arguments must come before labeled")),
            "expected positional-after-labeled diagnostic, got {errors:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Sum type (type definition) tests
    // -----------------------------------------------------------------------

    #[test]
    fn parse_type_def_simple() {
        let module = parse_mod("type Color = Red | Green | Blue");
        assert_eq!(module.declarations.len(), 1);
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert!(!def.public);
                assert_eq!(def.name.node, "Color");
                assert!(def.params.is_empty());
                assert_eq!(def.variants.len(), 3);
                assert_eq!(def.variants[0].name.node, "Red");
                assert!(def.variants[0].fields.is_empty());
                assert_eq!(def.variants[1].name.node, "Green");
                assert_eq!(def.variants[2].name.node, "Blue");
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn parse_type_def_with_fields() {
        let module = parse_mod("type Shape = Circle(Float) | Rectangle(Float, Float)");
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert_eq!(def.name.node, "Shape");
                assert_eq!(def.variants.len(), 2);
                assert_eq!(def.variants[0].name.node, "Circle");
                assert_eq!(def.variants[0].fields.len(), 1);
                assert!(def.variants[0].where_clause.is_empty());
                assert_eq!(def.variants[1].name.node, "Rectangle");
                assert_eq!(def.variants[1].fields.len(), 2);
                assert!(def.variants[1].where_clause.is_empty());
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn parse_type_def_with_named_variant_fields() {
        let module = parse_mod("type Energy = Solar(capacity: Float, lat: Float, lon: Float)");
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert_eq!(def.variants.len(), 1);
                assert_eq!(def.variants[0].fields.len(), 3);
                assert_eq!(
                    def.variants[0].fields[0]
                        .name
                        .as_ref()
                        .map(|s| s.node.as_str()),
                    Some("capacity")
                );
                assert_eq!(
                    def.variants[0].fields[1]
                        .name
                        .as_ref()
                        .map(|s| s.node.as_str()),
                    Some("lat")
                );
                assert_eq!(
                    def.variants[0].fields[2]
                        .name
                        .as_ref()
                        .map(|s| s.node.as_str()),
                    Some("lon")
                );
            }
            other => panic!("expected TypeDef, got {other:?}"),
        }
    }

    #[test]
    fn parse_type_def_rejects_mixed_named_and_positional_variant_fields() {
        let errors = parse_mod_err("type Bad = Pair(left: Int, Int)");
        assert!(
            errors.iter().any(|d| {
                d.message.contains("cannot mix named and positional fields")
                    || d.message.contains("expected variant field name")
            }),
            "expected named/positional variant field diagnostic, got {errors:?}"
        );
    }

    #[test]
    fn parse_type_def_variant_where_clause() {
        let module =
            parse_mod("type Expr(T) = Lit(Int) where T = Int | IsZero(Expr(Int)) where T = Bool");
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert_eq!(def.name.node, "Expr");
                assert_eq!(def.params, vec!["T"]);
                assert_eq!(def.variants.len(), 2);
                assert_eq!(def.variants[0].name.node, "Lit");
                assert_eq!(def.variants[0].where_clause.len(), 1);
                assert_eq!(def.variants[0].where_clause[0].type_var.node, "T");
                assert_eq!(
                    def.variants[0].where_clause[0].ty.node,
                    TypeAnnotation::Named("Int".to_string())
                );
                assert_eq!(def.variants[1].name.node, "IsZero");
                assert_eq!(def.variants[1].where_clause.len(), 1);
                assert_eq!(def.variants[1].where_clause[0].type_var.node, "T");
                assert_eq!(
                    def.variants[1].where_clause[0].ty.node,
                    TypeAnnotation::Named("Bool".to_string())
                );
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn parse_type_def_with_derive() {
        let module = parse_mod("type Shape = Circle(Float) | Point deriving Eq, Hash");
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert_eq!(def.name.node, "Shape");
                assert_eq!(def.derives.len(), 2);
                assert_eq!(def.derives[0].node, "Eq");
                assert_eq!(def.derives[1].node, "Hash");
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn parse_type_def_with_params() {
        let module = parse_mod("type MyOption(T) = MySome(T) | MyNone");
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert_eq!(def.name.node, "MyOption");
                assert_eq!(def.params, vec!["T"]);
                assert_eq!(def.variants.len(), 2);
                assert_eq!(def.variants[0].name.node, "MySome");
                assert_eq!(def.variants[0].fields.len(), 1);
                assert_eq!(def.variants[1].name.node, "MyNone");
                assert!(def.variants[1].fields.is_empty());
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn parse_pub_type_def() {
        let module = parse_mod("pub type Direction = North | South | East | West");
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert!(def.public);
                assert_eq!(def.name.node, "Direction");
                assert_eq!(def.variants.len(), 4);
            }
            _ => panic!("expected TypeDef"),
        }
    }

    #[test]
    fn parse_type_def_leading_pipe() {
        let module = parse_mod("type Color =\n  | Red\n  | Green\n  | Blue");
        match &module.declarations[0].node {
            DeclKind::TypeDef(def) => {
                assert_eq!(def.name.node, "Color");
                assert_eq!(def.variants.len(), 3);
            }
            _ => panic!("expected TypeDef"),
        }
    }
}

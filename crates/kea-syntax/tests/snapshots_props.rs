use std::fmt::Write;

use insta::assert_snapshot;
use kea_ast::FileId;
use kea_diag::Diagnostic;
use kea_syntax::{TokenKind, lex_layout, parse_expr_source, parse_module_source, parse_type_source};
use proptest::prelude::*;

#[derive(Clone, Copy)]
enum ParseMode {
    Module,
    Expr,
    Type,
}

#[derive(Clone, Copy)]
struct ParseCase {
    name: &'static str,
    mode: ParseMode,
    source: &'static str,
}

#[test]
fn lexer_layout_snapshot_corpus() {
    let cases: [(&str, &str); 18] = [
        ("fn_decl", "fn add(x, y) -> Int\n  x + y"),
        ("if_else_block", "if ready\n  start()\nelse\n  wait()"),
        ("case_block", "case x\n  Some(v) -> v\n  _ -> 0"),
        ("cond_block", "cond\n  x > 0 -> x\n  _ -> 0"),
        ("record_decl", "record User\n  name: String\n  age: Int"),
        ("trait_decl", "trait Show\n  fn show(self) -> String"),
        ("impl_decl", "impl Show for Int\n  fn show(self) -> String\n    \"int\""),
        ("for_expr", "for x in xs when x > 0\n  x + 1"),
        ("use_expr", "use value <- load()"),
        ("spawn_with_config", "spawn Counter { count: 0 } with\n  mailbox_size: 100"),
        ("stream_with_config", "stream\n  yield 1\nwith\n  buffer: 128"),
        ("import_named", "import Kea.Core.{read_csv, write_csv}"),
        ("type_deriving", "type Result(a, e) = | Ok(a) | Err(e) deriving Eq"),
        ("anon_record", "#{ ..base, retries: 3, timeout: 30 }"),
        ("record_pattern", "case x\n  User { name, .. } -> name"),
        ("string_interp", "\"hello ${name}, total: ${1 + 2}\""),
        ("bare_brace_warning", "\"hello {name}\""),
        ("tab_indent_error", "fn bad() -> Int\n\t1"),
    ];

    let mut output = String::new();
    for (name, source) in cases {
        writeln!(&mut output, "## {name}").unwrap();
        writeln!(&mut output, "source:").unwrap();
        output.push_str(&render_source(source));
        writeln!(&mut output, "{}", render_lex_result(source)).unwrap();
    }

    assert_snapshot!("lexer_layout_corpus", output);
}

#[test]
fn parser_snapshot_corpus() {
    let cases: [ParseCase; 28] = [
        ParseCase {
            name: "module_fn_decl",
            mode: ParseMode::Module,
            source: "fn add(x, y) -> Int\n  x + y",
        },
        ParseCase {
            name: "module_fn_effect",
            mode: ParseMode::Module,
            source: "fn read() -[impure]> String\n  \"ok\"",
        },
        ParseCase {
            name: "module_expr_decl_testing",
            mode: ParseMode::Module,
            source:
                "expr double(x: Int) -> Int\n  x + x\ntesting\n  assert_eq double(3), 6",
        },
        ParseCase {
            name: "module_test_decl",
            mode: ParseMode::Module,
            source: "test \"basic\" tags [:fast, :unit]\n  assert true",
        },
        ParseCase {
            name: "module_record_deriving",
            mode: ParseMode::Module,
            source: "record Point\n  x: Int\n  y: Int\nderiving Eq, Display",
        },
        ParseCase {
            name: "module_type_named_variant",
            mode: ParseMode::Module,
            source: "type Event = | User(id: Int, name: String)",
        },
        ParseCase {
            name: "module_alias_parametric",
            mode: ParseMode::Module,
            source: "alias Handler(t) = fn(Request) -> Result(t, AppError)",
        },
        ParseCase {
            name: "module_opaque_deriving",
            mode: ParseMode::Module,
            source: "opaque UserId = Int deriving Eq, Display",
        },
        ParseCase {
            name: "module_trait_methods",
            mode: ParseMode::Module,
            source: "trait Additive\n  fn zero() -> Self\n  fn add(self, other: Self) -> Self",
        },
        ParseCase {
            name: "module_trait_associated_type",
            mode: ParseMode::Module,
            source:
                "trait From\n  type Source\n  fn from(value: Self.Source) -> Result(Self, String)",
        },
        ParseCase {
            name: "module_impl_where",
            mode: ParseMode::Module,
            source: "impl From for Int where Source = String\n  fn from(value) -> Int\n    0",
        },
        ParseCase {
            name: "module_import_named_alias",
            mode: ParseMode::Module,
            source: "import Kea.Core.{read_csv}\nimport Kea.Math as M",
        },
        ParseCase {
            name: "module_mixed_decls",
            mode: ParseMode::Module,
            source:
                "record Point\n  x: Float\n  y: Float\ntrait Additive\n  fn zero() -> Self\nimpl Additive for Point\n  fn zero() -> Int\n    0\nfn main() -> Int\n  1",
        },
        ParseCase {
            name: "expr_if_else",
            mode: ParseMode::Expr,
            source: "if x > 0\n  x\nelse\n  0",
        },
        ParseCase {
            name: "expr_case_nested",
            mode: ParseMode::Expr,
            source: "case x\n  Some(#(a, b)) -> a + b\n  _ -> 0",
        },
        ParseCase {
            name: "expr_cond",
            mode: ParseMode::Expr,
            source: "cond\n  x > 0 -> \"pos\"\n  _ -> \"neg\"",
        },
        ParseCase {
            name: "expr_lambda",
            mode: ParseMode::Expr,
            source: "|x| -> x + 1",
        },
        ParseCase {
            name: "expr_anon_record_spread",
            mode: ParseMode::Expr,
            source: "#{ ..base, retries: 3 }",
        },
        ParseCase {
            name: "expr_named_record",
            mode: ParseMode::Expr,
            source: "User { name: \"alice\", age: 30 }",
        },
        ParseCase {
            name: "expr_record_pattern",
            mode: ParseMode::Expr,
            source: "case x\n  User { name, .. } -> name",
        },
        ParseCase {
            name: "expr_for_generators_guards_into",
            mode: ParseMode::Expr,
            source: "for x in xs when x > 0, y in ys when y != x\n  #(x, y)\ninto Set",
        },
        ParseCase {
            name: "expr_use_binding",
            mode: ParseMode::Expr,
            source: "use value <- load()",
        },
        ParseCase {
            name: "expr_spawn_with_config",
            mode: ParseMode::Expr,
            source: "spawn Counter { count: 0 } with\n  mailbox_size: 100, max_restarts: 5",
        },
        ParseCase {
            name: "expr_stream_with_buffer",
            mode: ParseMode::Expr,
            source: "stream\n  yield 1\nwith\n  buffer: 128",
        },
        ParseCase {
            name: "expr_actor_send_message_form",
            mode: ParseMode::Expr,
            source: "send(actor, Inc)",
        },
        ParseCase {
            name: "expr_actor_call_safe",
            mode: ParseMode::Expr,
            source: "call?(actor, Get)",
        },
        ParseCase {
            name: "type_forall_effect_arrow",
            mode: ParseMode::Type,
            source: "forall a. fn(a) -[pure]> a",
        },
        ParseCase {
            name: "module_parse_error_missing_fn_body",
            mode: ParseMode::Module,
            source: "fn broken(x) -> Int",
        },
    ];

    let mut output = String::new();
    for case in cases {
        writeln!(&mut output, "## {}", case.name).unwrap();
        writeln!(&mut output, "source:").unwrap();
        output.push_str(&render_source(case.source));
        writeln!(&mut output, "{}", render_parse_case(case)).unwrap();
    }

    assert_snapshot!("parser_ast_corpus", output);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn prop_layout_random_indentation_is_well_formed(lines in prop::collection::vec((0u8..8, any::<bool>()), 1..32)) {
        let source = render_random_source_without_tabs(&lines);
        let result = lex_layout(&source, FileId(0));

        match result {
            Ok((tokens, warnings)) => {
                prop_assert!(!tokens.is_empty(), "tokens should never be empty");
                prop_assert!(matches!(tokens.last().map(|tok| &tok.kind), Some(TokenKind::Eof)));

                let mut depth = 0_i32;
                for tok in tokens {
                    match tok.kind {
                        TokenKind::Indent => depth += 1,
                        TokenKind::Dedent => {
                            depth -= 1;
                            prop_assert!(depth >= 0, "dedent cannot go below zero");
                        }
                        _ => {}
                    }
                }
                prop_assert_eq!(depth, 0, "indent and dedent counts must balance");
                assert_coherent_diagnostics(&warnings);
            }
            Err(diags) => {
                prop_assert!(!diags.is_empty(), "error diagnostics should be present");
                assert_coherent_diagnostics(&diags);
            }
        }
    }

    #[test]
    fn prop_tabs_in_indentation_report_coherent_error(prefix in prop::collection::vec(0u8..6, 0..8)) {
        let mut source = String::new();
        for indent in prefix {
            let _ = writeln!(&mut source, "{}x", " ".repeat(indent as usize));
        }
        source.push_str("fn bad() -> Int\n\t1\n");

        let result = lex_layout(&source, FileId(0));
        prop_assert!(result.is_err(), "tab-indented source should fail layout lexing");
        let diags = result.expect_err("tab-indented source should fail layout lexing");
        prop_assert!(
            diags
                .iter()
                .any(|d| d.message.contains("tabs are not allowed in indentation")),
            "expected tab-indentation diagnostic, got: {diags:?}"
        );
        assert_coherent_diagnostics(&diags);
    }
}

fn render_source(source: &str) -> String {
    let mut rendered = String::new();
    for line in source.split('\n') {
        let visible = line.replace('\t', "\\t").replace(' ', "·");
        let _ = writeln!(&mut rendered, "|{visible}");
    }
    rendered
}

fn render_lex_result(source: &str) -> String {
    let mut out = String::new();
    match lex_layout(source, FileId(0)) {
        Ok((tokens, warnings)) => {
            let _ = writeln!(&mut out, "status: ok");
            let _ = writeln!(&mut out, "tokens:");
            for token in tokens {
                let _ = writeln!(&mut out, "- {:?}", token.kind);
            }
            if warnings.is_empty() {
                let _ = writeln!(&mut out, "warnings: []");
            } else {
                let _ = writeln!(&mut out, "warnings:");
                out.push_str(&render_diagnostics(&warnings));
            }
        }
        Err(diags) => {
            let _ = writeln!(&mut out, "status: err");
            let _ = writeln!(&mut out, "errors:");
            out.push_str(&render_diagnostics(&diags));
        }
    }
    out
}

fn render_parse_case(case: ParseCase) -> String {
    match case.mode {
        ParseMode::Module => match parse_module_source(case.source, FileId(0)) {
            Ok(module) => {
                let mut decls = String::new();
                for (idx, decl) in module.declarations.iter().enumerate() {
                    if idx > 0 {
                        decls.push_str("\n---\n");
                    }
                    let _ = writeln!(&mut decls, "{:#?}", decl.node);
                }
                format!("status: ok\n{}", strip_span_and_location_blocks(&decls))
            }
            Err(diags) => format!("status: err\n{}", render_diagnostics(&diags)),
        },
        ParseMode::Expr => match parse_expr_source(case.source, FileId(0)) {
            Ok(expr) => {
                let rendered = format!("{:#?}", expr.node);
                format!(
                    "status: ok\n{}",
                    strip_span_and_location_blocks(&rendered)
                )
            }
            Err(diags) => format!("status: err\n{}", render_diagnostics(&diags)),
        },
        ParseMode::Type => match parse_type_source(case.source, FileId(0)) {
            Ok(ty) => {
                let rendered = format!("{:#?}", ty.node);
                format!(
                    "status: ok\n{}",
                    strip_span_and_location_blocks(&rendered)
                )
            }
            Err(diags) => format!("status: err\n{}", render_diagnostics(&diags)),
        },
    }
}

fn render_diagnostics(diags: &[Diagnostic]) -> String {
    let mut out = String::new();
    for diag in diags {
        let location = diag
            .location
            .map(|loc| format!("{}..{}", loc.start, loc.end))
            .unwrap_or_else(|| "-".to_string());
        let _ = writeln!(
            &mut out,
            "- {:?} {} @{}: {}",
            diag.severity,
            diag.code.as_deref().unwrap_or("-"),
            location,
            diag.message
        );
        if let Some(help) = &diag.help {
            let _ = writeln!(&mut out, "  help: {help}");
        }
    }
    out
}

fn strip_span_and_location_blocks(input: &str) -> String {
    let mut output = String::new();
    let mut skipping_block = false;
    let mut depth = 0_i32;

    for line in input.lines() {
        let trimmed = line.trim_start();
        if skipping_block {
            depth += brace_delta(line);
            if depth <= 0 {
                skipping_block = false;
                depth = 0;
            }
            continue;
        }

        if trimmed.starts_with("span: Span {")
            || trimmed.starts_with("location: Some(SourceLocation {")
            || trimmed.starts_with("location: SourceLocation {")
            || trimmed.starts_with("location: SourceLocation")
        {
            skipping_block = true;
            depth = brace_delta(line);
            if depth <= 0 {
                skipping_block = false;
                depth = 0;
            }
            continue;
        }

        if trimmed.starts_with("file: FileId(")
            || trimmed.starts_with("file_id:")
            || trimmed.starts_with("start:")
            || trimmed.starts_with("end:")
        {
            continue;
        }

        output.push_str(line);
        output.push('\n');
    }

    output
}

fn brace_delta(line: &str) -> i32 {
    let opens = line.chars().filter(|ch| *ch == '{').count() as i32;
    let closes = line.chars().filter(|ch| *ch == '}').count() as i32;
    opens - closes
}

fn render_random_source_without_tabs(lines: &[(u8, bool)]) -> String {
    let mut source = String::new();
    let mut has_content_line = false;

    for (indent, blank) in lines.iter().copied() {
        if blank {
            source.push('\n');
            continue;
        }
        has_content_line = true;
        let _ = writeln!(&mut source, "{}x", " ".repeat(indent as usize));
    }

    if !has_content_line {
        source.push_str("x\n");
    }

    source
}

fn assert_coherent_diagnostics(diags: &[Diagnostic]) {
    for diag in diags {
        assert!(
            !diag.message.trim().is_empty(),
            "diagnostic message should not be empty: {diag:?}"
        );
        if let Some(location) = diag.location {
            assert!(
                location.start <= location.end,
                "diagnostic location should be ordered: {diag:?}"
            );
        }
    }
}

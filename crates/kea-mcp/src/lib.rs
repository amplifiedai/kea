#![recursion_limit = "256"]
//! MCP server for Kea.
//!
//! Exposes type-checking tools over MCP stdio transport so agents can
//! validate Kea code and consume structured diagnostics.

use std::borrow::Cow;
use std::sync::{Arc, Mutex};

use kea::process_module_in_env;
use kea_ast::FileId;
use kea_diag::{Diagnostic, Severity};
use kea_infer::InferenceContext;
use kea_infer::typeck::{
    RecordRegistry, SumTypeRegistry, TraitRegistry, TypeEnv, infer_and_resolve_in_context,
};
use kea_syntax::{classify_as_declaration, lex_layout, parse_expr, parse_module};
use kea_types::{Type, sanitize_type_display};
use rmcp::model::*;
use rmcp::service::{RequestContext, RoleServer};
use rmcp::{ServerHandler, ServiceExt};

struct Session {
    type_env: TypeEnv,
    record_registry: RecordRegistry,
    trait_registry: TraitRegistry,
    sum_type_registry: SumTypeRegistry,
}

impl Session {
    fn new() -> Self {
        Self {
            type_env: TypeEnv::new(),
            record_registry: RecordRegistry::new(),
            trait_registry: TraitRegistry::new(),
            sum_type_registry: SumTypeRegistry::new(),
        }
    }

    fn reset(&mut self) {
        *self = Self::new();
    }
}

pub struct KeaMcpServer {
    session: Arc<Mutex<Session>>,
}

impl KeaMcpServer {
    pub fn new() -> Self {
        Self {
            session: Arc::new(Mutex::new(Session::new())),
        }
    }

    pub async fn serve_stdio(self) -> Result<(), Box<dyn std::error::Error>> {
        let transport = rmcp::transport::stdio();
        let service = self.serve(transport).await?;
        service.waiting().await?;
        Ok(())
    }

    fn dispatch_tool(
        &self,
        request: CallToolRequestParams,
    ) -> Result<CallToolResult, rmcp::ErrorData> {
        let args = request.arguments.unwrap_or_default();

        match request.name.as_ref() {
            "type_check" => {
                let code = get_code_arg(&args)?;
                let result = self.handle_type_check(&code);
                Ok(text_result(&result))
            }
            "diagnose" => {
                let code = get_code_arg(&args)?;
                let result = self.handle_diagnose(&code);
                Ok(text_result(&result))
            }
            "get_type" => {
                let code = get_code_arg(&args)?;
                let result = self.handle_get_type(&code);
                Ok(text_result(&result))
            }
            "reset_session" => {
                self.session.lock().unwrap().reset();
                Ok(text_result(
                    &serde_json::json!({
                        "status": "ok",
                        "message": "session reset"
                    })
                    .to_string(),
                ))
            }
            _ => Err(rmcp::ErrorData::new(
                ErrorCode::METHOD_NOT_FOUND,
                format!("unknown tool: {}", request.name),
                None,
            )),
        }
    }

    fn handle_type_check(&self, code: &str) -> String {
        let mut session = self.session.lock().unwrap();
        let result = type_check_code(&mut session, code);
        serde_json::to_string_pretty(&result).unwrap()
    }

    fn handle_diagnose(&self, code: &str) -> String {
        let session = self.session.lock().unwrap();
        let result = get_type_of(&session, code);
        let diagnostics = result
            .get("diagnostics")
            .cloned()
            .unwrap_or_else(|| serde_json::json!([]));
        serde_json::to_string_pretty(&serde_json::json!({
            "status": "ok",
            "diagnostics": diagnostics
        }))
        .unwrap()
    }

    fn handle_get_type(&self, code: &str) -> String {
        let session = self.session.lock().unwrap();
        let result = get_type_of(&session, code);
        serde_json::to_string_pretty(&result).unwrap()
    }
}

impl Default for KeaMcpServer {
    fn default() -> Self {
        Self::new()
    }
}

impl ServerHandler for KeaMcpServer {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: ProtocolVersion::V_2024_11_05,
            capabilities: ServerCapabilities {
                tools: Some(ToolsCapability::default()),
                ..Default::default()
            },
            server_info: Implementation {
                name: "kea-mcp".into(),
                version: env!("CARGO_PKG_VERSION").into(),
                ..Default::default()
            },
            instructions: Some(
                "Kea language MCP server. Use type_check to verify code and diagnose/get_type for structured analysis."
                    .into(),
            ),
        }
    }

    fn list_tools(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> impl std::future::Future<Output = Result<ListToolsResult, rmcp::ErrorData>> + Send + '_
    {
        std::future::ready(Ok(ListToolsResult {
            tools: vec![
                tool_type_check(),
                tool_diagnose(),
                tool_get_type(),
                tool_reset_session(),
            ],
            ..Default::default()
        }))
    }

    fn call_tool(
        &self,
        request: CallToolRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> impl std::future::Future<Output = Result<CallToolResult, rmcp::ErrorData>> + Send + '_
    {
        std::future::ready(self.dispatch_tool(request))
    }
}

fn make_tool(
    name: &'static str,
    description: &'static str,
    schema: serde_json::Map<String, serde_json::Value>,
) -> Tool {
    Tool {
        name: Cow::Borrowed(name),
        title: None,
        description: Some(Cow::Borrowed(description)),
        input_schema: Arc::new(schema),
        output_schema: None,
        annotations: None,
        icons: None,
        meta: None,
    }
}

fn tool_type_check() -> Tool {
    make_tool(
        "type_check",
        "Parse and type-check Kea code. Returns diagnostics on error, or 'ok' with inferred type information on success. Bindings persist in the session on success.",
        code_input_schema(),
    )
}

fn tool_diagnose() -> Tool {
    make_tool(
        "diagnose",
        "Type-check Kea code and return structured diagnostics (no session mutation).",
        code_input_schema(),
    )
}

fn tool_get_type() -> Tool {
    make_tool(
        "get_type",
        "Infer the type of Kea code without modifying session state.",
        code_input_schema(),
    )
}

fn tool_reset_session() -> Tool {
    make_tool(
        "reset_session",
        "Clear all session state (bindings and type registries).",
        empty_input_schema(),
    )
}

fn code_input_schema() -> serde_json::Map<String, serde_json::Value> {
    serde_json::from_value(serde_json::json!({
        "type": "object",
        "properties": {
            "code": {
                "type": "string",
                "description": "Kea source code"
            }
        },
        "required": ["code"]
    }))
    .unwrap()
}

fn empty_input_schema() -> serde_json::Map<String, serde_json::Value> {
    serde_json::from_value(serde_json::json!({
        "type": "object",
        "properties": {}
    }))
    .unwrap()
}

fn get_code_arg(
    args: &serde_json::Map<String, serde_json::Value>,
) -> Result<String, rmcp::ErrorData> {
    args.get("code")
        .and_then(|v| v.as_str())
        .map(|s| s.to_string())
        .ok_or_else(|| {
            rmcp::ErrorData::new(
                ErrorCode::INVALID_PARAMS,
                "missing required argument: code",
                None,
            )
        })
}

fn text_result(text: &str) -> CallToolResult {
    CallToolResult::success(vec![Content::text(text)])
}

fn diagnostics_json(diags: &[Diagnostic]) -> serde_json::Value {
    serde_json::json!({
        "status": "error",
        "diagnostics": diags
    })
}

fn context_errors_json(ctx: &InferenceContext) -> serde_json::Value {
    serde_json::json!({
        "status": "error",
        "diagnostics": ctx.errors()
    })
}

fn is_declaration(tokens: &[kea_syntax::Token]) -> bool {
    classify_as_declaration(tokens)
}

fn type_check_code(session: &mut Session, code: &str) -> serde_json::Value {
    let (tokens, warnings) = match lex_layout(code, FileId(0)) {
        Ok((tokens, warnings)) => (tokens, warnings),
        Err(diags) => return diagnostics_json(&diags),
    };

    if is_declaration(&tokens) {
        type_check_decls(session, tokens, warnings)
    } else {
        type_check_expr(session, tokens, warnings)
    }
}

fn type_check_expr(
    session: &mut Session,
    tokens: Vec<kea_syntax::Token>,
    mut diagnostics: Vec<Diagnostic>,
) -> serde_json::Value {
    let expr = match parse_expr(tokens, FileId(0)) {
        Ok(expr) => expr,
        Err(diags) => {
            diagnostics.extend(diags);
            return diagnostics_json(&diagnostics);
        }
    };

    let mut ctx = InferenceContext::new();
    let ty = infer_and_resolve_in_context(
        &expr,
        &mut session.type_env,
        &mut ctx,
        &session.record_registry,
        &session.trait_registry,
        &session.sum_type_registry,
    );

    if ctx.has_errors() {
        diagnostics.extend_from_slice(ctx.errors());
        return context_errors_json(&ctx);
    }

    ctx.check_trait_bounds(&session.trait_registry);
    if ctx.has_errors() {
        diagnostics.extend_from_slice(ctx.errors());
        return context_errors_json(&ctx);
    }

    diagnostics.extend(
        ctx.errors()
            .iter()
            .filter(|d| !matches!(d.severity, Severity::Error))
            .cloned(),
    );

    let mut result = serde_json::json!({
        "status": "ok",
        "type": sanitize_type_display(&ty)
    });
    if !diagnostics.is_empty() {
        result["diagnostics"] = serde_json::json!(diagnostics);
    }
    result
}

fn type_check_decls(
    session: &mut Session,
    tokens: Vec<kea_syntax::Token>,
    diagnostics: Vec<Diagnostic>,
) -> serde_json::Value {
    let module = match parse_module(tokens, FileId(0)) {
        Ok(module) => module,
        Err(diags) => return diagnostics_json(&diags),
    };

    let processed = match process_module_in_env(
        &module,
        &mut session.type_env,
        &mut session.record_registry,
        &mut session.trait_registry,
        &mut session.sum_type_registry,
        diagnostics,
    ) {
        Ok(processed) => processed,
        Err(diags) => return diagnostics_json(&diags),
    };

    let bindings_json = processed
        .bindings
        .iter()
        .map(|binding| {
            serde_json::json!({
                "name": binding.name,
                "kind": binding.kind,
                "type": binding.ty
            })
        })
        .collect::<Vec<_>>();

    let mut result = serde_json::json!({
        "status": "ok",
        "bindings": bindings_json
    });
    if !processed.diagnostics.is_empty() {
        result["diagnostics"] = serde_json::json!(processed.diagnostics);
    }
    result
}

fn get_type_of(session: &Session, code: &str) -> serde_json::Value {
    let (tokens, diagnostics) = match lex_layout(code, FileId(0)) {
        Ok((tokens, diagnostics)) => (tokens, diagnostics),
        Err(diags) => return diagnostics_json(&diags),
    };

    let mut env = session.type_env.clone();
    let mut records = session.record_registry.clone();
    let mut traits = session.trait_registry.clone();
    let mut sum_types = session.sum_type_registry.clone();

    if is_declaration(&tokens) {
        let module = match parse_module(tokens, FileId(0)) {
            Ok(module) => module,
            Err(diags) => return diagnostics_json(&diags),
        };

        let processed = match process_module_in_env(
            &module,
            &mut env,
            &mut records,
            &mut traits,
            &mut sum_types,
            diagnostics,
        ) {
            Ok(processed) => processed,
            Err(diags) => return diagnostics_json(&diags),
        };

        let ty = processed
            .bindings
            .last()
            .map(|binding| binding.ty.clone())
            .unwrap_or_else(|| sanitize_type_display(&Type::Unit));

        let mut result = serde_json::json!({
            "status": "ok",
            "type": ty
        });
        if !processed.diagnostics.is_empty() {
            result["diagnostics"] = serde_json::json!(processed.diagnostics);
        }
        return result;
    }

    let expr = match parse_expr(tokens, FileId(0)) {
        Ok(expr) => expr,
        Err(diags) => return diagnostics_json(&diags),
    };

    let mut ctx = InferenceContext::new();
    let ty = infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sum_types);

    if ctx.has_errors() {
        return context_errors_json(&ctx);
    }

    ctx.check_trait_bounds(&traits);
    if ctx.has_errors() {
        return context_errors_json(&ctx);
    }

    let mut all_diags = diagnostics;
    all_diags.extend(
        ctx.errors()
            .iter()
            .filter(|d| !matches!(d.severity, Severity::Error))
            .cloned(),
    );

    let mut result = serde_json::json!({
        "status": "ok",
        "type": sanitize_type_display(&ty)
    });
    if !all_diags.is_empty() {
        result["diagnostics"] = serde_json::json!(all_diags);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_json(text: &str) -> serde_json::Value {
        serde_json::from_str(text).expect("valid json")
    }

    #[test]
    fn type_check_expression_ok() {
        let server = KeaMcpServer::new();
        let text = server.handle_type_check("1 + 2");
        let value = parse_json(&text);
        assert_eq!(value["status"], "ok");
        assert_eq!(value["type"], "Int");
    }

    #[test]
    fn type_check_function_decl_persists_binding() {
        let server = KeaMcpServer::new();
        let first = parse_json(&server.handle_type_check("fn add(x: Int, y: Int) -> Int\n  x + y"));
        assert_eq!(first["status"], "ok");

        let second = parse_json(&server.handle_type_check("add(1, 2)"));
        assert_eq!(second["status"], "ok");
        assert_eq!(second["type"], "Int");
    }

    #[test]
    fn diagnose_returns_structured_diagnostics() {
        let server = KeaMcpServer::new();
        let value = parse_json(&server.handle_diagnose("1 + true"));
        assert_eq!(value["status"], "ok");

        let diagnostics = value["diagnostics"].as_array().expect("diagnostics array");
        assert!(!diagnostics.is_empty());
        let first = &diagnostics[0];

        assert!(first.get("code").is_some());
        assert!(first.get("severity").is_some());
        assert!(first.get("category").is_some());
        assert!(first.get("message").is_some());
    }

    #[test]
    fn get_type_does_not_mutate_session() {
        let server = KeaMcpServer::new();

        let get_type = parse_json(&server.handle_get_type("fn id(x: Int) -> Int\n  x"));
        assert_eq!(get_type["status"], "ok");

        let after = parse_json(&server.handle_type_check("id(1)"));
        assert_eq!(after["status"], "error");
    }

    #[test]
    fn type_check_effectful_function_keeps_declared_effect_row() {
        let server = KeaMcpServer::new();
        let code = "effect Log\n  fn log(msg: String) -> Unit\n\nfn write(msg: String) -[Log]> Unit\n  Log.log(msg)";
        let value = parse_json(&server.handle_type_check(code));
        assert_eq!(value["status"], "ok");

        let bindings = value["bindings"].as_array().expect("bindings array");
        let ty = bindings
            .iter()
            .find(|b| b["name"] == "write")
            .and_then(|b| b["type"].as_str())
            .expect("write binding type");

        assert!(
            ty.contains("-[Log]>") && !ty.contains("[IO]"),
            "expected Log effect row without phantom IO, got {ty}"
        );
    }

    #[test]
    fn reset_session_does_not_leave_phantom_io_on_pure_functions() {
        let server = KeaMcpServer::new();
        let _ = server.handle_type_check(
            "effect Log\n  fn log(msg: String) -> Unit\n\nfn write(msg: String) -[Log]> Unit\n  Log.log(msg)",
        );

        server.session.lock().unwrap().reset();

        let value = parse_json(&server.handle_type_check("fn id(x: Int) -> Int\n  x"));
        assert_eq!(value["status"], "ok");

        let bindings = value["bindings"].as_array().expect("bindings array");
        let ty = bindings
            .iter()
            .find(|b| b["name"] == "id")
            .and_then(|b| b["type"].as_str())
            .expect("id binding type");

        assert_eq!(ty, "(Int) -> Int");
    }

    #[test]
    fn type_check_let_bound_call_result_preserves_returned_callable_effect_row() {
        let server = KeaMcpServer::new();
        let code = "effect Emit\n  fn emit(val: Int) -> Unit\n\nfn make_emitter() -> fn(Int) -[Emit]> Unit\n  |x: Int| -> Emit.emit(x)\n\nfn trap() -> Unit\n  let f = make_emitter()\n  f(42)";
        let value = parse_json(&server.handle_type_check(code));
        assert_eq!(value["status"], "ok", "type_check response: {value}");

        let bindings = value["bindings"].as_array().expect("bindings array");
        let trap_ty = bindings
            .iter()
            .find(|b| b["name"] == "trap")
            .and_then(|b| b["type"].as_str())
            .expect("trap binding type");

        assert!(
            trap_ty.contains("-[Emit]>") && !trap_ty.contains("[IO]"),
            "expected trap to preserve Emit and avoid phantom IO, got {trap_ty}"
        );
    }

    #[test]
    fn type_check_direct_curried_call_preserves_returned_callable_effect_row() {
        let server = KeaMcpServer::new();
        let code = "effect Emit\n  fn emit(val: Int) -> Unit\n\nfn apply(f: fn(Int) -[Emit]> Unit) -> fn(Int) -[Emit]> Unit\n  f\n\nfn logger(x: Int) -[Emit]> Unit\n  Emit.emit(x)\n\nfn trap() -> Unit\n  apply(logger)(42)";
        let value = parse_json(&server.handle_type_check(code));
        assert_eq!(value["status"], "ok", "type_check response: {value}");

        let bindings = value["bindings"].as_array().expect("bindings array");
        let trap_ty = bindings
            .iter()
            .find(|b| b["name"] == "trap")
            .and_then(|b| b["type"].as_str())
            .expect("trap binding type");

        assert!(
            trap_ty.contains("-[Emit]>") && !trap_ty.contains("[IO]"),
            "expected trap to preserve Emit and avoid phantom IO, got {trap_ty}"
        );
    }

    #[test]
    fn type_check_curried_lambda_callback_propagates_effect_rows() {
        let server = KeaMcpServer::new();
        let code = "effect Log\n  fn log(msg: Int) -> Unit\n\nfn trap() -[Log]> Unit\n  let apply = |f| -> |x| -> f(x)\n  let logger = |y: Int| -> Log.log(y)\n  apply(logger)(42)";
        let value = parse_json(&server.handle_type_check(code));
        assert_eq!(value["status"], "ok", "type_check response: {value}");

        let bindings = value["bindings"].as_array().expect("bindings array");
        let trap_ty = bindings
            .iter()
            .find(|b| b["name"] == "trap")
            .and_then(|b| b["type"].as_str())
            .expect("trap binding type");

        assert!(
            trap_ty.contains("-[Log]>") && !trap_ty.contains("[IO]"),
            "expected trap to preserve Log and avoid phantom IO, got {trap_ty}"
        );
    }

    #[test]
    fn type_check_curried_annotated_lambda_callback_uses_effect_row_contract() {
        let server = KeaMcpServer::new();
        let code = "effect Log\n  fn log(msg: Int) -> Unit\n\nfn trap() -[Log]> Unit\n  let apply = |f: fn(Int) -[Log]> Unit| -> |x: Int| -> f(x)\n  let logger = |y: Int| -> Log.log(y)\n  apply(logger)(42)";
        let value = parse_json(&server.handle_type_check(code));
        assert_eq!(value["status"], "ok", "type_check response: {value}");

        let bindings = value["bindings"].as_array().expect("bindings array");
        let trap_ty = bindings
            .iter()
            .find(|b| b["name"] == "trap")
            .and_then(|b| b["type"].as_str())
            .expect("trap binding type");

        assert!(
            trap_ty.contains("-[Log]>") && !trap_ty.contains("[IO]"),
            "expected trap to preserve Log and avoid phantom IO, got {trap_ty}"
        );
    }
}

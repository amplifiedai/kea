//! MCP server for Kea.
//!
//! Exposes type-checking tools over MCP stdio transport so agents can
//! validate Kea code and consume structured diagnostics.

use std::borrow::Cow;
use std::sync::{Arc, Mutex};

use crate::process_module_in_env;
use kea_ast::FileId;
use kea_diag::{Diagnostic, ErrorRegistry, Severity};
use kea_infer::InferenceContext;
use kea_infer::typeck::{
    RecordRegistry, SumTypeRegistry, TraitGoal, TraitRegistry, TypeEnv,
    infer_and_resolve_in_context,
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
            "list_bindings" => Ok(text_result(&self.handle_list_bindings())),
            "explain_infer" => {
                let code = get_code_arg(&args)?;
                Ok(text_result(&self.handle_explain_infer(&code)))
            }
            "trace_unify" => {
                let code = get_code_arg(&args)?;
                Ok(text_result(&self.handle_trace_unify(&code)))
            }
            "resolve_traits" => Ok(text_result(&self.handle_resolve_traits())),
            "solve_trait" => {
                let ty = get_string_arg(&args, "type")?;
                let trait_name = get_string_arg(&args, "trait")?;
                Ok(text_result(&self.handle_solve_trait(&ty, &trait_name)))
            }
            "query_effects" => {
                let code = get_code_arg(&args)?;
                Ok(text_result(&self.handle_query_effects(&code)))
            }
            "list_effect_operations" => {
                let effect = get_string_arg(&args, "effect")?;
                Ok(text_result(&self.handle_list_effect_operations(&effect)))
            }
            "what_operations" => {
                let ty = get_string_arg(&args, "type")?;
                Ok(text_result(&self.handle_what_operations(&ty)))
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

    fn handle_list_bindings(&self) -> String {
        let session = self.session.lock().unwrap();
        let names = session.type_env.all_names_with_schemes();
        if names.is_empty() {
            return "No bindings in session. Run type_check first.".into();
        }
        names
            .iter()
            .map(|(name, scheme)| format!("{name}: {}", sanitize_type_display(&scheme.ty)))
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn handle_explain_infer(&self, code: &str) -> String {
        let session = self.session.lock().unwrap();
        let (tokens, diagnostics) = match lex_layout(code, FileId(0)) {
            Ok((t, d)) => (t, d),
            Err(diags) => return format_diagnostics_text(&diags),
        };
        if is_declaration(&tokens) {
            return "explain_infer works on expressions, not declarations.".into();
        }
        let expr = match parse_expr(tokens, FileId(0)) {
            Ok(e) => e,
            Err(diags) => {
                let mut all = diagnostics;
                all.extend(diags);
                return format_diagnostics_text(&all);
            }
        };
        let mut env = session.type_env.clone();
        let records = session.record_registry.clone();
        let traits = session.trait_registry.clone();
        let sum_types = session.sum_type_registry.clone();
        let mut ctx = InferenceContext::new();
        ctx.enable_constraint_capture();
        let _ty =
            infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sum_types);
        let constraints = ctx.take_captured_constraints();
        if constraints.is_empty() {
            return "No constraints captured.".into();
        }
        constraints
            .iter()
            .enumerate()
            .map(|(i, c)| format!("{}: {c:?}", i + 1))
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn handle_trace_unify(&self, code: &str) -> String {
        let session = self.session.lock().unwrap();
        let (tokens, diagnostics) = match lex_layout(code, FileId(0)) {
            Ok((t, d)) => (t, d),
            Err(diags) => return format_diagnostics_text(&diags),
        };
        if is_declaration(&tokens) {
            return "trace_unify works on expressions, not declarations.".into();
        }
        let expr = match parse_expr(tokens, FileId(0)) {
            Ok(e) => e,
            Err(diags) => {
                let mut all = diagnostics;
                all.extend(diags);
                return format_diagnostics_text(&all);
            }
        };
        let mut env = session.type_env.clone();
        let records = session.record_registry.clone();
        let traits = session.trait_registry.clone();
        let sum_types = session.sum_type_registry.clone();
        let mut ctx = InferenceContext::new();
        ctx.enable_tracing();
        let _ty =
            infer_and_resolve_in_context(&expr, &mut env, &mut ctx, &records, &traits, &sum_types);
        let steps = ctx.unify_trace();
        if steps.is_empty() {
            return "No unification steps recorded.".into();
        }
        steps
            .iter()
            .map(|s| {
                format!(
                    "step {}: {:?}  {} ~ {}  {}",
                    s.step, s.action, s.left, s.right, s.detail
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn handle_resolve_traits(&self) -> String {
        let session = self.session.lock().unwrap();
        let traits = session.trait_registry.all_traits();
        if traits.is_empty() {
            return "No traits in session. Run type_check first.".into();
        }
        traits
            .values()
            .map(|info| {
                let methods = info
                    .methods
                    .iter()
                    .map(|m| format!("  {}: {} -> {}", m.name, format_param_types(&m.param_types), sanitize_type_display(&m.return_type)))
                    .collect::<Vec<_>>()
                    .join("\n");
                if methods.is_empty() {
                    info.name.clone()
                } else {
                    format!("{}\n{methods}", info.name)
                }
            })
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    fn handle_solve_trait(&self, ty_str: &str, trait_name: &str) -> String {
        let session = self.session.lock().unwrap();
        // Parse the type expression to get a Type
        let (tokens, _) = match lex_layout(ty_str, FileId(0)) {
            Ok(r) => r,
            Err(diags) => return format_diagnostics_text(&diags),
        };
        let expr = match parse_expr(tokens, FileId(0)) {
            Ok(e) => e,
            Err(diags) => return format_diagnostics_text(&diags),
        };
        let mut env = session.type_env.clone();
        let records = session.record_registry.clone();
        let traits_reg = session.trait_registry.clone();
        let sum_types = session.sum_type_registry.clone();
        let mut ctx = InferenceContext::new();
        let ty = infer_and_resolve_in_context(
            &expr,
            &mut env,
            &mut ctx,
            &records,
            &traits_reg,
            &sum_types,
        );
        let goal = TraitGoal::Implements {
            trait_name: trait_name.to_string(),
            ty,
        };
        let outcome = session.trait_registry.solve_goal(&goal);
        format!("{outcome:?}")
    }

    fn handle_query_effects(&self, code: &str) -> String {
        let session = self.session.lock().unwrap();
        let result = get_type_of(&session, code);
        let ty_str = match result.get("type").and_then(|v| v.as_str()) {
            Some(s) => s.to_string(),
            None => return serde_json::to_string_pretty(&result).unwrap(),
        };
        // Extract effect row from function type display like "(A) -[E]> B"
        if let Some(start) = ty_str.find("-[")
            && let Some(end) = ty_str[start..].find("]>")
        {
            let effects = &ty_str[start + 2..start + end];
            return if effects.is_empty() {
                "Effects: (none — pure function)".into()
            } else {
                format!("Effects: [{effects}]")
            };
        }
        if ty_str.contains("->") {
            "Effects: (none — pure function)".into()
        } else {
            format!("Type: {ty_str} (not a function type)")
        }
    }

    fn handle_list_effect_operations(&self, effect_name: &str) -> String {
        let session = self.session.lock().unwrap();
        match session.type_env.effect_operation_names(effect_name) {
            Some(ops) if !ops.is_empty() => {
                let mut lines = vec![format!("Effect {effect_name}:")];
                for op in &ops {
                    // Try to get the type scheme for each operation
                    if let Some(scheme) = session.type_env.resolve_qualified(effect_name, op) {
                        lines.push(format!("  {op}: {}", sanitize_type_display(&scheme.ty)));
                    } else {
                        lines.push(format!("  {op}"));
                    }
                }
                lines.join("\n")
            }
            _ => format!("No effect named '{effect_name}' in session. Run type_check with an effect declaration first."),
        }
    }

    fn handle_what_operations(&self, type_name: &str) -> String {
        let session = self.session.lock().unwrap();
        let mut results: Vec<String> = Vec::new();

        // 1. Inherent methods
        let inherent = session.type_env.inherent_methods_for_type(type_name);
        if !inherent.is_empty() {
            results.push(format!("Inherent methods on {type_name}:"));
            for m in &inherent {
                results.push(format!("  .{m}()"));
            }
        }

        // 2. Module functions (UMS: first-param matches)
        let module_fns = session.type_env.module_function_names(type_name);
        if let Some(fns) = module_fns
            && !fns.is_empty()
        {
            results.push(format!("Module functions ({type_name}.method):"));
            for f in &fns {
                results.push(format!("  .{f}()"));
            }
        }

        // 3. Trait implementations
        let mut trait_methods: Vec<String> = Vec::new();
        for (trait_name, info) in session.trait_registry.all_traits() {
            for impl_info in session.trait_registry.all_impls() {
                if impl_info.trait_name == *trait_name && impl_info.type_name == type_name {
                    for m in &info.methods {
                        trait_methods.push(format!("  .{}()  [{trait_name}]", m.name));
                    }
                }
            }
        }
        if !trait_methods.is_empty() {
            results.push(format!("Trait implementations for {type_name}:"));
            results.extend(trait_methods);
        }

        if results.is_empty() {
            format!("No operations found for type '{type_name}'. Run type_check to populate the session.")
        } else {
            results.join("\n")
        }
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
                resources: Some(ResourcesCapability::default()),
                ..Default::default()
            },
            server_info: Implementation {
                name: "kea".into(),
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
                tool_list_bindings(),
                tool_explain_infer(),
                tool_trace_unify(),
                tool_resolve_traits(),
                tool_solve_trait(),
                tool_query_effects(),
                tool_list_effect_operations(),
                tool_what_operations(),
            ],
            ..Default::default()
        }))
    }

    fn list_resources(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> impl std::future::Future<Output = Result<ListResourcesResult, rmcp::ErrorData>> + Send + '_
    {
        let mut resources = vec![
            make_resource("kea://syntax", "Kea Syntax Reference", "Kea language syntax: indentation rules, case expressions, handle/resume, effect rows, lambdas, and operators."),
            make_resource("kea://types", "Kea Type System", "Kea type system overview: Hindley-Milner inference, row polymorphism, effect rows, traits, and UMS dispatch."),
            make_resource("kea://effects", "Kea Effect System", "Kea algebraic effects: effect declarations, handle blocks, resume, built-in effects (IO, Fail, State, Log, Rand)."),
            make_resource("kea://style", "Kea Idioms and Style", "Idiomatic Kea: dot syntax, Fail over Result, effects as capabilities, handlers at the boundary."),
            make_resource("kea://examples", "Kea Code Examples", "Canonical Kea examples: pure functions, effects, handlers, structs, enums, traits, and collections."),
            make_resource("kea://errors", "Kea Error Registry", "Index of all Kea diagnostic codes (E0001–E0017, E0801, W1001) with titles and descriptions."),
            make_resource("session://bindings", "Session Bindings", "All names currently bound in the type-check session with their inferred types."),
            make_resource("session://effects", "Session Effects", "Effect declarations and their operations currently registered in the session."),
            make_resource("session://traits", "Session Traits", "Trait definitions and implementations currently registered in the session."),
        ];
        // Add one resource per error code for direct lookup.
        let registry = ErrorRegistry::global();
        for entry in registry.all() {
            let uri = format!("kea://errors/{}", entry.code);
            let desc = format!("{} — {}", entry.title, &entry.description[..entry.description.len().min(100)]);
            resources.push(make_resource(&uri, &format!("{}: {}", entry.code, entry.name), &desc));
        }
        std::future::ready(Ok(ListResourcesResult {
            resources,
            ..Default::default()
        }))
    }

    fn read_resource(
        &self,
        request: ReadResourceRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> impl std::future::Future<Output = Result<ReadResourceResult, rmcp::ErrorData>> + Send + '_
    {
        let uri = request.uri.clone();
        let contents = match uri.as_str() {
            "kea://syntax" => text_resource_contents(&uri, KEA_SYNTAX_REFERENCE),
            "kea://types" => text_resource_contents(&uri, KEA_TYPES_REFERENCE),
            "kea://effects" => text_resource_contents(&uri, KEA_EFFECTS_REFERENCE),
            "kea://style" => text_resource_contents(&uri, KEA_STYLE_REFERENCE),
            "kea://examples" => text_resource_contents(&uri, KEA_EXAMPLES_REFERENCE),
            "session://bindings" => {
                let text = self.handle_list_bindings();
                text_resource_contents(&uri, &text)
            }
            "session://effects" => {
                let session = self.session.lock().unwrap();
                let text = format_session_effects(&session);
                text_resource_contents(&uri, &text)
            }
            "session://traits" => {
                let text = self.handle_resolve_traits();
                text_resource_contents(&uri, &text)
            }
            "kea://errors" => {
                let text = format_error_registry_index();
                text_resource_contents(&uri, &text)
            }
            _ if uri.starts_with("kea://errors/") => {
                let code = &uri["kea://errors/".len()..];
                let registry = ErrorRegistry::global();
                match registry.get(code) {
                    Some(entry) => {
                        let json = format_error_entry_json(entry);
                        text_resource_contents(&uri, &json)
                    }
                    None => {
                        return std::future::ready(Err(rmcp::ErrorData::new(
                            ErrorCode::INVALID_PARAMS,
                            format!("unknown error code: {code}"),
                            None,
                        )));
                    }
                }
            }
            _ => {
                return std::future::ready(Err(rmcp::ErrorData::new(
                    ErrorCode::INVALID_PARAMS,
                    format!("unknown resource URI: {uri}"),
                    None,
                )));
            }
        };
        std::future::ready(Ok(ReadResourceResult {
            contents: vec![contents],
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

pub async fn serve_mcp_stdio() -> Result<(), Box<dyn std::error::Error>> {
    KeaMcpServer::new().serve_stdio().await
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

fn tool_list_bindings() -> Tool {
    make_tool(
        "list_bindings",
        "List all names currently bound in the session with their inferred types. Requires a prior type_check call.",
        empty_input_schema(),
    )
}

fn tool_explain_infer() -> Tool {
    make_tool(
        "explain_infer",
        "Type-check a Kea expression and return the constraint system generated during inference. Useful for understanding why a type was inferred.",
        code_input_schema(),
    )
}

fn tool_trace_unify() -> Tool {
    make_tool(
        "trace_unify",
        "Type-check a Kea expression and return the step-by-step unification trace. Shows each unification decision.",
        code_input_schema(),
    )
}

fn tool_resolve_traits() -> Tool {
    make_tool(
        "resolve_traits",
        "List all trait definitions registered in the current session, with their method signatures.",
        empty_input_schema(),
    )
}

fn tool_solve_trait() -> Tool {
    make_tool(
        "solve_trait",
        "Check whether a given type implements a given trait. Returns Unique (found one impl), Ambiguous, or NoMatch.",
        string_pair_schema("type", "A Kea type expression, e.g. \"Int\" or \"List String\"", "trait", "Trait name, e.g. \"Show\" or \"Eq\""),
    )
}

fn tool_query_effects() -> Tool {
    make_tool(
        "query_effects",
        "Infer the type of a Kea expression and extract its effect row. Returns the list of effects the expression performs.",
        code_input_schema(),
    )
}

fn tool_list_effect_operations() -> Tool {
    make_tool(
        "list_effect_operations",
        "List all operations declared by a named effect in the current session.",
        single_string_schema("effect", "Effect name, e.g. \"Log\" or \"State\""),
    )
}

fn tool_what_operations() -> Tool {
    make_tool(
        "what_operations",
        "List all operations available on a type via dot syntax: inherent methods, module functions, and trait implementations.",
        single_string_schema("type", "Type name, e.g. \"List\" or \"String\""),
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

fn single_string_schema(
    param: &str,
    description: &str,
) -> serde_json::Map<String, serde_json::Value> {
    serde_json::from_value(serde_json::json!({
        "type": "object",
        "properties": {
            param: {
                "type": "string",
                "description": description
            }
        },
        "required": [param]
    }))
    .unwrap()
}

fn string_pair_schema(
    p1: &str,
    d1: &str,
    p2: &str,
    d2: &str,
) -> serde_json::Map<String, serde_json::Value> {
    serde_json::from_value(serde_json::json!({
        "type": "object",
        "properties": {
            p1: { "type": "string", "description": d1 },
            p2: { "type": "string", "description": d2 }
        },
        "required": [p1, p2]
    }))
    .unwrap()
}

fn get_code_arg(
    args: &serde_json::Map<String, serde_json::Value>,
) -> Result<String, rmcp::ErrorData> {
    get_string_arg(args, "code")
}

fn get_string_arg(
    args: &serde_json::Map<String, serde_json::Value>,
    key: &str,
) -> Result<String, rmcp::ErrorData> {
    args.get(key)
        .and_then(|v| v.as_str())
        .map(|s| s.to_string())
        .ok_or_else(|| {
            rmcp::ErrorData::new(
                ErrorCode::INVALID_PARAMS,
                format!("missing required argument: {key}"),
                None,
            )
        })
}

fn text_result(text: &str) -> CallToolResult {
    CallToolResult::success(vec![Content::text(text)])
}

fn make_resource(uri: &str, name: &str, description: &str) -> Resource {
    Resource::new(
        RawResource {
            uri: uri.to_string(),
            name: name.to_string(),
            title: None,
            description: Some(description.to_string()),
            mime_type: Some("text/plain".to_string()),
            size: None,
            icons: None,
            meta: None,
        },
        None,
    )
}

fn text_resource_contents(uri: &str, text: &str) -> ResourceContents {
    ResourceContents::TextResourceContents {
        uri: uri.to_string(),
        mime_type: Some("text/plain".to_string()),
        text: text.to_string(),
        meta: None,
    }
}

fn format_error_registry_index() -> String {
    let registry = ErrorRegistry::global();
    let mut out = String::from("# Kea Error Registry\n\n");
    out.push_str("All diagnostic codes with titles and severity.\n\n");
    for entry in registry.all() {
        let sev = match entry.severity {
            kea_diag::Severity::Error => "error",
            kea_diag::Severity::Warning => "warning",
            kea_diag::Severity::Info => "info",
        };
        out.push_str(&format!("- {} [{}] {}\n", entry.code, sev, entry.title));
    }
    out
}

fn format_error_entry_json(entry: &kea_diag::ErrorEntry) -> String {
    let related = entry
        .related
        .iter()
        .map(|s| format!("\"{}\"", s))
        .collect::<Vec<_>>()
        .join(", ");
    let example = match entry.example {
        Some(e) => format!("\"{}\"", e.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n")),
        None => "null".to_string(),
    };
    format!(
        "{{\n  \"code\": \"{code}\",\n  \"name\": \"{name}\",\n  \"title\": \"{title}\",\n  \"severity\": \"{sev}\",\n  \"description\": \"{desc}\",\n  \"example\": {example},\n  \"fix\": \"{fix}\",\n  \"related\": [{related}]\n}}",
        code = entry.code,
        name = entry.name,
        title = entry.title,
        sev = match entry.severity {
            kea_diag::Severity::Error => "error",
            kea_diag::Severity::Warning => "warning",
            kea_diag::Severity::Info => "info",
        },
        desc = entry.description.replace('"', "\\\""),
        fix = entry.fix.replace('"', "\\\""),
    )
}

fn format_param_types(types: &[kea_types::Type]) -> String {
    types
        .iter()
        .map(sanitize_type_display)
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_diagnostics_text(diags: &[Diagnostic]) -> String {
    diags
        .iter()
        .map(|d| format!("{:?}: {}", d.severity, d.message))
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_session_effects(session: &Session) -> String {
    // Collect known effect names from type env by looking at module function registry
    // and checking which are registered as effect operations
    let mut lines: Vec<String> = Vec::new();
    // We query a few common names — the API doesn't have "list all effects" yet,
    // so we report what we know is available via all_names
    let names = session.type_env.all_names_with_schemes();
    let effect_like: Vec<_> = names
        .iter()
        .filter(|(name, _)| {
            // Heuristic: effect modules have operations registered
            session.type_env.effect_operation_names(name).is_some_and(|ops| !ops.is_empty())
        })
        .collect();
    if effect_like.is_empty() {
        return "No effects in session. Run type_check with effect declarations first.".into();
    }
    for (name, _) in &effect_like {
        if let Some(ops) = session.type_env.effect_operation_names(name) {
            lines.push(format!("effect {name}:"));
            for op in &ops {
                if let Some(scheme) = session.type_env.resolve_qualified(name, op) {
                    lines.push(format!("  fn {op}: {}", sanitize_type_display(&scheme.ty)));
                } else {
                    lines.push(format!("  fn {op}"));
                }
            }
        }
    }
    lines.join("\n")
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

// =============================================================================
// Static language reference resources
// =============================================================================

const KEA_SYNTAX_REFERENCE: &str = "\
# Kea Syntax Reference

## Indentation

Kea uses indentation-sensitive syntax. Blocks are delimited by indentation level.
No braces. No semicolons.

## Function definitions

    fn add(x: Int, y: Int) -> Int
      x + y

    fn add_with_effects(x: Int) -[IO]> Int
      IO.stdout(\"computing\")
      x + 1

## Let bindings

    let x = 42
    let (a, b) = pair

## Case expressions

    case value
      Some(x) -> x + 1
      None -> 0

## Lambdas

    |x| x + 1
    |x: Int, y: Int| x + y

## Handle / resume (effects)

    handle some_effectful_call()
      EffectName.operation(arg) -> resume result_value

## Effect rows in types

    fn foo(x: Int) -[IO]> String      -- IO effect
    fn bar() -[IO, Log]> Unit          -- multiple effects
    fn baz(f: fn() -[e]> T) -[e]> T   -- polymorphic effect row

## Dot syntax (Universal Method Syntax)

    xs.map(f)            -- sugar for List.map(xs, f)
    xs.List.map(f)       -- qualified dispatch
    xs.map(_.field)      -- _ is receiver placeholder

## Structs and enums

    struct Point
      x: Float
      y: Float

    enum Option A
      None
      Some(A)
";

const KEA_TYPES_REFERENCE: &str = "\
# Kea Type System

## Primitive types

- `Int` — machine integer
- `Float` — 64-bit float
- `Bool` — true/false
- `String` — UTF-8 string
- `Unit` — ()

## Type constructors

- `List A` — homogeneous list
- `Option A` — optional value
- `(A, B)` — tuple
- `fn(A) -> B` — pure function
- `fn(A) -[E]> B` — effectful function with effect row E

## Type inference

Kea uses Hindley-Milner inference. Types are inferred without annotation
in most positions. Annotate at module boundaries for documentation.

## Row polymorphism

Effect rows use Rémy-style row polymorphism:

    fn run(f: fn() -[Log, e]> T) -[e]> T
    -- e is a row variable — any other effects pass through

## Traits

    trait Show A
      fn show(x: A) -> String

Implemented via `as Show` in struct/enum declarations.

## Kinds

- `*` — a type (Int, String, List Int)
- `* -> *` — a type constructor (List, Option)
- `Eff` — an effect label (IO, Log)
";

const KEA_EFFECTS_REFERENCE: &str = "\
# Kea Effect System

## Declaring effects

    effect Log
      fn info(msg: String) -> Unit
      fn warn(msg: String) -> Unit

    effect State S
      fn get() -> S
      fn put(s: S) -> Unit

## Using effects

Declare effects in function signatures:

    fn process() -[Log, IO]> Unit
      Log.info(\"starting\")

## Handling effects

    handle some_call()
      Log.info(msg) ->
        IO.stdout(msg)
        resume ()
      Log.warn(msg) ->
        IO.stdout(\"WARN: \" + msg)
        resume ()

## Built-in effects

- `IO` — stdout/stderr output
- `Fail E` — typed failure (like exceptions)
- `State S` — mutable state cell
- `Log` — structured logging
- `Rand` — random number generation
- `Net` — network I/O

## Fail effect

    fn divide(a: Int, b: Int) -[Fail String]> Int
      if b == 0
        Fail.fail(\"division by zero\")
      else
        a / b

    -- At the boundary:
    case catch divide(10, 0)
      Ok(result) -> result
      Err(msg) -> 0
";

const KEA_STYLE_REFERENCE: &str = "\
# Kea Idioms and Style

## Prefer Fail over Result

Use `Fail E` effect for errors, not `Result A E`. Effects compose;
Result nesting doesn't.

    fn parse(s: String) -[Fail ParseError]> Int
      ...

## Effects are capabilities

A function's effect row is its capability declaration. Pure functions have
no row. Effectful functions declare exactly what they need.

## Handlers at the boundary

Install handlers at the outermost scope — entry points, test boundaries.
Business logic uses effects; infrastructure wires the handlers.

## Dot syntax over pipe

    xs.map(f).filter(g)   -- not f |> map vs |> filter

## Use _ for receiver placement

    xs.map(_.name)   -- sugar for |x| x.name

## Case over nested if

    case colour
      Red -> 0
      Green -> 1
      Blue -> 2

## Doc comments

Use `doc` blocks on every public function. No // comments for docs.
";

const KEA_EXAMPLES_REFERENCE: &str = "\
# Kea Code Examples

## Pure function

    fn factorial(n: Int) -> Int
      if n <= 1
        1
      else
        n * factorial(n - 1)

## Effect usage

    fn greet(name: String) -[IO]> Unit
      IO.stdout(\"Hello, \" + name + \"!\")

## Effect handler

    fn main() -[IO]> Unit
      Log.with_stdout_logger(||
        run_server()
      )

## Struct with method

    struct Counter
      value: Int

      pub fn increment(self: Counter) -> Counter
        Counter { value: self.value + 1 }

## Enum pattern match

    fn describe(opt: Option Int) -> String
      case opt
        None -> \"nothing\"
        Some(n) -> \"got \" + Int.to_string(n)

## Trait implementation

    as Show for Int
      fn show(x: Int) -> String
        Int.to_string(x)

## Collecting a stream

    Stream.collect(||
      Stream.chunk(1)
      Stream.chunk(2)
      Stream.chunk(3)
      Stream.done()
    )
    -- => [1, 2, 3]

## Log with test handler

    Log.with_collected_logs(||
      Log.info(\"a\")
      Log.info(\"b\")
    )
    -- => ((), [\"a\", \"b\"])
";

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
        let code = "effect Emit\n  fn emit(val: Int) -> Unit\n\nfn make_emitter() -> fn(Int) -[Emit]> Unit\n  |x: Int| Emit.emit(x)\n\nfn trap() -[Emit]> Unit\n  let f = make_emitter()\n  f(42)";
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
        let code = "effect Emit\n  fn emit(val: Int) -> Unit\n\nfn apply(f: fn(Int) -[Emit]> Unit) -> fn(Int) -[Emit]> Unit\n  f\n\nfn logger(x: Int) -[Emit]> Unit\n  Emit.emit(x)\n\nfn trap() -[Emit]> Unit\n  apply(logger)(42)";
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
        let code = "effect Log\n  fn log(msg: Int) -> Unit\n\nfn trap() -[Log]> Unit\n  let apply = |f| |x| f(x)\n  let logger = |y: Int| Log.log(y)\n  apply(logger)(42)";
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
        let code = "effect Log\n  fn log(msg: Int) -> Unit\n\nfn trap() -[Log]> Unit\n  let apply = |f: fn(Int) -[Log]> Unit| |x: Int| f(x)\n  let logger = |y: Int| Log.log(y)\n  apply(logger)(42)";
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
    fn type_check_parameterized_effect_handler_resume_value() {
        let server = KeaMcpServer::new();
        let code = "effect Reader C\n  fn ask() -> C\n\nfn read() -[Reader Int]> Int\n  Reader.ask()\n\nfn main() -> Int\n  handle read()\n    Reader.ask() -> resume 42\n";
        let value = parse_json(&server.handle_type_check(code));
        assert_eq!(
            value["status"], "ok",
            "parameterized effect handler should type-check, got: {value}"
        );
    }
}

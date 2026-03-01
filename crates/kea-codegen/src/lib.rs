//! Backend interface and Cranelift backend scaffold for Kea MIR.
//!
//! This crate defines the backend contract for 0d and provides a first
//! Cranelift-backed implementor. The API is backend-neutral: backends consume
//! MIR + ABI manifest + target config and return code artifacts,
//! diagnostics, and machine-readable pass stats.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CStr, CString};
use std::fs;
use std::io::{Read, Write};
use std::net::TcpStream;
use std::os::raw::c_char;
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use cranelift::prelude::{
    AbiParam, Configurable, FunctionBuilder, FunctionBuilderContext, InstBuilder, Value, types,
};
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::{MemFlags, TrapCode};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::{isa, settings};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use kea_hir::HirModule;
use kea_mir::{
    MirBinaryOp, MirBlockId, MirCallee, MirEffectOpClass, MirFunction, MirInst, MirLiteral,
    MirModule, MirTerminator, MirUnaryOp, MirValueId, lower_hir_module,
};
use kea_types::{EffectRow, FloatWidth, IntWidth, RecordType, Signedness, SumType, Type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendConfig {
    pub target_triple: String,
    pub opt_level: OptimizationLevel,
    pub mode: CodegenMode,
}

impl Default for BackendConfig {
    fn default() -> Self {
        Self {
            target_triple: "host".to_string(),
            opt_level: OptimizationLevel::Default,
            mode: CodegenMode::Jit,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationLevel {
    None,
    Default,
    Aggressive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodegenMode {
    Jit,
    Aot,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiManifest {
    pub functions: BTreeMap<String, AbiFunctionSignature>,
}

impl AbiManifest {
    pub fn get(&self, name: &str) -> Option<&AbiFunctionSignature> {
        self.functions.get(name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiFunctionSignature {
    pub param_classes: Vec<AbiParamClass>,
    pub return_style: AbiReturnStyle,
    pub effect_evidence: AbiEffectEvidencePlacement,
    pub effects: EffectRow,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbiParamClass {
    Value,
    Ref,
    Evidence,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbiReturnStyle {
    Value,
    SRet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbiEffectEvidencePlacement {
    None,
    TrailingParam,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendArtifact {
    pub object: Vec<u8>,
    pub stats: PassStats,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PassStats {
    pub per_function: Vec<FunctionPassStats>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FunctionPassStats {
    pub function: String,
    pub retain_count: usize,
    pub release_count: usize,
    pub alloc_count: usize,
    pub reuse_count: usize,
    pub reuse_token_produced_count: usize,
    pub reuse_token_consumed_count: usize,
    pub reuse_token_candidate_count: usize,
    pub trmc_candidate_count: usize,
    pub tail_self_call_count: usize,
    pub handler_enter_count: usize,
    pub handler_exit_count: usize,
    pub resume_count: usize,
    pub effect_op_direct_count: usize,
    pub effect_op_dispatch_count: usize,
    pub effect_op_zero_resume_count: usize,
}

#[derive(Debug, thiserror::Error, Clone, PartialEq, Eq)]
pub enum CodegenError {
    #[error("ABI manifest missing function `{function}`")]
    MissingAbiEntry { function: String },
    #[error(
        "ABI manifest parameter class count mismatch for `{function}`: expected {expected}, got {actual}"
    )]
    AbiParamCountMismatch {
        function: String,
        expected: usize,
        actual: usize,
    },
    #[error("target triple `{target}` is not yet supported by this backend")]
    UnsupportedTarget { target: String },
    #[error("unsupported Kea type in Cranelift lowering: `{ty}`")]
    UnsupportedType { ty: String },
    #[error("unsupported MIR operation in `{function}`: {detail}")]
    UnsupportedMir { function: String, detail: String },
    #[error("invalid MIR value `%{value}` referenced in `{function}`")]
    InvalidMirValue { function: String, value: u32 },
    #[error("unknown function `{function}`")]
    UnknownFunction { function: String },
    #[error("Cranelift module error: {detail}")]
    Module { detail: String },
    #[error("Cranelift object emission failed: {detail}")]
    ObjectEmit { detail: String },
    #[error("duplicate type layout declaration `{name}`")]
    DuplicateLayoutType { name: String },
    #[error("duplicate field `{field}` in record layout `{type_name}`")]
    DuplicateLayoutField { type_name: String, field: String },
    #[error("duplicate variant `{variant}` in sum layout `{type_name}`")]
    DuplicateLayoutVariant { type_name: String, variant: String },
    #[error("sum layout `{type_name}` must use contiguous tags starting at 0")]
    InvalidLayoutVariantTags { type_name: String },
    #[error("Fail-only lowering invariant violated in `{function}`: {detail}")]
    FailOnlyInvariantViolation { function: String, detail: String },
}

pub trait Backend {
    fn name(&self) -> &'static str;

    fn compile_module(
        &self,
        module: &MirModule,
        abi: &AbiManifest,
        config: &BackendConfig,
    ) -> Result<BackendArtifact, CodegenError>;
}

pub fn compile_hir_module<B: Backend>(
    backend: &B,
    hir: &HirModule,
    config: &BackendConfig,
) -> Result<BackendArtifact, CodegenError> {
    let mir = lower_hir_module(hir);
    let abi = default_abi_manifest(&mir);
    backend.compile_module(&mir, &abi, config)
}

pub fn execute_hir_main_jit(hir: &HirModule, config: &BackendConfig) -> Result<i32, CodegenError> {
    let mir = lower_hir_module(hir);
    execute_mir_main_jit(&mir, config)
}

#[derive(Debug, Default)]
pub struct CraneliftBackend;

impl Backend for CraneliftBackend {
    fn name(&self) -> &'static str {
        "cranelift"
    }

    fn compile_module(
        &self,
        module: &MirModule,
        abi: &AbiManifest,
        config: &BackendConfig,
    ) -> Result<BackendArtifact, CodegenError> {
        validate_abi_manifest(module, abi)?;
        validate_layout_catalog(module)?;
        validate_fail_only_invariants(module)?;
        let layout_plan = plan_layout_catalog(module)?;

        let isa = build_isa(config)?;
        let stats = collect_pass_stats(module);
        let object = match config.mode {
            CodegenMode::Jit => compile_with_jit(module, &layout_plan, &isa, config)?,
            CodegenMode::Aot => compile_with_object(module, &layout_plan, &isa, config)?,
        };

        Ok(BackendArtifact { object, stats })
    }
}

fn build_isa(config: &BackendConfig) -> Result<Arc<dyn isa::TargetIsa>, CodegenError> {
    let mut flag_builder = settings::builder();
    flag_builder
        .set("opt_level", opt_level_setting(config.opt_level))
        .map_err(|detail| CodegenError::Module {
            detail: detail.to_string(),
        })?;
    // Cranelift's x64 `return_call` lowering currently relies on frame pointers.
    // Keep them enabled so tail-recursive self calls compile across CI targets.
    flag_builder
        .set("preserve_frame_pointers", "true")
        .map_err(|detail| CodegenError::Module {
            detail: detail.to_string(),
        })?;
    if matches!(config.mode, CodegenMode::Aot) {
        flag_builder
            .set("is_pic", "true")
            .map_err(|detail| CodegenError::Module {
                detail: detail.to_string(),
            })?;
        flag_builder
            .set("use_colocated_libcalls", "false")
            .map_err(|detail| CodegenError::Module {
                detail: detail.to_string(),
            })?;
    }

    if config.target_triple == "host" {
        let isa_builder = cranelift_native::builder().map_err(|detail| CodegenError::Module {
            detail: format!("host ISA not supported: {detail}"),
        })?;
        return isa_builder
            .finish(settings::Flags::new(flag_builder))
            .map_err(|detail| CodegenError::Module {
                detail: detail.to_string(),
            });
    }

    Err(CodegenError::UnsupportedTarget {
        target: config.target_triple.clone(),
    })
}

fn opt_level_setting(level: OptimizationLevel) -> &'static str {
    match level {
        OptimizationLevel::None => "none",
        OptimizationLevel::Default => "speed",
        OptimizationLevel::Aggressive => "speed_and_size",
    }
}

#[derive(Debug, Clone)]
struct RuntimeFunctionSig {
    runtime_params: Vec<Type>,
    logical_return: Type,
    runtime_return: Type,
    fail_result_abi: bool,
}

fn fail_payload_type(row: &EffectRow) -> Option<Type> {
    row.row
        .fields
        .iter()
        .find(|(label, _)| label.as_str() == "Fail")
        .map(|(_, payload)| payload.clone())
}

fn runtime_function_signature(function: &MirFunction) -> RuntimeFunctionSig {
    if is_fail_only_effect_row(&function.signature.effects)
        && !matches!(function.signature.ret, Type::Result(_, _))
        && let Some(err_ty) = fail_payload_type(&function.signature.effects)
    {
        return RuntimeFunctionSig {
            runtime_params: function.signature.params.clone(),
            logical_return: function.signature.ret.clone(),
            runtime_return: Type::Result(
                Box::new(function.signature.ret.clone()),
                Box::new(err_ty),
            ),
            fail_result_abi: true,
        };
    }

    RuntimeFunctionSig {
        runtime_params: function.signature.params.clone(),
        logical_return: function.signature.ret.clone(),
        runtime_return: function.signature.ret.clone(),
        fail_result_abi: false,
    }
}

fn runtime_signature_map(module: &MirModule) -> BTreeMap<String, RuntimeFunctionSig> {
    module
        .functions
        .iter()
        .map(|function| (function.name.clone(), runtime_function_signature(function)))
        .collect()
}

struct DirectCapabilitySpec {
    effect: &'static str,
    operations: &'static [&'static str],
}

const DIRECT_CAPABILITIES: &[DirectCapabilitySpec] = &[
    DirectCapabilitySpec {
        effect: "IO",
        operations: &["stdout", "stderr", "read_file", "write_file"],
    },
    DirectCapabilitySpec {
        effect: "Clock",
        operations: &["now", "monotonic"],
    },
    DirectCapabilitySpec {
        effect: "Rand",
        operations: &["int", "seed"],
    },
    DirectCapabilitySpec {
        effect: "Net",
        operations: &["connect", "send", "recv"],
    },
];

fn is_known_direct_capability_operation(effect: &str, operation: &str) -> bool {
    DIRECT_CAPABILITIES
        .iter()
        .find(|capability| capability.effect == effect)
        .is_some_and(|capability| capability.operations.contains(&operation))
}

fn is_direct_capability_effect(effect: &str) -> bool {
    DIRECT_CAPABILITIES
        .iter()
        .any(|capability| capability.effect == effect)
}

unsafe extern "C" fn kea_net_connect_stub(addr: *const c_char) -> i64 {
    if addr.is_null() {
        return -1;
    }
    let Ok(addr) = (unsafe { CStr::from_ptr(addr) }).to_str() else {
        return -1;
    };
    let Ok(stream) = TcpStream::connect(addr) else {
        return -1;
    };
    let _ = stream.set_nodelay(true);
    let Ok(mut runtime) = net_runtime().lock() else {
        return -1;
    };
    let connection_id = runtime.next_id;
    runtime.next_id = runtime.next_id.saturating_add(1);
    runtime.connections.insert(connection_id, stream);
    connection_id
}

unsafe extern "C" fn kea_net_send_stub(conn: i64, data: *const c_char) -> i8 {
    if data.is_null() {
        return -1;
    }
    let payload = unsafe { CStr::from_ptr(data) }.to_bytes();
    let Ok(mut runtime) = net_runtime().lock() else {
        return -1;
    };
    let Some(stream) = runtime.connections.get_mut(&conn) else {
        return -1;
    };
    match stream.write_all(payload) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

unsafe extern "C" fn kea_net_recv_stub(conn: i64, size: i64) -> i64 {
    if size <= 0 {
        return 0;
    }
    let Ok(mut runtime) = net_runtime().lock() else {
        return -1;
    };
    let Some(stream) = runtime.connections.get_mut(&conn) else {
        return -1;
    };
    let mut buffer = vec![0u8; size as usize];
    match stream.read(&mut buffer) {
        Ok(read) => read as i64,
        Err(_) => -1,
    }
}

unsafe extern "C" fn kea_io_write_file_stub(path: *const c_char, data: *const c_char) -> i8 {
    if path.is_null() || data.is_null() {
        return -1;
    }
    let Ok(path) = (unsafe { CStr::from_ptr(path) }).to_str() else {
        return -1;
    };
    let bytes = unsafe { CStr::from_ptr(data) }.to_bytes();
    match fs::write(path, bytes) {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

unsafe extern "C" fn kea_io_read_file_stub(path: *const c_char) -> *const c_char {
    static EMPTY: &[u8] = b"\0";
    if path.is_null() {
        EMPTY.as_ptr() as *const c_char
    }
    else {
        let Ok(path) = (unsafe { CStr::from_ptr(path) }).to_str() else {
            return EMPTY.as_ptr() as *const c_char;
        };
        let Ok(contents) = fs::read_to_string(path) else {
            return EMPTY.as_ptr() as *const c_char;
        };
        match CString::new(contents) {
            Ok(cstring) => cstring.into_raw(),
            Err(_) => EMPTY.as_ptr() as *const c_char,
        }
    }
}

unsafe extern "C" fn kea_clock_now_stub() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos() as i64)
        .unwrap_or(0)
}

unsafe extern "C" fn kea_clock_monotonic_stub() -> i64 {
    static START: OnceLock<Instant> = OnceLock::new();
    let start = START.get_or_init(Instant::now);
    let nanos = start.elapsed().as_nanos() as i64;
    if nanos <= 0 { 1 } else { nanos }
}

#[derive(Default)]
struct NetRuntimeState {
    next_id: i64,
    connections: BTreeMap<i64, TcpStream>,
}

fn net_runtime() -> &'static Mutex<NetRuntimeState> {
    static RUNTIME: OnceLock<Mutex<NetRuntimeState>> = OnceLock::new();
    RUNTIME.get_or_init(|| {
        Mutex::new(NetRuntimeState {
            next_id: 1,
            connections: BTreeMap::new(),
        })
    })
}

unsafe extern "C" fn kea_panic_div_zero_stub() -> ! {
    eprintln!("panic: integer division by zero");
    std::process::exit(101);
}

unsafe extern "C" fn kea_panic_mod_zero_stub() -> ! {
    eprintln!("panic: integer remainder by zero");
    std::process::exit(101);
}

fn register_jit_runtime_symbols(builder: &mut JITBuilder) {
    builder.symbol("__kea_net_connect", kea_net_connect_stub as *const u8);
    builder.symbol("__kea_net_send", kea_net_send_stub as *const u8);
    builder.symbol("__kea_net_recv", kea_net_recv_stub as *const u8);
    builder.symbol("__kea_io_write_file", kea_io_write_file_stub as *const u8);
    builder.symbol("__kea_io_read_file", kea_io_read_file_stub as *const u8);
    builder.symbol("__kea_clock_now", kea_clock_now_stub as *const u8);
    builder.symbol("__kea_clock_monotonic", kea_clock_monotonic_stub as *const u8);
    builder.symbol(
        "__kea_panic_div_zero",
        kea_panic_div_zero_stub as *const u8,
    );
    builder.symbol(
        "__kea_panic_mod_zero",
        kea_panic_mod_zero_stub as *const u8,
    );
}

fn compile_with_jit(
    module: &MirModule,
    layout_plan: &BackendLayoutPlan,
    isa: &Arc<dyn isa::TargetIsa>,
    _config: &BackendConfig,
) -> Result<Vec<u8>, CodegenError> {
    let mut builder = JITBuilder::with_isa(isa.clone(), cranelift_module::default_libcall_names());
    register_jit_runtime_symbols(&mut builder);
    let mut jit_module = JITModule::new(builder);
    let _ = compile_into_module(&mut jit_module, module, layout_plan)?;
    jit_module
        .finalize_definitions()
        .map_err(|detail| CodegenError::Module {
            detail: detail.to_string(),
        })?;

    // JIT mode emits executable memory, not an object file payload.
    Ok(Vec::new())
}

fn compile_with_object(
    module: &MirModule,
    layout_plan: &BackendLayoutPlan,
    isa: &Arc<dyn isa::TargetIsa>,
    _config: &BackendConfig,
) -> Result<Vec<u8>, CodegenError> {
    let builder = ObjectBuilder::new(
        isa.clone(),
        "kea",
        cranelift_module::default_libcall_names(),
    )
    .map_err(|detail| CodegenError::Module {
        detail: detail.to_string(),
    })?;
    let mut object_module = ObjectModule::new(builder);
    let _ = compile_into_module(&mut object_module, module, layout_plan)?;
    let product = object_module.finish();
    product.emit().map_err(|detail| CodegenError::ObjectEmit {
        detail: detail.to_string(),
    })
}

fn compile_into_module<M: Module>(
    module: &mut M,
    mir: &MirModule,
    layout_plan: &BackendLayoutPlan,
) -> Result<BTreeMap<String, FuncId>, CodegenError> {
    let runtime_signatures = runtime_signature_map(mir);
    let mut func_ids: BTreeMap<String, FuncId> = BTreeMap::new();
    let mut external_func_ids: BTreeMap<String, FuncId> = BTreeMap::new();
    let mut signatures: BTreeMap<String, cranelift_codegen::ir::Signature> = BTreeMap::new();
    let external_signatures = collect_external_call_signatures(module, mir)?;
    let mut requires_heap_alloc = false;
    let mut requires_io_stdout = false;
    let mut requires_io_stderr = false;
    let mut requires_io_read_file = false;
    let mut requires_io_write_file = false;
    let mut requires_clock_now = false;
    let mut requires_clock_monotonic = false;
    let mut requires_rand_int = false;
    let mut requires_rand_seed = false;
    let mut requires_net_connect = false;
    let mut requires_net_send = false;
    let mut requires_net_recv = false;
    let mut requires_string_concat = false;
    let mut requires_free = false;
    for function in &mir.functions {
        let runtime_sig = runtime_signatures.get(&function.name).ok_or_else(|| {
            CodegenError::UnknownFunction {
                function: function.name.clone(),
            }
        })?;
        let needs_aggregate_alloc = function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::RecordInit { .. }
                        | MirInst::RecordInitReuse { .. }
                        | MirInst::RecordInitFromToken { .. }
                        | MirInst::SumInitReuse { .. }
                        | MirInst::SumInitFromToken { .. }
                        | MirInst::ClosureInit { .. }
                        | MirInst::SumInit { .. }
                        | MirInst::Const {
                            literal: MirLiteral::String(_),
                            ..
                        }
                )
            })
        });
        let mut has_fail_zero_resume = false;
        for block in &function.blocks {
            for inst in &block.instructions {
                match inst {
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } => {
                        if !is_known_direct_capability_operation(effect, operation) {
                            continue;
                        }
                        match (effect.as_str(), operation.as_str()) {
                            ("IO", "stdout") => requires_io_stdout = true,
                            ("IO", "stderr") => requires_io_stderr = true,
                            ("IO", "read_file") => requires_io_read_file = true,
                            ("IO", "write_file") => requires_io_write_file = true,
                            ("Clock", "now") => requires_clock_now = true,
                            ("Clock", "monotonic") => requires_clock_monotonic = true,
                            ("Rand", "int") => requires_rand_int = true,
                            ("Rand", "seed") => requires_rand_seed = true,
                            ("Net", "connect") => requires_net_connect = true,
                            ("Net", "send") => requires_net_send = true,
                            ("Net", "recv") => requires_net_recv = true,
                            _ => {}
                        }
                    }
                    MirInst::Binary {
                        op: MirBinaryOp::Concat,
                        ..
                    } => {
                        requires_string_concat = true;
                        requires_heap_alloc = true;
                    }
                    MirInst::StateCellNew { .. } => {
                        requires_heap_alloc = true;
                        requires_free = true;
                    }
                    MirInst::Release { .. }
                    | MirInst::ReuseToken { .. }
                    | MirInst::RecordInitReuse { .. }
                    | MirInst::RecordInitFromToken { .. }
                    | MirInst::SumInitReuse { .. }
                    | MirInst::SumInitFromToken { .. } => {
                        requires_heap_alloc = true;
                        requires_free = true;
                    }
                    MirInst::EffectOp {
                        class: MirEffectOpClass::ZeroResume,
                        effect,
                        operation,
                        ..
                    } if effect == "Fail" && operation == "fail" => {
                        has_fail_zero_resume = true;
                    }
                    _ => {}
                }
            }
        }
        let needs_fail_result_alloc = runtime_sig.fail_result_abi
            || (matches!(runtime_sig.runtime_return, Type::Result(_, _)) && has_fail_zero_resume);
        if needs_aggregate_alloc || needs_fail_result_alloc {
            requires_heap_alloc = true;
        }
    }

    for function in &mir.functions {
        let runtime_sig = runtime_signatures.get(&function.name).ok_or_else(|| {
            CodegenError::UnknownFunction {
                function: function.name.clone(),
            }
        })?;
        let signature = build_signature(module, function, runtime_sig)?;
        let linkage = if function.name == "main" {
            Linkage::Export
        } else {
            Linkage::Local
        };

        let func_id = module
            .declare_function(&function.name, linkage, &signature)
            .map_err(|detail| CodegenError::Module {
                detail: detail.to_string(),
            })?;
        func_ids.insert(function.name.clone(), func_id);
        signatures.insert(function.name.clone(), signature);
    }

    for (name, signature) in external_signatures {
        let func_id = module
            .declare_function(&name, Linkage::Import, &signature)
            .map_err(|detail| CodegenError::Module {
                detail: detail.to_string(),
            })?;
        external_func_ids.insert(name, func_id);
    }

    let malloc_func_id = if requires_heap_alloc {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(ptr_ty));
        Some(
            module
                .declare_function("malloc", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let free_func_id = if requires_free {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(ptr_ty));
        Some(
            module
                .declare_function("free", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let drop_func_ids = declare_drop_functions(module, layout_plan, requires_free)?;

    let stdout_func_id = if requires_io_stdout {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(types::I32));
        Some(
            module
                .declare_function("puts", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let write_func_id = if requires_io_stderr {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(types::I32));
        signature.params.push(AbiParam::new(ptr_ty));
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(ptr_ty));
        Some(
            module
                .declare_function("write", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let io_write_file_func_id = if requires_io_write_file {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(ptr_ty));
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(types::I8));
        Some(
            module
                .declare_function("__kea_io_write_file", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let io_read_file_func_id = if requires_io_read_file {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(ptr_ty));
        Some(
            module
                .declare_function("__kea_io_read_file", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let clock_now_func_id = if requires_clock_now {
        let mut signature = module.make_signature();
        signature.returns.push(AbiParam::new(types::I64));
        Some(
            module
                .declare_function("__kea_clock_now", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let clock_monotonic_func_id = if requires_clock_monotonic {
        let mut signature = module.make_signature();
        signature.returns.push(AbiParam::new(types::I64));
        Some(
            module
                .declare_function("__kea_clock_monotonic", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let rand_func_id = if requires_rand_int {
        let mut signature = module.make_signature();
        signature.returns.push(AbiParam::new(types::I32));
        Some(
            module
                .declare_function("rand", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let srand_func_id = if requires_rand_seed {
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(types::I32));
        Some(
            module
                .declare_function("srand", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let net_connect_func_id = if requires_net_connect {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(types::I64));
        Some(
            module
                .declare_function("__kea_net_connect", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let net_send_func_id = if requires_net_send {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(types::I64));
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(types::I8));
        Some(
            module
                .declare_function("__kea_net_send", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let net_recv_func_id = if requires_net_recv {
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(types::I64));
        signature.params.push(AbiParam::new(types::I64));
        signature.returns.push(AbiParam::new(types::I64));
        Some(
            module
                .declare_function("__kea_net_recv", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let strlen_func_id = if requires_string_concat || requires_io_stderr {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(ptr_ty));
        Some(
            module
                .declare_function("strlen", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    let memcpy_func_id = if requires_string_concat {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(ptr_ty));
        signature.params.push(AbiParam::new(ptr_ty));
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(ptr_ty));
        Some(
            module
                .declare_function("memcpy", Linkage::Import, &signature)
                .map_err(|detail| CodegenError::Module {
                    detail: detail.to_string(),
                })?,
        )
    } else {
        None
    };

    if requires_free {
        define_drop_functions(module, layout_plan, &drop_func_ids, free_func_id)?;
    }

    let mut builder_context = FunctionBuilderContext::new();

    for function in &mir.functions {
        let mut context = module.make_context();
        context.func.signature = signatures.get(&function.name).cloned().ok_or_else(|| {
            CodegenError::UnknownFunction {
                function: function.name.clone(),
            }
        })?;

        {
            let mut builder = FunctionBuilder::new(&mut context.func, &mut builder_context);
            let mut block_map = BTreeMap::new();
            for block in &function.blocks {
                block_map.insert(block.id.clone(), builder.create_block());
            }

            let entry_block =
                *block_map
                    .get(&function.entry)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function.name.clone(),
                        detail: "entry block missing".to_string(),
                    })?;

            builder.append_block_params_for_function_params(entry_block);
            for block in &function.blocks {
                if block.id == function.entry {
                    continue;
                }
                let clif_block =
                    *block_map
                        .get(&block.id)
                        .ok_or_else(|| CodegenError::UnsupportedMir {
                            function: function.name.clone(),
                            detail: format!("missing Cranelift block for MIR block {:?}", block.id),
                        })?;
                for param in &block.params {
                    let ty = clif_type(&param.ty)?;
                    builder.append_block_param(clif_block, ty);
                }
            }

            let mut values: BTreeMap<MirValueId, Value> = BTreeMap::new();
            let current_runtime_sig = runtime_signatures.get(&function.name).ok_or_else(|| {
                CodegenError::UnknownFunction {
                    function: function.name.clone(),
                }
            })?;
            let value_types = infer_mir_value_types(function, layout_plan);

            for block in &function.blocks {
                let clif_block =
                    *block_map
                        .get(&block.id)
                        .ok_or_else(|| CodegenError::UnsupportedMir {
                            function: function.name.clone(),
                            detail: format!("missing Cranelift block for MIR block {:?}", block.id),
                        })?;
                builder.switch_to_block(clif_block);
                if block.id == function.entry {
                    for (index, value) in
                        builder.block_params(clif_block).iter().copied().enumerate()
                    {
                        values.insert(MirValueId(index as u32), value);
                    }
                } else {
                    let block_params = builder.block_params(clif_block);
                    if block_params.len() != block.params.len() {
                        return Err(CodegenError::UnsupportedMir {
                            function: function.name.clone(),
                            detail: format!(
                                "block {:?} parameter arity mismatch: expected {}, got {}",
                                block.id,
                                block.params.len(),
                                block_params.len()
                            ),
                        });
                    }
                    for (param, value) in block.params.iter().zip(block_params.iter().copied()) {
                        values.insert(param.id.clone(), value);
                    }
                }

                let tail_self_call = detect_tail_self_call(function, block);
                let instruction_count = if tail_self_call.is_some() {
                    block.instructions.len().saturating_sub(1)
                } else {
                    block.instructions.len()
                };

                let mut block_terminated = false;
                let lower_inst_ctx = LowerInstCtx {
                    func_ids: &func_ids,
                    external_func_ids: &external_func_ids,
                    layout_plan,
                    malloc_func_id,
                    free_func_id,
                    stdout_func_id,
                    write_func_id,
                    io_write_file_func_id,
                    io_read_file_func_id,
                    clock_now_func_id,
                    clock_monotonic_func_id,
                    rand_func_id,
                    srand_func_id,
                    net_connect_func_id,
                    net_send_func_id,
                    net_recv_func_id,
                    strlen_func_id,
                    memcpy_func_id,
                    drop_func_ids: &drop_func_ids,
                    value_types: &value_types,
                    runtime_signatures: &runtime_signatures,
                    current_runtime_sig,
                };
                for inst in block.instructions.iter().take(instruction_count) {
                    if lower_instruction(
                        module,
                        &mut builder,
                        &function.name,
                        inst,
                        &mut values,
                        &lower_inst_ctx,
                    )? {
                        block_terminated = true;
                        break;
                    }
                }
                if !block_terminated {
                    let terminator_ctx = LowerTerminatorCtx {
                        function_name: &function.name,
                        function,
                        current_runtime_sig,
                        malloc_func_id,
                        values: &values,
                        block_map: &block_map,
                        func_ids: &func_ids,
                    };
                    lower_terminator(module, &mut builder, block, &terminator_ctx)?;
                }
            }
            builder.seal_all_blocks();
            builder.finalize();
        }

        let func_id =
            *func_ids
                .get(&function.name)
                .ok_or_else(|| CodegenError::UnknownFunction {
                    function: function.name.clone(),
                })?;
        module
            .define_function(func_id, &mut context)
            .map_err(|detail| CodegenError::Module {
                detail: format!("{detail:?}"),
            })?;
        module.clear_context(&mut context);
    }

    Ok(func_ids)
}

fn execute_mir_main_jit(module: &MirModule, config: &BackendConfig) -> Result<i32, CodegenError> {
    let main = module
        .functions
        .iter()
        .find(|function| function.name == "main")
        .ok_or_else(|| CodegenError::UnknownFunction {
            function: "main".to_string(),
        })?;
    let main_runtime_sig = runtime_function_signature(main);
    if !main.signature.params.is_empty() {
        return Err(CodegenError::UnsupportedMir {
            function: "main".to_string(),
            detail: "JIT entrypoint requires zero-argument `main`".to_string(),
        });
    }
    if !main_runtime_sig.logical_return.is_integer() && main_runtime_sig.logical_return != Type::Unit
    {
        return Err(CodegenError::UnsupportedMir {
            function: "main".to_string(),
            detail: format!(
                "JIT entrypoint only supports `main` returning integer or Unit (got `{}`)",
                main_runtime_sig.logical_return
            ),
        });
    }

    let isa = build_isa(config)?;
    let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    register_jit_runtime_symbols(&mut builder);
    let mut jit_module = JITModule::new(builder);
    let layout_plan = plan_layout_catalog(module)?;
    let func_ids = compile_into_module(&mut jit_module, module, &layout_plan)?;
    jit_module
        .finalize_definitions()
        .map_err(|detail| CodegenError::Module {
            detail: detail.to_string(),
        })?;

    let main_id = *func_ids
        .get("main")
        .ok_or_else(|| CodegenError::UnknownFunction {
            function: "main".to_string(),
        })?;
    let entrypoint = jit_module.get_finalized_function(main_id);

    // SAFETY: `main` signature is validated above before transmuting and calling.
    let exit_code = unsafe {
        if main_runtime_sig.fail_result_abi {
            let main_fn = std::mem::transmute::<*const u8, extern "C" fn() -> usize>(entrypoint);
            let result_ptr = main_fn();
            if result_ptr == 0 {
                return Err(CodegenError::UnsupportedMir {
                    function: "main".to_string(),
                    detail: "Fail-only main returned null Result pointer".to_string(),
                });
            }
            let tag = *(result_ptr as *const i32);
            if tag == 0 {
                match main_runtime_sig.logical_return {
                    Type::Int => {
                        let payload = *((result_ptr as *const u8).add(8) as *const i64);
                        payload as i32
                    }
                    Type::IntN(width, signedness) => match (width, signedness) {
                        (IntWidth::I8, Signedness::Signed) => {
                            *((result_ptr as *const u8).add(8) as *const i8) as i32
                        }
                        (IntWidth::I8, Signedness::Unsigned) => {
                            *((result_ptr as *const u8).add(8)) as i32
                        }
                        (IntWidth::I16, Signedness::Signed) => {
                            *((result_ptr as *const u8).add(8) as *const i16) as i32
                        }
                        (IntWidth::I16, Signedness::Unsigned) => {
                            *((result_ptr as *const u8).add(8) as *const u16) as i32
                        }
                        (IntWidth::I32, Signedness::Signed) => {
                            *((result_ptr as *const u8).add(8) as *const i32)
                        }
                        (IntWidth::I32, Signedness::Unsigned) => {
                            *((result_ptr as *const u8).add(8) as *const u32) as i32
                        }
                        (IntWidth::I64, Signedness::Signed) => {
                            *((result_ptr as *const u8).add(8) as *const i64) as i32
                        }
                        (IntWidth::I64, Signedness::Unsigned) => {
                            *((result_ptr as *const u8).add(8) as *const u64) as i32
                        }
                    },
                    Type::Unit => 0,
                    _ => unreachable!("validated logical main return type above"),
                }
            } else {
                return Err(CodegenError::UnsupportedMir {
                    function: "main".to_string(),
                    detail: "main failed with unhandled Fail effect".to_string(),
                });
            }
        } else {
            match main_runtime_sig.logical_return {
                Type::Int => {
                    let main_fn =
                        std::mem::transmute::<*const u8, extern "C" fn() -> i32>(entrypoint);
                    main_fn()
                }
                Type::IntN(width, signedness) => match (width, signedness) {
                    (IntWidth::I8, Signedness::Signed) => {
                        let main_fn =
                            std::mem::transmute::<*const u8, extern "C" fn() -> i8>(entrypoint);
                        main_fn() as i32
                    }
                    (IntWidth::I8, Signedness::Unsigned) => {
                        let main_fn =
                            std::mem::transmute::<*const u8, extern "C" fn() -> u8>(entrypoint);
                        main_fn() as i32
                    }
                    (IntWidth::I16, Signedness::Signed) => {
                        let main_fn =
                            std::mem::transmute::<*const u8, extern "C" fn() -> i16>(entrypoint);
                        main_fn() as i32
                    }
                    (IntWidth::I16, Signedness::Unsigned) => {
                        let main_fn =
                            std::mem::transmute::<*const u8, extern "C" fn() -> u16>(entrypoint);
                        main_fn() as i32
                    }
                    (IntWidth::I32, Signedness::Signed) => {
                        let main_fn =
                            std::mem::transmute::<*const u8, extern "C" fn() -> i32>(entrypoint);
                        main_fn()
                    }
                    (IntWidth::I32, Signedness::Unsigned) => {
                        let main_fn =
                            std::mem::transmute::<*const u8, extern "C" fn() -> u32>(entrypoint);
                        main_fn() as i32
                    }
                    (IntWidth::I64, Signedness::Signed) => {
                        let main_fn =
                            std::mem::transmute::<*const u8, extern "C" fn() -> i64>(entrypoint);
                        main_fn() as i32
                    }
                    (IntWidth::I64, Signedness::Unsigned) => {
                        let main_fn =
                            std::mem::transmute::<*const u8, extern "C" fn() -> u64>(entrypoint);
                        main_fn() as i32
                    }
                },
                Type::Unit => {
                    let main_fn =
                        std::mem::transmute::<*const u8, extern "C" fn() -> i32>(entrypoint);
                    let _ = main_fn();
                    0
                }
                _ => unreachable!("validated return type before JIT entrypoint dispatch"),
            }
        }
    };
    Ok(exit_code)
}

fn build_signature<M: Module>(
    module: &M,
    function: &MirFunction,
    runtime_sig: &RuntimeFunctionSig,
) -> Result<cranelift_codegen::ir::Signature, CodegenError> {
    let mut signature = module.make_signature();
    if function.name != "main"
        && function
            .blocks
            .iter()
            .any(|block| detect_tail_self_call(function, block).is_some())
    {
        signature.call_conv = CallConv::Tail;
    }

    for param in &function.signature.params {
        let ty = clif_type(param)?;
        signature.params.push(AbiParam::new(ty));
    }

    if function.name == "main" && matches!(runtime_sig.runtime_return, Type::Unit | Type::Int) {
        signature.returns.push(AbiParam::new(types::I32));
    } else if runtime_sig.runtime_return != Type::Unit {
        let ret_type = clif_type(&runtime_sig.runtime_return)?;
        signature.returns.push(AbiParam::new(ret_type));
    }

    Ok(signature)
}

fn collect_external_call_signatures<M: Module>(
    module: &M,
    mir: &MirModule,
) -> Result<BTreeMap<String, cranelift_codegen::ir::Signature>, CodegenError> {
    let mut signatures: BTreeMap<
        String,
        (
            Vec<cranelift::prelude::Type>,
            Option<cranelift::prelude::Type>,
        ),
    > = BTreeMap::new();

    for function in &mir.functions {
        for block in &function.blocks {
            for inst in &block.instructions {
                let MirInst::Call {
                    callee: MirCallee::External(name),
                    args,
                    arg_types,
                    ret_type,
                    ..
                } = inst
                else {
                    continue;
                };

                if arg_types.len() != args.len() {
                    return Err(CodegenError::UnsupportedMir {
                        function: function.name.clone(),
                        detail: format!(
                            "external call `{name}` has {} args but {} arg types",
                            args.len(),
                            arg_types.len()
                        ),
                    });
                }

                let canonical_params = arg_types
                    .iter()
                    .map(clif_type)
                    .collect::<Result<Vec<_>, _>>()?;
                let canonical_ret = if *ret_type == Type::Unit {
                    None
                } else {
                    Some(clif_type(ret_type)?)
                };

                match signatures.get(name) {
                    Some((existing_params, existing_ret))
                        if existing_params != &canonical_params
                            || existing_ret != &canonical_ret =>
                    {
                        return Err(CodegenError::UnsupportedMir {
                            function: function.name.clone(),
                            detail: format!(
                                "external call `{name}` used with conflicting signatures"
                            ),
                        });
                    }
                    Some(_) => {}
                    None => {
                        signatures.insert(name.clone(), (canonical_params, canonical_ret));
                    }
                }
            }
        }
    }

    let mut clif_signatures = BTreeMap::new();
    for (name, (params, ret)) in signatures {
        let mut signature = module.make_signature();
        for param in params {
            signature.params.push(AbiParam::new(param));
        }
        if let Some(ret) = ret {
            signature.returns.push(AbiParam::new(ret));
        }
        clif_signatures.insert(name, signature);
    }
    Ok(clif_signatures)
}

fn clif_type(ty: &Type) -> Result<cranelift::prelude::Type, CodegenError> {
    match ty {
        Type::Int => Ok(types::I64),
        Type::IntN(width, _) => clif_int_type(*width),
        Type::Float => Ok(types::F64),
        Type::FloatN(width) => clif_float_type(*width),
        Type::Bool => Ok(types::I8),
        Type::Unit => Ok(types::I8),
        Type::Never => Ok(types::I64),
        Type::String => Ok(types::I64),
        Type::Dynamic => Ok(types::I64),
        Type::Var(_) => Ok(types::I64),
        // 0d bootstrap aggregate/runtime representation:
        // nominal records/sums and Result-like carriers flow through ABI as
        // opaque machine-word handles until full aggregate lowering lands.
        Type::Record(_)
        | Type::AnonRecord(_)
        | Type::Tuple(_)
        | Type::Sum(_)
        | Type::Option(_)
        | Type::Result(_, _)
        | Type::Function(_)
        | Type::Opaque { .. } => Ok(types::I64),
        unsupported => Err(CodegenError::UnsupportedType {
            ty: unsupported.to_string(),
        }),
    }
}

const STATE_CELL_TYPE_MARKER: &str = "__kea_state_cell";
const STATE_CELL_PAYLOAD_SIZE: u32 = 16;
const STATE_CELL_VALUE_OFFSET: i32 = 0;
const STATE_CELL_MANAGED_OFFSET: i32 = 8;

fn clif_int_type(width: IntWidth) -> Result<cranelift::prelude::Type, CodegenError> {
    match width {
        IntWidth::I8 => Ok(types::I8),
        IntWidth::I16 => Ok(types::I16),
        IntWidth::I32 => Ok(types::I32),
        IntWidth::I64 => Ok(types::I64),
    }
}

fn clif_float_type(width: FloatWidth) -> Result<cranelift::prelude::Type, CodegenError> {
    match width {
        // Bootstrap uses f32 for Float16 paths until full f16 lowering lands.
        FloatWidth::F16 | FloatWidth::F32 => Ok(types::F32),
        FloatWidth::F64 => Ok(types::F64),
    }
}

fn int_signedness(ty: &Type) -> Option<Signedness> {
    match ty {
        Type::Int => Some(Signedness::Signed),
        Type::IntN(_, signedness) => Some(*signedness),
        _ => None,
    }
}

fn coerce_value_to_type(
    builder: &mut FunctionBuilder,
    value: Value,
    expected_ty: &Type,
) -> Result<Value, CodegenError> {
    let expected_clif_ty = clif_type(expected_ty)?;
    let actual_ty = builder.func.dfg.value_type(value);
    if actual_ty == expected_clif_ty {
        return Ok(value);
    }

    if actual_ty.is_int() && expected_clif_ty.is_int() {
        if actual_ty.bits() < expected_clif_ty.bits() {
            let widened = if int_signedness(expected_ty) == Some(Signedness::Signed) {
                builder.ins().sextend(expected_clif_ty, value)
            } else {
                builder.ins().uextend(expected_clif_ty, value)
            };
            return Ok(widened);
        }
        if actual_ty.bits() > expected_clif_ty.bits() {
            return Ok(builder.ins().ireduce(expected_clif_ty, value));
        }
    }

    Ok(coerce_value_to_clif_type(builder, value, expected_clif_ty))
}

fn coerce_value_to_clif_type(
    builder: &mut FunctionBuilder,
    value: Value,
    expected_ty: cranelift::prelude::Type,
) -> Value {
    let actual_ty = builder.func.dfg.value_type(value);
    if actual_ty == expected_ty {
        return value;
    }
    if actual_ty.is_int() && expected_ty.is_int() {
        if actual_ty.bits() < expected_ty.bits() {
            return builder.ins().uextend(expected_ty, value);
        }
        if actual_ty.bits() > expected_ty.bits() {
            return builder.ins().ireduce(expected_ty, value);
        }
    }
    value
}

fn lower_result_allocation(
    module: &mut impl Module,
    builder: &mut FunctionBuilder,
    function_name: &str,
    malloc_func_id: Option<FuncId>,
    tag: i32,
    payload: Value,
    payload_ty: &Type,
) -> Result<Value, CodegenError> {
    let result_ptr = allocate_heap_payload(
        module,
        builder,
        function_name,
        malloc_func_id,
        16,
        "Result lowering requires malloc import",
    )?;
    let tag_value = builder.ins().iconst(types::I32, i64::from(tag));
    builder
        .ins()
        .store(MemFlags::new(), tag_value, result_ptr, 0);
    let payload = coerce_value_to_type(builder, payload, payload_ty)?;
    builder.ins().store(MemFlags::new(), payload, result_ptr, 8);
    Ok(result_ptr)
}

fn lower_string_literal<M: Module>(
    module: &mut M,
    builder: &mut FunctionBuilder,
    function_name: &str,
    malloc_func_id: Option<FuncId>,
    text: &str,
) -> Result<Value, CodegenError> {
    let bytes = text.as_bytes();
    let alloc_size =
        u32::try_from(bytes.len().saturating_add(1)).map_err(|_| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "string literal too large to lower".to_string(),
        })?;
    let out_ptr = allocate_heap_payload(
        module,
        builder,
        function_name,
        malloc_func_id,
        alloc_size,
        "string literal lowering requires malloc import",
    )?;
    for (idx, byte) in bytes.iter().enumerate() {
        let offset = i32::try_from(idx).map_err(|_| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "string literal offset does not fit i32".to_string(),
        })?;
        let value = builder.ins().iconst(types::I8, i64::from(*byte));
        builder.ins().store(MemFlags::new(), value, out_ptr, offset);
    }
    let term_offset = i32::try_from(bytes.len()).map_err(|_| CodegenError::UnsupportedMir {
        function: function_name.to_string(),
        detail: "string literal terminator offset does not fit i32".to_string(),
    })?;
    let term = builder.ins().iconst(types::I8, 0);
    builder
        .ins()
        .store(MemFlags::new(), term, out_ptr, term_offset);
    Ok(out_ptr)
}

fn store_record_fields(
    builder: &mut FunctionBuilder,
    function_name: &str,
    layout: &BackendRecordLayout,
    record_type: &str,
    base_ptr: Value,
    fields: &[(String, MirValueId)],
    values: &BTreeMap<MirValueId, Value>,
) -> Result<(), CodegenError> {
    for (field_name, field_value_id) in fields {
        let field_value = get_value(values, function_name, field_value_id)?;
        let offset = *layout.field_offsets.get(field_name).ok_or_else(|| {
            CodegenError::UnsupportedMir {
                function: function_name.to_string(),
                detail: format!(
                    "record layout `{record_type}` missing field `{field_name}` during init"
                ),
            }
        })?;
        let offset = i32::try_from(offset).map_err(|_| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: format!("record field `{record_type}.{field_name}` offset does not fit i32"),
        })?;
        builder
            .ins()
            .store(MemFlags::new(), field_value, base_ptr, offset);
    }
    Ok(())
}

struct SumInitSpec<'a> {
    sum_type: &'a str,
    variant: &'a str,
    tag: u32,
    fields: &'a [MirValueId],
}

fn store_sum_init_payload(
    builder: &mut FunctionBuilder,
    function_name: &str,
    layout: &BackendSumLayout,
    spec: SumInitSpec<'_>,
    values: &BTreeMap<MirValueId, Value>,
    base_ptr: Value,
) -> Result<(), CodegenError> {
    let expected_fields = *layout
        .variant_field_counts
        .get(spec.variant)
        .ok_or_else(|| {
        CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: format!(
                "sum layout `{}` missing variant `{}` during init",
                spec.sum_type, spec.variant
            ),
        }
    })?;
    if expected_fields as usize != spec.fields.len() {
        return Err(CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: format!(
                "sum init `{sum_type}.{variant}` expected {} fields but got {}",
                expected_fields,
                spec.fields.len(),
                sum_type = spec.sum_type,
                variant = spec.variant,
            ),
        });
    }

    let tag_offset = i32::try_from(layout.tag_offset).map_err(|_| CodegenError::UnsupportedMir {
        function: function_name.to_string(),
        detail: format!("sum tag offset for `{}` does not fit i32", spec.sum_type),
    })?;
    let tag_value = builder.ins().iconst(types::I32, i64::from(spec.tag));
    builder
        .ins()
        .store(MemFlags::new(), tag_value, base_ptr, tag_offset);

    for (idx, field_value_id) in spec.fields.iter().enumerate() {
        let field_value = get_value(values, function_name, field_value_id)?;
        let field_offset = layout.payload_offset + (idx as u32 * 8);
        let field_offset = i32::try_from(field_offset).map_err(|_| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: format!(
                "sum payload offset `{}.{}`[{idx}] does not fit i32",
                spec.sum_type, spec.variant
            ),
        })?;
        builder
            .ins()
            .store(MemFlags::new(), field_value, base_ptr, field_offset);
    }
    Ok(())
}

fn allocate_heap_payload(
    module: &mut impl Module,
    builder: &mut FunctionBuilder,
    function_name: &str,
    malloc_func_id: Option<FuncId>,
    payload_bytes: u32,
    missing_malloc_detail: &str,
) -> Result<Value, CodegenError> {
    let malloc_func_id = malloc_func_id.ok_or_else(|| CodegenError::UnsupportedMir {
        function: function_name.to_string(),
        detail: missing_malloc_detail.to_string(),
    })?;
    let malloc_ref = module.declare_func_in_func(malloc_func_id, builder.func);
    let ptr_ty = module.target_config().pointer_type();
    let alloc_bytes = payload_bytes.max(1).saturating_add(8);
    let alloc_size = builder.ins().iconst(ptr_ty, i64::from(alloc_bytes));
    let alloc_call = builder.ins().call(malloc_ref, &[alloc_size]);
    let raw_ptr = builder
        .inst_results(alloc_call)
        .first()
        .copied()
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "malloc call returned no pointer value".to_string(),
        })?;
    let rc_value = builder.ins().iconst(types::I64, 1);
    builder.ins().store(MemFlags::new(), rc_value, raw_ptr, 0);
    Ok(builder.ins().iadd_imm(raw_ptr, 8))
}

fn allocate_heap_payload_dynamic(
    module: &mut impl Module,
    builder: &mut FunctionBuilder,
    function_name: &str,
    malloc_func_id: Option<FuncId>,
    payload_bytes: Value,
    missing_malloc_detail: &str,
) -> Result<Value, CodegenError> {
    let malloc_func_id = malloc_func_id.ok_or_else(|| CodegenError::UnsupportedMir {
        function: function_name.to_string(),
        detail: missing_malloc_detail.to_string(),
    })?;
    let malloc_ref = module.declare_func_in_func(malloc_func_id, builder.func);
    let ptr_ty = module.target_config().pointer_type();
    let payload_bytes = coerce_value_to_clif_type(builder, payload_bytes, ptr_ty);
    let alloc_bytes = builder.ins().iadd_imm(payload_bytes, 8);
    let alloc_call = builder.ins().call(malloc_ref, &[alloc_bytes]);
    let raw_ptr = builder
        .inst_results(alloc_call)
        .first()
        .copied()
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "malloc call returned no pointer value".to_string(),
        })?;
    let rc_value = builder.ins().iconst(types::I64, 1);
    builder.ins().store(MemFlags::new(), rc_value, raw_ptr, 0);
    Ok(builder.ins().iadd_imm(raw_ptr, 8))
}

fn is_managed_heap_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::String
            | Type::Record(_)
            | Type::Tuple(_)
            | Type::Sum(_)
            | Type::Option(_)
            | Type::Result(_, _)
    )
}

fn drop_sum_name_for_type(ty: &Type) -> Option<&str> {
    match ty {
        Type::Sum(sum) => Some(sum.name.as_str()),
        Type::Option(_) => Some("Option"),
        Type::Result(_, _) => Some("Result"),
        _ => None,
    }
}

fn drop_function_for_type(ty: &Type, drop_func_ids: &DropFunctionIds) -> Option<FuncId> {
    match ty {
        Type::Record(record) => drop_func_ids.records.get(record.name.as_str()).copied(),
        _ => drop_sum_name_for_type(ty)
            .and_then(|name| drop_func_ids.sums.get(name))
            .copied(),
    }
}

fn sum_type_has_immediate_variants(ty: &Type, layout_plan: &BackendLayoutPlan) -> bool {
    drop_sum_name_for_type(ty)
        .and_then(|name| layout_plan.sums.get(name))
        .is_some_and(|layout| layout.variant_field_counts.values().any(|count| *count == 0))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StateCellRcMode {
    Never,
    Always,
    MixedSum { max_immediate_tag: i64 },
}

fn state_cell_rc_mode_for_type(ty: &Type, layout_plan: &BackendLayoutPlan) -> StateCellRcMode {
    let Some(sum_name) = drop_sum_name_for_type(ty) else {
        return if matches!(
            ty,
            Type::String
                | Type::Record(_)
                | Type::Tuple(_)
                | Type::AnonRecord(_)
                | Type::Function(_)
                | Type::Opaque { .. }
        ) {
            StateCellRcMode::Always
        } else {
            StateCellRcMode::Never
        };
    };
    let Some(layout) = layout_plan.sums.get(sum_name) else {
        return if is_managed_heap_type(ty) {
            StateCellRcMode::Always
        } else {
            StateCellRcMode::Never
        };
    };
    let has_unit_variant = layout.variant_field_counts.values().any(|count| *count == 0);
    let has_payload_variant = layout.variant_field_counts.values().any(|count| *count > 0);
    if has_payload_variant && has_unit_variant {
        let max_immediate_tag = i64::try_from(layout.variant_field_counts.len())
            .ok()
            .and_then(|len| len.checked_sub(1))
            .unwrap_or(0);
        StateCellRcMode::MixedSum { max_immediate_tag }
    } else if has_payload_variant {
        StateCellRcMode::Always
    } else {
        StateCellRcMode::Never
    }
}

fn state_cell_rc_mode_for_value(value: &MirValueId, ctx: &LowerInstCtx<'_>) -> StateCellRcMode {
    let ty = ctx.value_types.get(value).unwrap_or(&Type::Dynamic);
    state_cell_rc_mode_for_type(ty, ctx.layout_plan)
}

fn mangle_drop_symbol(prefix: &str, name: &str) -> String {
    let mut out = String::with_capacity(prefix.len() + name.len() + 8);
    out.push_str(prefix);
    out.push_str("__");
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    out
}

fn infer_mir_value_types(
    function: &MirFunction,
    layout_plan: &BackendLayoutPlan,
) -> BTreeMap<MirValueId, Type> {
    let mut value_types = BTreeMap::new();

    for (index, param_ty) in function.signature.params.iter().enumerate() {
        value_types.insert(MirValueId(index as u32), param_ty.clone());
    }

    for block in &function.blocks {
        for param in &block.params {
            value_types.insert(param.id.clone(), param.ty.clone());
        }
        for inst in &block.instructions {
            match inst {
                MirInst::Const { dest, literal } => {
                    let ty = match literal {
                        MirLiteral::Int(_) => Type::Int,
                        MirLiteral::Float(_) => Type::Float,
                        MirLiteral::Bool(_) => Type::Bool,
                        MirLiteral::String(_) => Type::String,
                        MirLiteral::Unit => Type::Unit,
                    };
                    value_types.insert(dest.clone(), ty);
                }
                MirInst::Binary { dest, op, left, .. } => {
                    let ty = match op {
                        MirBinaryOp::Eq
                        | MirBinaryOp::Neq
                        | MirBinaryOp::Lt
                        | MirBinaryOp::Lte
                        | MirBinaryOp::Gt
                        | MirBinaryOp::Gte
                        | MirBinaryOp::And
                        | MirBinaryOp::Or => Type::Bool,
                        MirBinaryOp::Concat => Type::String,
                        _ => value_types.get(left).cloned().unwrap_or(Type::Int),
                    };
                    value_types.insert(dest.clone(), ty);
                }
                MirInst::Unary { dest, op, operand } => {
                    let ty = match op {
                        MirUnaryOp::Not => Type::Bool,
                        _ => value_types.get(operand).cloned().unwrap_or(Type::Int),
                    };
                    value_types.insert(dest.clone(), ty);
                }
                MirInst::RecordInit {
                    dest, record_type, ..
                }
                | MirInst::RecordInitReuse {
                    dest, record_type, ..
                }
                | MirInst::RecordInitFromToken {
                    dest, record_type, ..
                } => {
                    value_types.insert(
                        dest.clone(),
                        Type::Record(RecordType {
                            name: record_type.clone(),
                            params: Vec::new(),
                            row: kea_types::RowType::closed(Vec::new()),
                        }),
                    );
                }
                MirInst::SumInit { dest, sum_type, .. }
                | MirInst::SumInitReuse { dest, sum_type, .. }
                | MirInst::SumInitFromToken { dest, sum_type, .. } => {
                    value_types.insert(
                        dest.clone(),
                        Type::Sum(SumType {
                            name: sum_type.clone(),
                            type_args: Vec::new(),
                            variants: Vec::new(),
                        }),
                    );
                }
                MirInst::SumTagLoad { dest, .. } => {
                    value_types.insert(dest.clone(), Type::Int);
                }
                MirInst::SumPayloadLoad {
                    dest,
                    sum_type,
                    variant,
                    field_index,
                    field_ty,
                    ..
                } => {
                    let resolved = if *field_ty == Type::Dynamic {
                        layout_plan
                            .sums
                            .get(sum_type)
                            .and_then(|layout| layout.variant_field_types.get(variant))
                            .and_then(|fields| fields.get(*field_index))
                            .cloned()
                            .unwrap_or(Type::Dynamic)
                    } else {
                        field_ty.clone()
                    };
                    value_types.insert(dest.clone(), resolved);
                }
                MirInst::RecordFieldLoad {
                    dest,
                    record_type,
                    field,
                    field_ty,
                    ..
                } => {
                    let resolved = if *field_ty == Type::Dynamic {
                        layout_plan
                            .records
                            .get(record_type)
                            .and_then(|layout| layout.field_types.get(field))
                            .cloned()
                            .unwrap_or(Type::Dynamic)
                    } else {
                        field_ty.clone()
                    };
                    value_types.insert(dest.clone(), resolved);
                }
                MirInst::ClosureCaptureLoad {
                    dest, capture_ty, ..
                } => {
                    value_types.insert(dest.clone(), capture_ty.clone());
                }
                MirInst::Move { dest, src }
                | MirInst::Borrow { dest, src }
                | MirInst::TryClaim { dest, src }
                | MirInst::Freeze { dest, src }
                | MirInst::ReuseToken {
                    dest, source: src, ..
                } => {
                    let ty = value_types.get(src).cloned().unwrap_or(Type::Dynamic);
                    value_types.insert(dest.clone(), ty);
                }
                MirInst::CowUpdate {
                    dest,
                    target,
                    record_type,
                    ..
                } => {
                    let ty = value_types.get(target).cloned().unwrap_or_else(|| {
                        Type::Record(RecordType {
                            name: record_type.clone(),
                            params: Vec::new(),
                            row: kea_types::RowType::closed(Vec::new()),
                        })
                    });
                    value_types.insert(dest.clone(), ty);
                }
                MirInst::Call {
                    result: Some(dest),
                    ret_type,
                    ..
                } => {
                    value_types.insert(dest.clone(), ret_type.clone());
                }
                MirInst::StateCellLoad { dest, .. } => {
                    value_types.insert(dest.clone(), Type::Dynamic);
                }
                MirInst::FunctionRef { dest, .. } | MirInst::ClosureInit { dest, .. } => {
                    value_types.insert(dest.clone(), Type::Dynamic);
                }
                MirInst::EffectOp {
                    result: Some(dest), ..
                } => {
                    value_types.insert(dest.clone(), Type::Dynamic);
                }
                MirInst::StateCellNew { dest, .. } => {
                    value_types.insert(
                        dest.clone(),
                        Type::Opaque {
                            name: STATE_CELL_TYPE_MARKER.to_string(),
                            params: Vec::new(),
                        },
                    );
                }
                MirInst::StateCellStore { .. }
                | MirInst::Retain { .. }
                | MirInst::Release { .. }
                | MirInst::HandlerEnter { .. }
                | MirInst::HandlerExit { .. }
                | MirInst::Resume { .. }
                | MirInst::Call { result: None, .. }
                | MirInst::EffectOp { result: None, .. }
                | MirInst::Unsupported { .. }
                | MirInst::Nop => {}
            }
        }
    }

    value_types
}

struct LowerInstCtx<'a> {
    func_ids: &'a BTreeMap<String, FuncId>,
    external_func_ids: &'a BTreeMap<String, FuncId>,
    layout_plan: &'a BackendLayoutPlan,
    malloc_func_id: Option<FuncId>,
    free_func_id: Option<FuncId>,
    stdout_func_id: Option<FuncId>,
    write_func_id: Option<FuncId>,
    io_write_file_func_id: Option<FuncId>,
    io_read_file_func_id: Option<FuncId>,
    clock_now_func_id: Option<FuncId>,
    clock_monotonic_func_id: Option<FuncId>,
    rand_func_id: Option<FuncId>,
    srand_func_id: Option<FuncId>,
    net_connect_func_id: Option<FuncId>,
    net_send_func_id: Option<FuncId>,
    net_recv_func_id: Option<FuncId>,
    strlen_func_id: Option<FuncId>,
    memcpy_func_id: Option<FuncId>,
    drop_func_ids: &'a DropFunctionIds,
    value_types: &'a BTreeMap<MirValueId, Type>,
    runtime_signatures: &'a BTreeMap<String, RuntimeFunctionSig>,
    current_runtime_sig: &'a RuntimeFunctionSig,
}

fn emit_generic_release<M: Module>(
    module: &mut M,
    builder: &mut FunctionBuilder,
    function_name: &str,
    payload_ptr: Value,
    free_func_id: Option<FuncId>,
) -> Result<(), CodegenError> {
    let free_func_id = free_func_id.ok_or_else(|| CodegenError::UnsupportedMir {
        function: function_name.to_string(),
        detail: "release lowering requires imported `free` symbol".to_string(),
    })?;
    let rc_ptr = builder.ins().iadd_imm(payload_ptr, -8);
    let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
    let next = builder.ins().iadd_imm(rc_value, -1);
    builder.ins().store(MemFlags::new(), next, rc_ptr, 0);

    let free_ref = module.declare_func_in_func(free_func_id, builder.func);
    let free_block = builder.create_block();
    let cont_block = builder.create_block();
    let is_zero = builder.ins().icmp_imm(IntCC::Equal, next, 0);
    builder
        .ins()
        .brif(is_zero, free_block, &[], cont_block, &[]);
    builder.switch_to_block(free_block);
    let _ = builder.ins().call(free_ref, &[rc_ptr]);
    builder.ins().jump(cont_block, &[]);
    builder.switch_to_block(cont_block);
    Ok(())
}

fn emit_retain(builder: &mut FunctionBuilder, payload_ptr: Value) {
    let rc_ptr = builder.ins().iadd_imm(payload_ptr, -8);
    let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
    let next = builder.ins().iadd_imm(rc_value, 1);
    builder.ins().store(MemFlags::new(), next, rc_ptr, 0);
}

fn emit_retain_if_managed_flag(
    builder: &mut FunctionBuilder,
    payload_value: Value,
    managed_flag: Value,
    ptr_ty: cranelift::prelude::Type,
) {
    let retain_block = builder.create_block();
    let cont_block = builder.create_block();
    let is_managed = builder.ins().icmp_imm(IntCC::NotEqual, managed_flag, 0);
    builder
        .ins()
        .brif(is_managed, retain_block, &[], cont_block, &[]);
    builder.switch_to_block(retain_block);
    let payload_ptr = coerce_value_to_clif_type(builder, payload_value, ptr_ty);
    emit_retain(builder, payload_ptr);
    builder.ins().jump(cont_block, &[]);
    builder.switch_to_block(cont_block);
}

fn emit_release_if_managed_flag<M: Module>(
    module: &mut M,
    builder: &mut FunctionBuilder,
    function_name: &str,
    payload_value: Value,
    managed_flag: Value,
    ptr_ty: cranelift::prelude::Type,
    free_func_id: Option<FuncId>,
) -> Result<(), CodegenError> {
    let release_block = builder.create_block();
    let cont_block = builder.create_block();
    let is_managed = builder.ins().icmp_imm(IntCC::NotEqual, managed_flag, 0);
    builder
        .ins()
        .brif(is_managed, release_block, &[], cont_block, &[]);
    builder.switch_to_block(release_block);
    let payload_ptr = coerce_value_to_clif_type(builder, payload_value, ptr_ty);
    emit_generic_release(module, builder, function_name, payload_ptr, free_func_id)?;
    builder.ins().jump(cont_block, &[]);
    builder.switch_to_block(cont_block);
    Ok(())
}

fn emit_state_cell_flag_and_retain(
    builder: &mut FunctionBuilder,
    payload_value: Value,
    rc_mode: StateCellRcMode,
    ptr_ty: cranelift::prelude::Type,
) -> Value {
    match rc_mode {
        StateCellRcMode::Never => builder.ins().iconst(types::I8, 0),
        StateCellRcMode::Always => {
            let payload_ptr = coerce_value_to_clif_type(builder, payload_value, ptr_ty);
            emit_retain(builder, payload_ptr);
            builder.ins().iconst(types::I8, 1)
        }
        StateCellRcMode::MixedSum { max_immediate_tag } => {
            let immediate_block = builder.create_block();
            let managed_block = builder.create_block();
            let join_block = builder.create_block();
            builder.append_block_param(join_block, types::I8);

            let is_immediate = builder
                .ins()
                .icmp_imm(IntCC::UnsignedLessThanOrEqual, payload_value, max_immediate_tag);
            builder
                .ins()
                .brif(is_immediate, immediate_block, &[], managed_block, &[]);

            builder.switch_to_block(immediate_block);
            let unmanaged = builder.ins().iconst(types::I8, 0);
            builder.ins().jump(join_block, &[unmanaged]);

            builder.switch_to_block(managed_block);
            let payload_ptr = coerce_value_to_clif_type(builder, payload_value, ptr_ty);
            emit_retain(builder, payload_ptr);
            let managed = builder.ins().iconst(types::I8, 1);
            builder.ins().jump(join_block, &[managed]);

            builder.switch_to_block(join_block);
            builder
                .block_params(join_block)
                .first()
                .copied()
                .unwrap_or_else(|| builder.ins().iconst(types::I8, 0))
        }
    }
}

fn emit_typed_release<M: Module>(
    module: &mut M,
    builder: &mut FunctionBuilder,
    function_name: &str,
    payload_ptr: Value,
    value_ty: Option<&Type>,
    drop_func_ids: &DropFunctionIds,
    free_func_id: Option<FuncId>,
) -> Result<(), CodegenError> {
    if let Some(ty) = value_ty
        && is_managed_heap_type(ty)
        && let Some(drop_func_id) = drop_function_for_type(ty, drop_func_ids)
    {
        let drop_ref = module.declare_func_in_func(drop_func_id, builder.func);
        let _ = builder.ins().call(drop_ref, &[payload_ptr]);
        return Ok(());
    }

    emit_generic_release(module, builder, function_name, payload_ptr, free_func_id)
}

fn declare_drop_functions<M: Module>(
    module: &mut M,
    layout_plan: &BackendLayoutPlan,
    enabled: bool,
) -> Result<DropFunctionIds, CodegenError> {
    if !enabled {
        return Ok(DropFunctionIds::default());
    }
    let ptr_ty = module.target_config().pointer_type();
    let mut signature = module.make_signature();
    signature.params.push(AbiParam::new(ptr_ty));

    let mut drop_ids = DropFunctionIds::default();
    for record_name in layout_plan.records.keys() {
        let symbol = mangle_drop_symbol("__kea_drop_record", record_name);
        let func_id = module
            .declare_function(&symbol, Linkage::Local, &signature)
            .map_err(|detail| CodegenError::Module {
                detail: detail.to_string(),
            })?;
        drop_ids.records.insert(record_name.clone(), func_id);
    }
    for sum_name in layout_plan.sums.keys() {
        let symbol = mangle_drop_symbol("__kea_drop_sum", sum_name);
        let func_id = module
            .declare_function(&symbol, Linkage::Local, &signature)
            .map_err(|detail| CodegenError::Module {
                detail: detail.to_string(),
            })?;
        drop_ids.sums.insert(sum_name.clone(), func_id);
    }
    Ok(drop_ids)
}

fn define_record_drop_function<M: Module>(
    module: &mut M,
    type_name: &str,
    layout: &BackendRecordLayout,
    drop_func_ids: &DropFunctionIds,
    free_func_id: Option<FuncId>,
) -> Result<(), CodegenError> {
    let func_id = *drop_func_ids
        .records
        .get(type_name)
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: type_name.to_string(),
            detail: format!("missing declared drop function for record `{type_name}`"),
        })?;

    let mut context = module.make_context();
    let ptr_ty = module.target_config().pointer_type();
    context.func.signature.params.push(AbiParam::new(ptr_ty));

    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut context.func, &mut builder_context);
    let entry = builder.create_block();
    let unique_block = builder.create_block();
    let free_block = builder.create_block();
    let ret_block = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);

    let payload_ptr = builder
        .block_params(entry)
        .first()
        .copied()
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: type_name.to_string(),
            detail: "drop function missing payload parameter".to_string(),
        })?;
    let rc_ptr = builder.ins().iadd_imm(payload_ptr, -8);
    let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
    let next = builder.ins().iadd_imm(rc_value, -1);
    builder.ins().store(MemFlags::new(), next, rc_ptr, 0);
    let is_zero = builder.ins().icmp_imm(IntCC::Equal, next, 0);
    builder
        .ins()
        .brif(is_zero, unique_block, &[], ret_block, &[]);

    builder.switch_to_block(unique_block);
    for (field_name, field_ty) in &layout.field_types {
        if !is_managed_heap_type(field_ty) {
            continue;
        }
        let Some(field_offset) = layout.field_offsets.get(field_name) else {
            continue;
        };
        let field_offset =
            i32::try_from(*field_offset).map_err(|_| CodegenError::UnsupportedMir {
                function: type_name.to_string(),
                detail: format!(
                    "record `{type_name}` field `{field_name}` offset does not fit i32"
                ),
            })?;
        let field_ptr = builder
            .ins()
            .load(ptr_ty, MemFlags::new(), payload_ptr, field_offset);
        emit_typed_release(
            module,
            &mut builder,
            type_name,
            field_ptr,
            Some(field_ty),
            drop_func_ids,
            free_func_id,
        )?;
    }
    builder.ins().jump(free_block, &[]);
    builder.switch_to_block(free_block);
    let free_func_id = free_func_id.ok_or_else(|| CodegenError::UnsupportedMir {
        function: type_name.to_string(),
        detail: "drop lowering requires imported `free` symbol".to_string(),
    })?;
    let free_ref = module.declare_func_in_func(free_func_id, builder.func);
    let _ = builder.ins().call(free_ref, &[rc_ptr]);
    builder.ins().jump(ret_block, &[]);

    builder.switch_to_block(ret_block);
    builder.ins().return_(&[]);
    builder.seal_all_blocks();
    builder.finalize();

    module
        .define_function(func_id, &mut context)
        .map_err(|detail| CodegenError::Module {
            detail: format!("drop function `{type_name}`: {detail:?}"),
        })?;
    module.clear_context(&mut context);
    Ok(())
}

fn define_sum_drop_function<M: Module>(
    module: &mut M,
    type_name: &str,
    layout: &BackendSumLayout,
    drop_func_ids: &DropFunctionIds,
    free_func_id: Option<FuncId>,
) -> Result<(), CodegenError> {
    let func_id = *drop_func_ids
        .sums
        .get(type_name)
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: type_name.to_string(),
            detail: format!("missing declared drop function for sum `{type_name}`"),
        })?;

    let mut context = module.make_context();
    let ptr_ty = module.target_config().pointer_type();
    context.func.signature.params.push(AbiParam::new(ptr_ty));

    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut context.func, &mut builder_context);
    let entry = builder.create_block();
    let unique_block = builder.create_block();
    let free_block = builder.create_block();
    let ret_block = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);

    let payload_ptr = builder
        .block_params(entry)
        .first()
        .copied()
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: type_name.to_string(),
            detail: "drop function missing payload parameter".to_string(),
        })?;
    let has_unit_variant = layout.variant_field_counts.values().any(|count| *count == 0);
    let has_payload_variant = layout.variant_field_counts.values().any(|count| *count > 0);
    if has_unit_variant && !has_payload_variant {
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();
        module
            .define_function(func_id, &mut context)
            .map_err(|detail| CodegenError::Module {
                detail: format!("drop function `{type_name}`: {detail:?}"),
            })?;
        module.clear_context(&mut context);
        return Ok(());
    }
    if has_unit_variant && has_payload_variant {
        let pointer_block = builder.create_block();
        let max_tag = i64::try_from(layout.variant_field_counts.len())
            .map_err(|_| CodegenError::UnsupportedMir {
                function: type_name.to_string(),
                detail: format!("sum `{type_name}` has invalid mixed-variant tag cardinality"),
            })?
            - 1;
        let max_tag_value = builder.ins().iconst(ptr_ty, max_tag);
        let is_immediate =
            builder
                .ins()
                .icmp(IntCC::UnsignedLessThanOrEqual, payload_ptr, max_tag_value);
        builder
            .ins()
            .brif(is_immediate, ret_block, &[], pointer_block, &[]);
        builder.switch_to_block(pointer_block);
    }
    let rc_ptr = builder.ins().iadd_imm(payload_ptr, -8);
    let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
    let next = builder.ins().iadd_imm(rc_value, -1);
    builder.ins().store(MemFlags::new(), next, rc_ptr, 0);
    let is_zero = builder.ins().icmp_imm(IntCC::Equal, next, 0);
    builder
        .ins()
        .brif(is_zero, unique_block, &[], ret_block, &[]);

    builder.switch_to_block(unique_block);
    let tag_offset = i32::try_from(layout.tag_offset).map_err(|_| CodegenError::UnsupportedMir {
        function: type_name.to_string(),
        detail: format!("sum `{type_name}` tag offset does not fit i32"),
    })?;
    let tag_value = builder
        .ins()
        .load(types::I32, MemFlags::new(), payload_ptr, tag_offset);
    let payload_offset =
        i32::try_from(layout.payload_offset).map_err(|_| CodegenError::UnsupportedMir {
            function: type_name.to_string(),
            detail: format!("sum `{type_name}` payload offset does not fit i32"),
        })?;
    let mut variants = layout
        .variant_tags
        .iter()
        .filter_map(|(variant_name, tag)| {
            let field_types = layout.variant_field_types.get(variant_name)?;
            if field_types.iter().any(is_managed_heap_type) {
                Some((*tag, field_types.as_slice()))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    variants.sort_by_key(|(tag, _)| *tag);

    if variants.is_empty() {
        builder.ins().jump(free_block, &[]);
    } else {
        let mut check_block = unique_block;
        for (idx, (variant_tag, field_types)) in variants.iter().enumerate() {
            if idx > 0 {
                builder.switch_to_block(check_block);
            }
            let variant_release_block = builder.create_block();
            let next_check_or_free = if idx + 1 < variants.len() {
                builder.create_block()
            } else {
                free_block
            };

            let expected_tag = builder.ins().iconst(types::I32, i64::from(*variant_tag));
            let is_match = builder.ins().icmp(IntCC::Equal, tag_value, expected_tag);
            builder
                .ins()
                .brif(is_match, variant_release_block, &[], next_check_or_free, &[]);

            builder.switch_to_block(variant_release_block);
            for (field_idx, field_ty) in field_types.iter().enumerate() {
                if !is_managed_heap_type(field_ty) {
                    continue;
                }
                let field_offset = payload_offset
                    .checked_add(i32::try_from(field_idx.saturating_mul(8)).map_err(|_| {
                        CodegenError::UnsupportedMir {
                            function: type_name.to_string(),
                            detail: format!(
                                "sum `{type_name}` variant tag `{variant_tag}` field offset overflow"
                            ),
                        }
                    })?)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: type_name.to_string(),
                        detail: format!(
                            "sum `{type_name}` variant tag `{variant_tag}` field offset overflow"
                        ),
                    })?;
                let field_ptr = builder
                    .ins()
                    .load(ptr_ty, MemFlags::new(), payload_ptr, field_offset);
                emit_typed_release(
                    module,
                    &mut builder,
                    type_name,
                    field_ptr,
                    Some(field_ty),
                    drop_func_ids,
                    free_func_id,
                )?;
            }
            builder.ins().jump(free_block, &[]);
            check_block = next_check_or_free;
        }

        if check_block != free_block {
            builder.switch_to_block(check_block);
            builder.ins().jump(free_block, &[]);
        }
    }

    builder.switch_to_block(free_block);
    let free_func_id = free_func_id.ok_or_else(|| CodegenError::UnsupportedMir {
        function: type_name.to_string(),
        detail: "drop lowering requires imported `free` symbol".to_string(),
    })?;
    let free_ref = module.declare_func_in_func(free_func_id, builder.func);
    let _ = builder.ins().call(free_ref, &[rc_ptr]);
    builder.ins().jump(ret_block, &[]);

    builder.switch_to_block(ret_block);
    builder.ins().return_(&[]);
    builder.seal_all_blocks();
    builder.finalize();

    module
        .define_function(func_id, &mut context)
        .map_err(|detail| CodegenError::Module {
            detail: format!("drop function `{type_name}`: {detail:?}"),
        })?;
    module.clear_context(&mut context);
    Ok(())
}

fn define_drop_functions<M: Module>(
    module: &mut M,
    layout_plan: &BackendLayoutPlan,
    drop_func_ids: &DropFunctionIds,
    free_func_id: Option<FuncId>,
) -> Result<(), CodegenError> {
    for (record_name, layout) in &layout_plan.records {
        define_record_drop_function(module, record_name, layout, drop_func_ids, free_func_id)?;
    }
    for (sum_name, layout) in &layout_plan.sums {
        define_sum_drop_function(module, sum_name, layout, drop_func_ids, free_func_id)?;
    }
    Ok(())
}

fn lower_instruction<M: Module>(
    module: &mut M,
    builder: &mut FunctionBuilder,
    function_name: &str,
    inst: &MirInst,
    values: &mut BTreeMap<MirValueId, Value>,
    ctx: &LowerInstCtx<'_>,
) -> Result<bool, CodegenError> {
    match inst {
        MirInst::Const { dest, literal } => {
            let value = match literal {
                MirLiteral::String(text) => {
                    lower_string_literal(module, builder, function_name, ctx.malloc_func_id, text)?
                }
                _ => lower_literal(builder, literal, function_name)?,
            };
            values.insert(dest.clone(), value);
            Ok(false)
        }
        MirInst::Binary {
            dest,
            op,
            left,
            right,
        } => {
            let lhs = get_value(values, function_name, left)?;
            let rhs = get_value(values, function_name, right)?;
            let result = if *op == MirBinaryOp::Concat {
                lower_string_concat(module, builder, function_name, lhs, rhs, ctx)?
            } else {
                lower_binary(module, builder, function_name, *op, lhs, rhs)?
            };
            values.insert(dest.clone(), result);
            Ok(false)
        }
        MirInst::Unary { dest, op, operand } => {
            let value = get_value(values, function_name, operand)?;
            let result = lower_unary(builder, function_name, *op, value)?;
            values.insert(dest.clone(), result);
            Ok(false)
        }
        MirInst::RecordInit {
            dest,
            record_type,
            fields,
        } => {
            let layout = ctx.layout_plan.records.get(record_type).ok_or_else(|| {
                CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("record layout `{record_type}` not found"),
                }
            })?;
            let base_ptr = allocate_heap_payload(
                module,
                builder,
                function_name,
                ctx.malloc_func_id,
                layout.size_bytes,
                &format!(
                    "record allocation requested for `{record_type}` but malloc import was not declared"
                ),
            )?;
            store_record_fields(
                builder,
                function_name,
                layout,
                record_type,
                base_ptr,
                fields,
                values,
            )?;
            values.insert(dest.clone(), base_ptr);
            Ok(false)
        }
        MirInst::RecordInitReuse {
            dest,
            source,
            record_type,
            fields,
        } => {
            let layout = ctx.layout_plan.records.get(record_type).ok_or_else(|| {
                CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("record layout `{record_type}` not found"),
                }
            })?;
            let ptr_ty = module.target_config().pointer_type();
            let source_ptr = get_value(values, function_name, source)?;
            let source_ptr = coerce_value_to_clif_type(builder, source_ptr, ptr_ty);

            let unique_block = builder.create_block();
            let alloc_block = builder.create_block();
            let join_block = builder.create_block();
            builder.append_block_param(join_block, ptr_ty);

            let rc_ptr = builder.ins().iadd_imm(source_ptr, -8);
            let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
            let is_unique = builder.ins().icmp_imm(IntCC::Equal, rc_value, 1);
            builder
                .ins()
                .brif(is_unique, unique_block, &[], alloc_block, &[]);

            builder.switch_to_block(unique_block);
            store_record_fields(
                builder,
                function_name,
                layout,
                record_type,
                source_ptr,
                fields,
                values,
            )?;
            builder.ins().jump(join_block, &[source_ptr]);

            builder.switch_to_block(alloc_block);
            let source_ty = ctx.value_types.get(source);
            emit_typed_release(
                module,
                builder,
                function_name,
                source_ptr,
                source_ty,
                ctx.drop_func_ids,
                ctx.free_func_id,
            )?;
            let fresh_ptr = allocate_heap_payload(
                module,
                builder,
                function_name,
                ctx.malloc_func_id,
                layout.size_bytes,
                &format!(
                    "record allocation requested for `{record_type}` but malloc import was not declared"
                ),
            )?;
            store_record_fields(
                builder,
                function_name,
                layout,
                record_type,
                fresh_ptr,
                fields,
                values,
            )?;
            builder.ins().jump(join_block, &[fresh_ptr]);

            builder.switch_to_block(join_block);
            let result_ptr = builder
                .block_params(join_block)
                .first()
                .copied()
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("record reuse join block missing result for `{record_type}`"),
                })?;
            values.insert(dest.clone(), result_ptr);
            Ok(false)
        }
        MirInst::RecordInitFromToken {
            dest,
            token,
            record_type,
            fields,
        } => {
            let layout = ctx.layout_plan.records.get(record_type).ok_or_else(|| {
                CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("record layout `{record_type}` not found"),
                }
            })?;
            let ptr_ty = module.target_config().pointer_type();
            let token_ptr = get_value(values, function_name, token)?;
            let token_ptr = coerce_value_to_clif_type(builder, token_ptr, ptr_ty);

            let reuse_block = builder.create_block();
            let alloc_block = builder.create_block();
            let join_block = builder.create_block();
            builder.append_block_param(join_block, ptr_ty);

            let has_token = builder.ins().icmp_imm(IntCC::NotEqual, token_ptr, 0);
            builder
                .ins()
                .brif(has_token, reuse_block, &[], alloc_block, &[]);

            builder.switch_to_block(reuse_block);
            store_record_fields(
                builder,
                function_name,
                layout,
                record_type,
                token_ptr,
                fields,
                values,
            )?;
            builder.ins().jump(join_block, &[token_ptr]);

            builder.switch_to_block(alloc_block);
            let fresh_ptr = allocate_heap_payload(
                module,
                builder,
                function_name,
                ctx.malloc_func_id,
                layout.size_bytes,
                &format!(
                    "record allocation requested for `{record_type}` but malloc import was not declared"
                ),
            )?;
            store_record_fields(
                builder,
                function_name,
                layout,
                record_type,
                fresh_ptr,
                fields,
                values,
            )?;
            builder.ins().jump(join_block, &[fresh_ptr]);

            builder.switch_to_block(join_block);
            let result_ptr = builder
                .block_params(join_block)
                .first()
                .copied()
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("record token-init join block missing result for `{record_type}`"),
                })?;
            values.insert(dest.clone(), result_ptr);
            Ok(false)
        }
        MirInst::SumInit {
            dest,
            sum_type,
            variant,
            tag,
            fields,
        } => {
            let layout =
                ctx.layout_plan
                    .sums
                    .get(sum_type)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!("sum layout `{sum_type}` not found"),
                    })?;
            let base_ptr = allocate_heap_payload(
                module,
                builder,
                function_name,
                ctx.malloc_func_id,
                layout.size_bytes,
                &format!(
                    "sum allocation requested for `{sum_type}` but malloc import was not declared"
                ),
            )?;
            store_sum_init_payload(
                builder,
                function_name,
                layout,
                SumInitSpec {
                    sum_type,
                    variant,
                    tag: *tag,
                    fields,
                },
                values,
                base_ptr,
            )?;
            values.insert(dest.clone(), base_ptr);
            Ok(false)
        }
        MirInst::SumInitReuse {
            dest,
            source,
            sum_type,
            variant,
            tag,
            fields,
        } => {
            let layout =
                ctx.layout_plan
                    .sums
                    .get(sum_type)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!("sum layout `{sum_type}` not found"),
                    })?;
            if layout.variant_field_counts.values().any(|count| *count == 0) {
                return Err(CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "sum reuse for `{sum_type}` is not yet supported for unit/mixed variants"
                    ),
                });
            }
            let ptr_ty = module.target_config().pointer_type();
            let source_ptr = get_value(values, function_name, source)?;
            let source_ptr = coerce_value_to_clif_type(builder, source_ptr, ptr_ty);

            let unique_block = builder.create_block();
            let alloc_block = builder.create_block();
            let join_block = builder.create_block();
            builder.append_block_param(join_block, ptr_ty);

            let rc_ptr = builder.ins().iadd_imm(source_ptr, -8);
            let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
            let is_unique = builder.ins().icmp_imm(IntCC::Equal, rc_value, 1);
            builder
                .ins()
                .brif(is_unique, unique_block, &[], alloc_block, &[]);

            builder.switch_to_block(unique_block);
            store_sum_init_payload(
                builder,
                function_name,
                layout,
                SumInitSpec {
                    sum_type,
                    variant,
                    tag: *tag,
                    fields,
                },
                values,
                source_ptr,
            )?;
            builder.ins().jump(join_block, &[source_ptr]);

            builder.switch_to_block(alloc_block);
            let source_ty = ctx.value_types.get(source);
            emit_typed_release(
                module,
                builder,
                function_name,
                source_ptr,
                source_ty,
                ctx.drop_func_ids,
                ctx.free_func_id,
            )?;
            let fresh_ptr = allocate_heap_payload(
                module,
                builder,
                function_name,
                ctx.malloc_func_id,
                layout.size_bytes,
                &format!(
                    "sum allocation requested for `{sum_type}` but malloc import was not declared"
                ),
            )?;
            store_sum_init_payload(
                builder,
                function_name,
                layout,
                SumInitSpec {
                    sum_type,
                    variant,
                    tag: *tag,
                    fields,
                },
                values,
                fresh_ptr,
            )?;
            builder.ins().jump(join_block, &[fresh_ptr]);

            builder.switch_to_block(join_block);
            let result_ptr = builder
                .block_params(join_block)
                .first()
                .copied()
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("sum reuse join block missing result for `{sum_type}`"),
                })?;
            values.insert(dest.clone(), result_ptr);
            Ok(false)
        }
        MirInst::SumInitFromToken {
            dest,
            token,
            sum_type,
            variant,
            tag,
            fields,
        } => {
            let layout =
                ctx.layout_plan
                    .sums
                    .get(sum_type)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!("sum layout `{sum_type}` not found"),
                    })?;
            if layout.variant_field_counts.values().any(|count| *count == 0) {
                return Err(CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "sum token-init for `{sum_type}` is not yet supported for unit/mixed variants"
                    ),
                });
            }
            let ptr_ty = module.target_config().pointer_type();
            let token_ptr = get_value(values, function_name, token)?;
            let token_ptr = coerce_value_to_clif_type(builder, token_ptr, ptr_ty);

            let reuse_block = builder.create_block();
            let alloc_block = builder.create_block();
            let join_block = builder.create_block();
            builder.append_block_param(join_block, ptr_ty);

            let has_token = builder.ins().icmp_imm(IntCC::NotEqual, token_ptr, 0);
            builder
                .ins()
                .brif(has_token, reuse_block, &[], alloc_block, &[]);

            builder.switch_to_block(reuse_block);
            store_sum_init_payload(
                builder,
                function_name,
                layout,
                SumInitSpec {
                    sum_type,
                    variant,
                    tag: *tag,
                    fields,
                },
                values,
                token_ptr,
            )?;
            builder.ins().jump(join_block, &[token_ptr]);

            builder.switch_to_block(alloc_block);
            let fresh_ptr = allocate_heap_payload(
                module,
                builder,
                function_name,
                ctx.malloc_func_id,
                layout.size_bytes,
                &format!(
                    "sum allocation requested for `{sum_type}` but malloc import was not declared"
                ),
            )?;
            store_sum_init_payload(
                builder,
                function_name,
                layout,
                SumInitSpec {
                    sum_type,
                    variant,
                    tag: *tag,
                    fields,
                },
                values,
                fresh_ptr,
            )?;
            builder.ins().jump(join_block, &[fresh_ptr]);

            builder.switch_to_block(join_block);
            let result_ptr = builder
                .block_params(join_block)
                .first()
                .copied()
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("sum token-init join block missing result for `{sum_type}`"),
                })?;
            values.insert(dest.clone(), result_ptr);
            Ok(false)
        }
        MirInst::SumTagLoad {
            dest,
            sum,
            sum_type,
        } => {
            let base = get_value(values, function_name, sum)?;
            let layout =
                ctx.layout_plan
                    .sums
                    .get(sum_type)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!("sum layout `{sum_type}` not found"),
                    })?;
            let has_unit_variant = layout
                .variant_field_counts
                .values()
                .any(|count| *count == 0);
            let has_payload_variant = layout.variant_field_counts.values().any(|count| *count > 0);
            // Unit-only sums are represented as immediate integer tags in MIR
            // (e.g. `Ordering` constructors lower to `Const Int(tag)`).
            // Do not dereference these as heap pointers.
            if has_unit_variant && !has_payload_variant {
                values.insert(dest.clone(), base);
                return Ok(false);
            }
            // Mixed sums currently use a bootstrap representation where unit
            // variants are immediate tags while payload variants are pointers.
            // Distinguish them before loading a tag from memory.
            if has_unit_variant && has_payload_variant {
                let immediate_block = builder.create_block();
                let pointer_block = builder.create_block();
                let continue_block = builder.create_block();
                builder.append_block_param(continue_block, types::I64);

                let max_tag = i64::try_from(layout.variant_field_counts.len())
                    .ok()
                    .and_then(|len| len.checked_sub(1))
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "sum `{sum_type}` has invalid mixed-variant tag cardinality"
                        ),
                    })?;
                let is_immediate =
                    builder
                        .ins()
                        .icmp_imm(IntCC::UnsignedLessThanOrEqual, base, max_tag);
                builder
                    .ins()
                    .brif(is_immediate, immediate_block, &[], pointer_block, &[]);

                builder.switch_to_block(immediate_block);
                builder.ins().jump(continue_block, &[base]);

                builder.switch_to_block(pointer_block);
                let tag_offset =
                    i32::try_from(layout.tag_offset).map_err(|_| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!("sum tag offset for `{sum_type}` does not fit i32"),
                    })?;
                let tag_i32 = builder
                    .ins()
                    .load(types::I32, MemFlags::new(), base, tag_offset);
                let tag_i64 = builder.ins().uextend(types::I64, tag_i32);
                builder.ins().jump(continue_block, &[tag_i64]);

                builder.switch_to_block(continue_block);
                let tag = builder
                    .block_params(continue_block)
                    .first()
                    .copied()
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!("sum tag join block missing value for `{sum_type}`"),
                    })?;
                values.insert(dest.clone(), tag);
                return Ok(false);
            }
            let tag_offset =
                i32::try_from(layout.tag_offset).map_err(|_| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("sum tag offset for `{sum_type}` does not fit i32"),
                })?;
            let tag_i32 = builder
                .ins()
                .load(types::I32, MemFlags::new(), base, tag_offset);
            let tag_i64 = builder.ins().uextend(types::I64, tag_i32);
            values.insert(dest.clone(), tag_i64);
            Ok(false)
        }
        MirInst::SumPayloadLoad {
            dest,
            sum,
            sum_type,
            variant,
            field_index,
            field_ty,
        } => {
            let base = get_value(values, function_name, sum)?;
            let layout =
                ctx.layout_plan
                    .sums
                    .get(sum_type)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!("sum layout `{sum_type}` not found"),
                    })?;
            let expected_fields = *layout.variant_field_counts.get(variant).ok_or_else(|| {
                CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "sum layout `{sum_type}` missing variant `{variant}` during payload load"
                    ),
                }
            })?;
            if *field_index >= expected_fields as usize {
                return Err(CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "sum payload load `{sum_type}.{variant}[{field_index}]` out of bounds (arity {expected_fields})"
                    ),
                });
            }
            let payload_offset = layout.payload_offset + (*field_index as u32 * 8);
            let payload_offset =
                i32::try_from(payload_offset).map_err(|_| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "sum payload offset `{sum_type}.{variant}[{field_index}]` does not fit i32"
                    ),
                })?;
            let value_ty = clif_type(field_ty)?;
            let value = builder
                .ins()
                .load(value_ty, MemFlags::new(), base, payload_offset);
            if is_managed_heap_type(field_ty)
                && !sum_type_has_immediate_variants(field_ty, ctx.layout_plan)
            {
                let ptr_ty = module.target_config().pointer_type();
                let payload_ptr = coerce_value_to_clif_type(builder, value, ptr_ty);
                emit_retain(builder, payload_ptr);
            }
            values.insert(dest.clone(), value);
            Ok(false)
        }
        MirInst::RecordFieldLoad {
            dest,
            record,
            record_type,
            field,
            field_ty,
        } => {
            let base = get_value(values, function_name, record)?;
            let layout = ctx.layout_plan.records.get(record_type).ok_or_else(|| {
                CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("record layout `{record_type}` not found"),
                }
            })?;
            let offset =
                *layout
                    .field_offsets
                    .get(field)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "record layout `{record_type}` missing field `{field}` during lowering"
                        ),
                    })?;
            let addr = builder.ins().iadd_imm(base, i64::from(offset));
            let resolved_field_ty = if *field_ty == Type::Dynamic {
                layout
                    .field_types
                    .get(field)
                    .cloned()
                    .unwrap_or(Type::Dynamic)
            } else {
                field_ty.clone()
            };
            let value_ty = clif_type(&resolved_field_ty)?;
            let value = builder.ins().load(value_ty, MemFlags::new(), addr, 0);
            if is_managed_heap_type(&resolved_field_ty)
                && !sum_type_has_immediate_variants(&resolved_field_ty, ctx.layout_plan)
            {
                let ptr_ty = module.target_config().pointer_type();
                let payload_ptr = coerce_value_to_clif_type(builder, value, ptr_ty);
                emit_retain(builder, payload_ptr);
            }
            values.insert(dest.clone(), value);
            Ok(false)
        }
        MirInst::FunctionRef { dest, function } => {
            let func_id =
                *ctx.func_ids
                    .get(function)
                    .ok_or_else(|| CodegenError::UnknownFunction {
                        function: function.clone(),
                    })?;
            let func_ref = module.declare_func_in_func(func_id, builder.func);
            let ptr_ty = module.target_config().pointer_type();
            let addr = builder.ins().func_addr(ptr_ty, func_ref);
            values.insert(dest.clone(), addr);
            Ok(false)
        }
        MirInst::ClosureInit {
            dest,
            entry,
            captures,
            capture_types,
        } => {
            if captures.len() != capture_types.len() {
                return Err(CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "closure init capture arity mismatch: {} values, {} types",
                        captures.len(),
                        capture_types.len()
                    ),
                });
            }
            let ptr_ty = module.target_config().pointer_type();
            let closure_ptr = allocate_heap_payload(
                module,
                builder,
                function_name,
                ctx.malloc_func_id,
                (1 + captures.len()) as u32 * 8,
                "closure lowering requires malloc import",
            )?;

            let entry_value = get_value(values, function_name, entry)?;
            let entry_ptr = coerce_value_to_clif_type(builder, entry_value, ptr_ty);
            builder
                .ins()
                .store(MemFlags::new(), entry_ptr, closure_ptr, 0);

            for (idx, (capture, capture_ty)) in
                captures.iter().zip(capture_types.iter()).enumerate()
            {
                let capture_value = get_value(values, function_name, capture)?;
                let expected_capture_ty = clif_type(capture_ty)?;
                let capture_value =
                    coerce_value_to_clif_type(builder, capture_value, expected_capture_ty);
                let offset = ((idx + 1) * 8) as i32;
                builder
                    .ins()
                    .store(MemFlags::new(), capture_value, closure_ptr, offset);
            }

            values.insert(dest.clone(), closure_ptr);
            Ok(false)
        }
        MirInst::ClosureCaptureLoad {
            dest,
            closure,
            capture_index,
            capture_ty,
        } => {
            let closure_ptr = get_value(values, function_name, closure)?;
            let ptr_ty = module.target_config().pointer_type();
            let closure_ptr = coerce_value_to_clif_type(builder, closure_ptr, ptr_ty);
            let value_ty = clif_type(capture_ty)?;
            let offset = ((*capture_index + 1) * 8) as i32;
            let capture_value = builder
                .ins()
                .load(value_ty, MemFlags::new(), closure_ptr, offset);
            values.insert(dest.clone(), capture_value);
            Ok(false)
        }
        MirInst::StateCellNew { dest, initial } => {
            let ptr_ty = module.target_config().pointer_type();
            let initial_rc_mode = state_cell_rc_mode_for_value(initial, ctx);
            let initial = get_value(values, function_name, initial)?;
            let initial = coerce_value_to_clif_type(builder, initial, types::I64);
            let cell_ptr = allocate_heap_payload(
                module,
                builder,
                function_name,
                ctx.malloc_func_id,
                STATE_CELL_PAYLOAD_SIZE,
                "state cell allocation requested but malloc import was not declared",
            )?;
            let managed_flag = emit_state_cell_flag_and_retain(
                builder,
                initial,
                initial_rc_mode,
                ptr_ty,
            );
            builder.ins().store(
                MemFlags::new(),
                initial,
                cell_ptr,
                STATE_CELL_VALUE_OFFSET,
            );
            builder.ins().store(
                MemFlags::new(),
                managed_flag,
                cell_ptr,
                STATE_CELL_MANAGED_OFFSET,
            );
            values.insert(dest.clone(), cell_ptr);
            Ok(false)
        }
        MirInst::StateCellLoad { dest, cell } => {
            let ptr_ty = module.target_config().pointer_type();
            let cell_ptr = get_value(values, function_name, cell)?;
            let cell_ptr = coerce_value_to_clif_type(builder, cell_ptr, ptr_ty);
            let value = builder
                .ins()
                .load(types::I64, MemFlags::new(), cell_ptr, STATE_CELL_VALUE_OFFSET);
            let managed_flag = builder
                .ins()
                .load(types::I8, MemFlags::new(), cell_ptr, STATE_CELL_MANAGED_OFFSET);
            emit_retain_if_managed_flag(builder, value, managed_flag, ptr_ty);
            values.insert(dest.clone(), value);
            Ok(false)
        }
        MirInst::StateCellStore { cell, value } => {
            let ptr_ty = module.target_config().pointer_type();
            let rc_mode = state_cell_rc_mode_for_value(value, ctx);
            let cell_ptr = get_value(values, function_name, cell)?;
            let cell_ptr = coerce_value_to_clif_type(builder, cell_ptr, ptr_ty);
            let previous = builder
                .ins()
                .load(types::I64, MemFlags::new(), cell_ptr, STATE_CELL_VALUE_OFFSET);
            let previous_managed = builder
                .ins()
                .load(types::I8, MemFlags::new(), cell_ptr, STATE_CELL_MANAGED_OFFSET);
            emit_release_if_managed_flag(
                module,
                builder,
                function_name,
                previous,
                previous_managed,
                ptr_ty,
                ctx.free_func_id,
            )?;

            let value = get_value(values, function_name, value)?;
            let value = coerce_value_to_clif_type(builder, value, types::I64);
            let managed_flag =
                emit_state_cell_flag_and_retain(builder, value, rc_mode, ptr_ty);
            builder
                .ins()
                .store(MemFlags::new(), value, cell_ptr, STATE_CELL_VALUE_OFFSET);
            builder.ins().store(
                MemFlags::new(),
                managed_flag,
                cell_ptr,
                STATE_CELL_MANAGED_OFFSET,
            );
            Ok(false)
        }
        MirInst::Call {
            callee,
            args,
            arg_types,
            result,
            ret_type,
            callee_fail_result_abi,
            capture_fail_result,
            ..
        } => {
            if arg_types.len() != args.len() {
                return Err(CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "call has {} args but {} arg types",
                        args.len(),
                        arg_types.len()
                    ),
                });
            }
            let mut lowered_args = Vec::with_capacity(args.len());
            for (arg, arg_ty) in args.iter().zip(arg_types.iter()) {
                let raw = get_value(values, function_name, arg)?;
                lowered_args.push(coerce_value_to_type(builder, raw, arg_ty)?);
            }

            let mut callee_uses_fail_result_abi = false;
            let call_result = match callee {
                MirCallee::Local(name) => {
                    let runtime_sig = ctx.runtime_signatures.get(name).ok_or_else(|| {
                        CodegenError::UnknownFunction {
                            function: name.clone(),
                        }
                    })?;
                    callee_uses_fail_result_abi = runtime_sig.fail_result_abi;
                    if runtime_sig.runtime_params.len() != lowered_args.len() {
                        return Err(CodegenError::UnsupportedMir {
                            function: function_name.to_string(),
                            detail: format!(
                                "local call `{name}` has {} args but runtime signature expects {}",
                                lowered_args.len(),
                                runtime_sig.runtime_params.len()
                            ),
                        });
                    }
                    for (idx, expected_ty) in runtime_sig.runtime_params.iter().enumerate() {
                        lowered_args[idx] =
                            coerce_value_to_type(builder, lowered_args[idx], expected_ty)?;
                    }
                    let callee_id =
                        *ctx.func_ids
                            .get(name)
                            .ok_or_else(|| CodegenError::UnknownFunction {
                                function: name.clone(),
                            })?;
                    let local_ref = module.declare_func_in_func(callee_id, builder.func);
                    let call = builder.ins().call(local_ref, &lowered_args);
                    builder.inst_results(call).first().copied()
                }
                MirCallee::External(name) => {
                    let callee_id = *ctx.external_func_ids.get(name).ok_or_else(|| {
                        CodegenError::UnknownFunction {
                            function: name.clone(),
                        }
                    })?;
                    let external_ref = module.declare_func_in_func(callee_id, builder.func);
                    let call = builder.ins().call(external_ref, &lowered_args);
                    let call_result = builder.inst_results(call).first().copied();
                    if *ret_type == Type::Unit {
                        None
                    } else {
                        call_result
                    }
                }
                MirCallee::Value(_) => {
                    callee_uses_fail_result_abi = *callee_fail_result_abi;
                    let callee_value = if let MirCallee::Value(callee_value) = callee {
                        get_value(values, function_name, callee_value)?
                    } else {
                        unreachable!("matched Value callee above")
                    };
                    let ptr_ty = module.target_config().pointer_type();
                    let closure_ptr = coerce_value_to_clif_type(builder, callee_value, ptr_ty);
                    let callee_ptr = builder.ins().load(ptr_ty, MemFlags::new(), closure_ptr, 0);
                    let mut signature = module.make_signature();
                    signature.params.push(AbiParam::new(ptr_ty));
                    for arg_ty in arg_types {
                        signature.params.push(AbiParam::new(clif_type(arg_ty)?));
                    }
                    if callee_uses_fail_result_abi {
                        // Fail-only callees always return a runtime Result handle.
                        signature.returns.push(AbiParam::new(ptr_ty));
                    } else if *ret_type != Type::Unit {
                        signature.returns.push(AbiParam::new(clif_type(ret_type)?));
                    }
                    let sig_ref = builder.import_signature(signature);
                    let mut closure_call_args = Vec::with_capacity(lowered_args.len() + 1);
                    closure_call_args.push(closure_ptr);
                    closure_call_args.extend(lowered_args);
                    let call = builder
                        .ins()
                        .call_indirect(sig_ref, callee_ptr, &closure_call_args);
                    let call_result = builder.inst_results(call).first().copied();
                    if *ret_type == Type::Unit {
                        None
                    } else {
                        call_result
                    }
                }
            };

            if callee_uses_fail_result_abi {
                let result_ptr = call_result.ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: "Fail-only callee must return Result handle in runtime ABI".to_string(),
                })?;
                if *capture_fail_result {
                    let dest = result
                        .as_ref()
                        .ok_or_else(|| CodegenError::UnsupportedMir {
                            function: function_name.to_string(),
                            detail: "captured Fail-only call must produce a value".to_string(),
                        })?;
                    let ptr_ty = module.target_config().pointer_type();
                    let result_ptr = coerce_value_to_clif_type(builder, result_ptr, ptr_ty);
                    values.insert(dest.clone(), result_ptr);
                    return Ok(false);
                }
                let tag = builder
                    .ins()
                    .load(types::I32, MemFlags::new(), result_ptr, 0);
                let is_ok = builder.ins().icmp_imm(IntCC::Equal, tag, 0);
                let ok_block = builder.create_block();
                let err_block = builder.create_block();
                let continue_block = builder.create_block();
                builder.ins().brif(is_ok, ok_block, &[], err_block, &[]);

                builder.switch_to_block(err_block);
                if ctx.current_runtime_sig.fail_result_abi {
                    builder.ins().return_(&[result_ptr]);
                } else {
                    builder.ins().trap(TrapCode::unwrap_user(1));
                }

                builder.switch_to_block(ok_block);
                if let Some(dest) = result {
                    if *ret_type == Type::Unit {
                        values.insert(dest.clone(), builder.ins().iconst(types::I8, 0));
                    } else {
                        let payload_ty = clif_type(ret_type)?;
                        let payload =
                            builder
                                .ins()
                                .load(payload_ty, MemFlags::new(), result_ptr, 8);
                        values.insert(dest.clone(), payload);
                    }
                }
                builder.ins().jump(continue_block, &[]);
                builder.switch_to_block(continue_block);
                return Ok(false);
            }

            if let Some(dest) = result {
                let value = call_result.ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: "call expected to produce a value but returned unit".to_string(),
                })?;
                values.insert(dest.clone(), value);
            }

            Ok(false)
        }
        MirInst::EffectOp {
            class,
            effect,
            operation,
            args,
            result,
            ..
        } => {
            if *class == MirEffectOpClass::Direct {
                if !is_known_direct_capability_operation(effect, operation) {
                    return Err(CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "unknown direct capability operation `{effect}.{operation}`"
                        ),
                    });
                }
                if effect == "IO" {
                    let ptr_ty = module.target_config().pointer_type();
                    match operation.as_str() {
                        "stdout" => {
                            let arg = args.first().ok_or_else(|| CodegenError::UnsupportedMir {
                                function: function_name.to_string(),
                                detail: "IO.stdout expects one string argument".to_string(),
                            })?;
                            if args.len() != 1 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "IO.stdout expects exactly one string argument"
                                        .to_string(),
                                });
                            }
                            let arg_value = get_value(values, function_name, arg)?;
                            let arg_ptr = coerce_value_to_clif_type(builder, arg_value, ptr_ty);
                            let stdout_func_id =
                                ctx.stdout_func_id
                                    .ok_or_else(|| CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail:
                                            "IO.stdout lowering requires imported `puts` symbol"
                                                .to_string(),
                                    })?;
                            let stdout_ref =
                                module.declare_func_in_func(stdout_func_id, builder.func);
                            let _ = builder.ins().call(stdout_ref, &[arg_ptr]);
                            if let Some(dest) = result {
                                values.insert(dest.clone(), builder.ins().iconst(types::I8, 0));
                            }
                            Ok(false)
                        }
                        "stderr" => {
                            let arg = args.first().ok_or_else(|| CodegenError::UnsupportedMir {
                                function: function_name.to_string(),
                                detail: "IO.stderr expects one string argument".to_string(),
                            })?;
                            if args.len() != 1 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "IO.stderr expects exactly one string argument"
                                        .to_string(),
                                });
                            }
                            let arg_value = get_value(values, function_name, arg)?;
                            let arg_ptr = coerce_value_to_clif_type(builder, arg_value, ptr_ty);
                            let write_func_id =
                                ctx.write_func_id
                                    .ok_or_else(|| CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail:
                                            "IO.stderr lowering requires imported `write` symbol"
                                                .to_string(),
                                    })?;
                            let strlen_func_id =
                                ctx.strlen_func_id
                                    .ok_or_else(|| CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail:
                                            "IO.stderr lowering requires imported `strlen` symbol"
                                                .to_string(),
                                    })?;
                            let strlen_ref =
                                module.declare_func_in_func(strlen_func_id, builder.func);
                            let strlen_call = builder.ins().call(strlen_ref, &[arg_ptr]);
                            let len = builder
                                .inst_results(strlen_call)
                                .first()
                                .copied()
                                .ok_or_else(|| CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "strlen call returned no value".to_string(),
                                })?;
                            let len = coerce_value_to_clif_type(builder, len, ptr_ty);
                            let write_ref =
                                module.declare_func_in_func(write_func_id, builder.func);
                            let fd = builder.ins().iconst(types::I32, 2);
                            let _ = builder.ins().call(write_ref, &[fd, arg_ptr, len]);
                            if let Some(dest) = result {
                                values.insert(dest.clone(), builder.ins().iconst(types::I8, 0));
                            }
                            Ok(false)
                        }
                        "write_file" => {
                            if args.len() != 2 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "IO.write_file expects exactly two string arguments"
                                        .to_string(),
                                });
                            }
                            let path_value = get_value(values, function_name, &args[0])?;
                            let data_value = get_value(values, function_name, &args[1])?;
                            let path_ptr = coerce_value_to_clif_type(builder, path_value, ptr_ty);
                            let data_ptr = coerce_value_to_clif_type(builder, data_value, ptr_ty);
                            let write_file_func_id = ctx.io_write_file_func_id.ok_or_else(|| {
                                    CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail: "IO.write_file lowering requires imported `__kea_io_write_file` symbol".to_string(),
                                    }
                                })?;
                            let write_file_ref =
                                module.declare_func_in_func(write_file_func_id, builder.func);
                            let _ = builder.ins().call(write_file_ref, &[path_ptr, data_ptr]);
                            if let Some(dest) = result {
                                values.insert(dest.clone(), builder.ins().iconst(types::I8, 0));
                            }
                            Ok(false)
                        }
                        "read_file" => {
                            let arg = args.first().ok_or_else(|| CodegenError::UnsupportedMir {
                                function: function_name.to_string(),
                                detail: "IO.read_file expects one string argument".to_string(),
                            })?;
                            if args.len() != 1 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "IO.read_file expects exactly one string argument"
                                        .to_string(),
                                });
                            }
                            let path_value = get_value(values, function_name, arg)?;
                            let path_ptr = coerce_value_to_clif_type(builder, path_value, ptr_ty);
                            let read_file_func_id = ctx.io_read_file_func_id.ok_or_else(|| {
                                    CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail: "IO.read_file lowering requires imported `__kea_io_read_file` symbol".to_string(),
                                    }
                                })?;
                            let read_file_ref =
                                module.declare_func_in_func(read_file_func_id, builder.func);
                            let read_call = builder.ins().call(read_file_ref, &[path_ptr]);
                            if let Some(dest) = result {
                                let raw = builder
                                    .inst_results(read_call)
                                    .first()
                                    .copied()
                                    .ok_or_else(|| CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail: "IO.read_file call returned no value".to_string(),
                                    })?;
                                values.insert(
                                    dest.clone(),
                                    coerce_value_to_clif_type(builder, raw, ptr_ty),
                                );
                            }
                            Ok(false)
                        }
                        _ => Err(CodegenError::UnsupportedMir {
                            function: function_name.to_string(),
                            detail: format!(
                                "instruction `{inst:?}` not implemented in 0d pure lowering"
                            ),
                        }),
                    }
                } else if effect == "Clock" && matches!(operation.as_str(), "now" | "monotonic") {
                    if !args.is_empty() {
                        return Err(CodegenError::UnsupportedMir {
                            function: function_name.to_string(),
                            detail: format!("Clock.{operation} expects no arguments"),
                        });
                    }
                    let clock_func_id = match operation.as_str() {
                        "now" => ctx.clock_now_func_id,
                        "monotonic" => ctx.clock_monotonic_func_id,
                        _ => None,
                    }
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "Clock.{operation} lowering requires imported clock runtime symbol"
                        ),
                    })?;
                    let clock_ref = module.declare_func_in_func(clock_func_id, builder.func);
                    let clock_call = builder.ins().call(clock_ref, &[]);
                    if let Some(dest) = result {
                        let timestamp = builder
                            .inst_results(clock_call)
                            .first()
                            .copied()
                            .ok_or_else(|| CodegenError::UnsupportedMir {
                                function: function_name.to_string(),
                                detail: format!("Clock.{operation} call returned no value"),
                            })?;
                        let ptr_ty = module.target_config().pointer_type();
                        values.insert(dest.clone(), coerce_value_to_clif_type(builder, timestamp, ptr_ty));
                    }
                    Ok(false)
                } else if effect == "Rand" && matches!(operation.as_str(), "int" | "seed") {
                    match operation.as_str() {
                        "int" => {
                            if !args.is_empty() {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Rand.int expects no arguments".to_string(),
                                });
                            }
                            let rand_func_id =
                                ctx.rand_func_id
                                    .ok_or_else(|| CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail: "Rand.int lowering requires imported `rand` symbol"
                                            .to_string(),
                                    })?;
                            let rand_ref = module.declare_func_in_func(rand_func_id, builder.func);
                            let rand_call = builder.ins().call(rand_ref, &[]);
                            if let Some(dest) = result {
                                let raw = builder
                                    .inst_results(rand_call)
                                    .first()
                                    .copied()
                                    .ok_or_else(|| CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail: "rand call returned no value".to_string(),
                                    })?;
                                let as_i64 = coerce_value_to_clif_type(builder, raw, types::I64);
                                values.insert(dest.clone(), as_i64);
                            }
                            Ok(false)
                        }
                        "seed" => {
                            let seed_value_id =
                                args.first().ok_or_else(|| CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Rand.seed expects one Int argument".to_string(),
                                })?;
                            if args.len() != 1 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Rand.seed expects exactly one Int argument"
                                        .to_string(),
                                });
                            }
                            let seed_value = get_value(values, function_name, seed_value_id)?;
                            let seed_value =
                                coerce_value_to_clif_type(builder, seed_value, types::I32);
                            let srand_func_id =
                                ctx.srand_func_id
                                    .ok_or_else(|| CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail:
                                            "Rand.seed lowering requires imported `srand` symbol"
                                                .to_string(),
                                    })?;
                            let srand_ref =
                                module.declare_func_in_func(srand_func_id, builder.func);
                            let _ = builder.ins().call(srand_ref, &[seed_value]);
                            if let Some(dest) = result {
                                values.insert(dest.clone(), builder.ins().iconst(types::I8, 0));
                            }
                            Ok(false)
                        }
                        _ => unreachable!("Rand branch is guarded by operation match"),
                    }
                } else if effect == "Net"
                    && matches!(operation.as_str(), "connect" | "send" | "recv")
                {
                    match operation.as_str() {
                        "connect" => {
                            let addr_value_id =
                                args.first().ok_or_else(|| CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Net.connect expects one String argument".to_string(),
                                })?;
                            if args.len() != 1 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Net.connect expects exactly one String argument"
                                        .to_string(),
                                });
                            }
                            let addr_value = get_value(values, function_name, addr_value_id)?;
                            let ptr_ty = module.target_config().pointer_type();
                            let addr_ptr = coerce_value_to_clif_type(builder, addr_value, ptr_ty);
                            let connect_func_id = ctx.net_connect_func_id.ok_or_else(|| {
                                CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail:
                                        "Net.connect lowering requires imported `__kea_net_connect` symbol"
                                            .to_string(),
                                }
                            })?;
                            let connect_ref =
                                module.declare_func_in_func(connect_func_id, builder.func);
                            let connect_call = builder.ins().call(connect_ref, &[addr_ptr]);
                            if let Some(dest) = result {
                                let conn = builder
                                    .inst_results(connect_call)
                                    .first()
                                    .copied()
                                    .ok_or_else(|| CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail: "Net.connect call returned no value".to_string(),
                                    })?;
                                values.insert(
                                    dest.clone(),
                                    coerce_value_to_clif_type(builder, conn, types::I64),
                                );
                            }
                            Ok(false)
                        }
                        "send" => {
                            if args.len() != 2 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Net.send expects exactly two arguments".to_string(),
                                });
                            }
                            let conn_value = get_value(values, function_name, &args[0])?;
                            let data_value = get_value(values, function_name, &args[1])?;
                            let conn_value =
                                coerce_value_to_clif_type(builder, conn_value, types::I64);
                            let ptr_ty = module.target_config().pointer_type();
                            let data_ptr = coerce_value_to_clif_type(builder, data_value, ptr_ty);
                            let send_func_id = ctx.net_send_func_id.ok_or_else(|| {
                                CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail:
                                        "Net.send lowering requires imported `__kea_net_send` symbol"
                                            .to_string(),
                                }
                            })?;
                            let send_ref = module.declare_func_in_func(send_func_id, builder.func);
                            let _ = builder.ins().call(send_ref, &[conn_value, data_ptr]);
                            if let Some(dest) = result {
                                values.insert(dest.clone(), builder.ins().iconst(types::I8, 0));
                            }
                            Ok(false)
                        }
                        "recv" => {
                            if args.len() != 2 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Net.recv expects exactly two arguments".to_string(),
                                });
                            }
                            let conn_value = get_value(values, function_name, &args[0])?;
                            let size_value = get_value(values, function_name, &args[1])?;
                            let conn_value =
                                coerce_value_to_clif_type(builder, conn_value, types::I64);
                            let size_value =
                                coerce_value_to_clif_type(builder, size_value, types::I64);
                            let recv_func_id = ctx.net_recv_func_id.ok_or_else(|| {
                                CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail:
                                        "Net.recv lowering requires imported `__kea_net_recv` symbol"
                                            .to_string(),
                                }
                            })?;
                            let recv_ref = module.declare_func_in_func(recv_func_id, builder.func);
                            let recv_call = builder.ins().call(recv_ref, &[conn_value, size_value]);
                            if let Some(dest) = result {
                                let received = builder
                                    .inst_results(recv_call)
                                    .first()
                                    .copied()
                                    .ok_or_else(|| CodegenError::UnsupportedMir {
                                        function: function_name.to_string(),
                                        detail: "Net.recv call returned no value".to_string(),
                                    })?;
                                values.insert(
                                    dest.clone(),
                                    coerce_value_to_clif_type(builder, received, types::I64),
                                );
                            }
                            Ok(false)
                        }
                        _ => unreachable!("Net branch is guarded by operation match"),
                    }
                } else {
                    Err(CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "instruction `{inst:?}` not implemented in 0d pure lowering"
                        ),
                    })
                }
            } else if *class == MirEffectOpClass::ZeroResume
                && effect == "Fail"
                && operation == "fail"
            {
                if result.is_some() {
                    return Err(CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail:
                            "Fail.zero-resume operation must not produce a value in 0d lowering"
                                .to_string(),
                    });
                }
                if let Type::Result(_, err_ty) = &ctx.current_runtime_sig.runtime_return {
                    let payload_value_id = args.first().ok_or_else(|| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail:
                            "Fail.zero-resume operation in Result-returning function requires one payload argument"
                                .to_string(),
                    })?;
                    let payload = get_value(values, function_name, payload_value_id)?;
                    let result_ptr = lower_result_allocation(
                        module,
                        builder,
                        function_name,
                        ctx.malloc_func_id,
                        1,
                        payload,
                        err_ty,
                    )?;
                    builder.ins().return_(&[result_ptr]);
                    return Ok(true);
                }
                builder.ins().trap(TrapCode::unwrap_user(1));
                Ok(true)
            } else if *class == MirEffectOpClass::Dispatch {
                Err(CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "effect operation `{effect}.{operation}` requires evidence dispatch \
                         (Tier 3) but no handler cell was threaded — ensure the effect is \
                         handled or the function receives dispatch parameters"
                    ),
                })
            } else {
                Err(CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("instruction `{inst:?}` not implemented in 0d pure lowering"),
                })
            }
        }
        MirInst::Unsupported { detail } => Err(CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: detail.clone(),
        }),
        MirInst::Nop => Ok(false),
        MirInst::Retain { value } => {
            let ptr_ty = module.target_config().pointer_type();
            let payload_ptr = get_value(values, function_name, value)?;
            let payload_ptr = coerce_value_to_clif_type(builder, payload_ptr, ptr_ty);
            emit_retain(builder, payload_ptr);
            Ok(false)
        }
        MirInst::Release { value } => {
            let ptr_ty = module.target_config().pointer_type();
            let payload_ptr = get_value(values, function_name, value)?;
            let payload_ptr = coerce_value_to_clif_type(builder, payload_ptr, ptr_ty);
            let value_ty = ctx.value_types.get(value);
            if matches!(
                value_ty,
                Some(Type::Opaque { name, .. }) if name == STATE_CELL_TYPE_MARKER
            ) {
                let free_func_id = ctx.free_func_id.ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: "state-cell release lowering requires imported `free` symbol"
                        .to_string(),
                })?;
                let rc_ptr = builder.ins().iadd_imm(payload_ptr, -8);
                let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
                let next = builder.ins().iadd_imm(rc_value, -1);
                builder.ins().store(MemFlags::new(), next, rc_ptr, 0);

                let free_block = builder.create_block();
                let cont_block = builder.create_block();
                let is_zero = builder.ins().icmp_imm(IntCC::Equal, next, 0);
                builder
                    .ins()
                    .brif(is_zero, free_block, &[], cont_block, &[]);

                builder.switch_to_block(free_block);
                let stored_value = builder.ins().load(
                    types::I64,
                    MemFlags::new(),
                    payload_ptr,
                    STATE_CELL_VALUE_OFFSET,
                );
                let stored_managed = builder.ins().load(
                    types::I8,
                    MemFlags::new(),
                    payload_ptr,
                    STATE_CELL_MANAGED_OFFSET,
                );
                emit_release_if_managed_flag(
                    module,
                    builder,
                    function_name,
                    stored_value,
                    stored_managed,
                    ptr_ty,
                    ctx.free_func_id,
                )?;
                let free_ref = module.declare_func_in_func(free_func_id, builder.func);
                let _ = builder.ins().call(free_ref, &[rc_ptr]);
                builder.ins().jump(cont_block, &[]);
                builder.switch_to_block(cont_block);
                return Ok(false);
            }
            emit_typed_release(
                module,
                builder,
                function_name,
                payload_ptr,
                value_ty,
                ctx.drop_func_ids,
                ctx.free_func_id,
            )?;
            Ok(false)
        }
        MirInst::ReuseToken { dest, source } => {
            let ptr_ty = module.target_config().pointer_type();
            let source_ptr = get_value(values, function_name, source)?;
            let source_ptr = coerce_value_to_clif_type(builder, source_ptr, ptr_ty);

            let unique_block = builder.create_block();
            let release_block = builder.create_block();
            let join_block = builder.create_block();
            builder.append_block_param(join_block, ptr_ty);

            let rc_ptr = builder.ins().iadd_imm(source_ptr, -8);
            let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
            let is_unique = builder.ins().icmp_imm(IntCC::Equal, rc_value, 1);
            builder
                .ins()
                .brif(is_unique, unique_block, &[], release_block, &[]);

            builder.switch_to_block(unique_block);
            builder.ins().jump(join_block, &[source_ptr]);

            builder.switch_to_block(release_block);
            let source_ty = ctx.value_types.get(source);
            emit_typed_release(
                module,
                builder,
                function_name,
                source_ptr,
                source_ty,
                ctx.drop_func_ids,
                ctx.free_func_id,
            )?;
            let null_token = builder.ins().iconst(ptr_ty, 0);
            builder.ins().jump(join_block, &[null_token]);

            builder.switch_to_block(join_block);
            let token_ptr = builder
                .block_params(join_block)
                .first()
                .copied()
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: "reuse-token join block missing token value".to_string(),
                })?;
            values.insert(dest.clone(), token_ptr);
            Ok(false)
        }
        MirInst::Move { dest, src }
        | MirInst::Borrow { dest, src }
        | MirInst::TryClaim { dest, src }
        | MirInst::Freeze { dest, src } => {
            let value = get_value(values, function_name, src)?;
            values.insert(dest.clone(), value);
            Ok(false)
        }
        MirInst::CowUpdate {
            dest,
            target,
            record_type,
            updates,
            ..
        } => {
            let target_ptr = get_value(values, function_name, target)?;
            let layout = ctx.layout_plan.records.get(record_type).ok_or_else(|| {
                CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("record layout `{record_type}` not found"),
                }
            })?;

            let mut update_values = BTreeMap::new();
            for update in updates {
                if !layout.field_offsets.contains_key(&update.field) {
                    return Err(CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "record layout `{record_type}` missing field `{}` during update",
                            update.field
                        ),
                    });
                }
                update_values.insert(
                    update.field.clone(),
                    get_value(values, function_name, &update.value)?,
                );
            }

            let ptr_ty = module.target_config().pointer_type();
            let unique_block = builder.create_block();
            let copy_block = builder.create_block();
            let join_block = builder.create_block();
            builder.append_block_param(join_block, ptr_ty);

            let rc_ptr = builder.ins().iadd_imm(target_ptr, -8);
            let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
            let is_unique = builder.ins().icmp_imm(IntCC::Equal, rc_value, 1);
            builder
                .ins()
                .brif(is_unique, unique_block, &[], copy_block, &[]);

            builder.switch_to_block(unique_block);
            for (field_name, updated) in &update_values {
                let offset_u32 =
                    *layout
                        .field_offsets
                        .get(field_name)
                        .ok_or_else(|| CodegenError::UnsupportedMir {
                            function: function_name.to_string(),
                            detail: format!(
                                "record layout `{record_type}` missing field `{field_name}` during in-place update"
                            ),
                        })?;
                let offset =
                    i32::try_from(offset_u32).map_err(|_| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "record field `{record_type}.{field_name}` offset does not fit i32"
                        ),
                    })?;
                let field_ty = layout
                    .field_types
                    .get(field_name)
                    .cloned()
                    .unwrap_or(Type::Dynamic);
                let value_ty = clif_type(&field_ty)?;
                let value = coerce_value_to_clif_type(builder, *updated, value_ty);
                builder
                    .ins()
                    .store(MemFlags::new(), value, target_ptr, offset);
            }
            builder.ins().jump(join_block, &[target_ptr]);

            builder.switch_to_block(copy_block);
            let out_ptr = allocate_heap_payload(
                module,
                builder,
                function_name,
                ctx.malloc_func_id,
                layout.size_bytes,
                &format!(
                    "record allocation requested for `{record_type}` but malloc import was not declared"
                ),
            )?;
            for (field_name, offset_u32) in &layout.field_offsets {
                let offset =
                    i32::try_from(*offset_u32).map_err(|_| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "record field `{record_type}.{field_name}` offset does not fit i32"
                        ),
                    })?;
                let field_ty = layout
                    .field_types
                    .get(field_name)
                    .cloned()
                    .unwrap_or(Type::Dynamic);
                let value_ty = clif_type(&field_ty)?;
                let value = if let Some(updated) = update_values.get(field_name) {
                    coerce_value_to_clif_type(builder, *updated, value_ty)
                } else {
                    builder
                        .ins()
                        .load(value_ty, MemFlags::new(), target_ptr, offset)
                };
                builder.ins().store(MemFlags::new(), value, out_ptr, offset);
            }
            builder.ins().jump(join_block, &[out_ptr]);

            builder.switch_to_block(join_block);
            let merged = builder.block_params(join_block)[0];
            values.insert(dest.clone(), merged);
            Ok(false)
        }
        MirInst::HandlerEnter { .. } | MirInst::HandlerExit { .. } => Ok(false),
        MirInst::Resume { .. } => Err(CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "Resume instruction reached codegen — non-tail resume should be \
                     decomposed during MIR lowering (compiler bug)"
                .to_string(),
        }),
    }
}

fn lower_literal(
    builder: &mut FunctionBuilder,
    literal: &MirLiteral,
    function_name: &str,
) -> Result<Value, CodegenError> {
    match literal {
        MirLiteral::Int(value) => Ok(builder.ins().iconst(types::I64, *value)),
        MirLiteral::Float(value) => Ok(builder.ins().f64const(*value)),
        MirLiteral::Bool(value) => Ok(builder.ins().iconst(types::I8, if *value { 1 } else { 0 })),
        MirLiteral::Unit => Ok(builder.ins().iconst(types::I8, 0)),
        MirLiteral::String(_) => Err(CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "string constants are not implemented in 0d pure lowering".to_string(),
        }),
    }
}

fn lower_string_concat(
    module: &mut impl Module,
    builder: &mut FunctionBuilder,
    function_name: &str,
    lhs: Value,
    rhs: Value,
    ctx: &LowerInstCtx<'_>,
) -> Result<Value, CodegenError> {
    let ptr_ty = module.target_config().pointer_type();
    let lhs_ptr = coerce_value_to_clif_type(builder, lhs, ptr_ty);
    let rhs_ptr = coerce_value_to_clif_type(builder, rhs, ptr_ty);

    let strlen_func_id = ctx
        .strlen_func_id
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "string concat lowering requires imported `strlen` symbol".to_string(),
        })?;
    let memcpy_func_id = ctx
        .memcpy_func_id
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "string concat lowering requires imported `memcpy` symbol".to_string(),
        })?;

    let strlen_ref = module.declare_func_in_func(strlen_func_id, builder.func);
    let memcpy_ref = module.declare_func_in_func(memcpy_func_id, builder.func);

    let lhs_len_call = builder.ins().call(strlen_ref, &[lhs_ptr]);
    let lhs_len = builder
        .inst_results(lhs_len_call)
        .first()
        .copied()
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "strlen(lhs) returned no value".to_string(),
        })?;

    let rhs_len_call = builder.ins().call(strlen_ref, &[rhs_ptr]);
    let rhs_len = builder
        .inst_results(rhs_len_call)
        .first()
        .copied()
        .ok_or_else(|| CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: "strlen(rhs) returned no value".to_string(),
        })?;

    let joined_len = builder.ins().iadd(lhs_len, rhs_len);
    let alloc_payload_bytes = builder.ins().iadd_imm(joined_len, 1);
    let out_ptr = allocate_heap_payload_dynamic(
        module,
        builder,
        function_name,
        ctx.malloc_func_id,
        alloc_payload_bytes,
        "string concat lowering requires malloc import",
    )?;

    let _ = builder.ins().call(memcpy_ref, &[out_ptr, lhs_ptr, lhs_len]);
    let rhs_dest = builder.ins().iadd(out_ptr, lhs_len);
    let _ = builder
        .ins()
        .call(memcpy_ref, &[rhs_dest, rhs_ptr, rhs_len]);

    let nul_dest = builder.ins().iadd(out_ptr, joined_len);
    let nul = builder.ins().iconst(types::I8, 0);
    builder.ins().store(MemFlags::new(), nul, nul_dest, 0);
    Ok(out_ptr)
}

fn declare_void_panic_func(
    module: &mut impl Module,
    name: &str,
) -> Result<FuncId, CodegenError> {
    let mut sig = module.make_signature();
    sig.params.clear();
    sig.returns.clear();
    module
        .declare_function(name, Linkage::Import, &sig)
        .map_err(|detail| CodegenError::Module {
            detail: detail.to_string(),
        })
}

fn lower_binary(
    module: &mut impl Module,
    builder: &mut FunctionBuilder,
    function_name: &str,
    op: MirBinaryOp,
    lhs: Value,
    rhs: Value,
) -> Result<Value, CodegenError> {
    let lhs_ty = builder.func.dfg.value_type(lhs);
    let rhs_ty = builder.func.dfg.value_type(rhs);

    if lhs_ty != rhs_ty {
        return Err(CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: format!("binary operands have mismatched types `{lhs_ty}` and `{rhs_ty}`"),
        });
    }

    let value = match op {
        MirBinaryOp::Add if lhs_ty.is_int() => builder.ins().iadd(lhs, rhs),
        MirBinaryOp::Sub if lhs_ty.is_int() => builder.ins().isub(lhs, rhs),
        MirBinaryOp::Mul if lhs_ty.is_int() => builder.ins().imul(lhs, rhs),
        MirBinaryOp::WrappingAdd if lhs_ty.is_int() => builder.ins().iadd(lhs, rhs),
        MirBinaryOp::WrappingSub if lhs_ty.is_int() => builder.ins().isub(lhs, rhs),
        MirBinaryOp::WrappingMul if lhs_ty.is_int() => builder.ins().imul(lhs, rhs),
        MirBinaryOp::Div if lhs_ty.is_int() => {
            let panic_id = declare_void_panic_func(module, "__kea_panic_div_zero")?;
            let panic_ref = module.declare_func_in_func(panic_id, builder.func);

            let zero_block = builder.create_block();
            let ok_block = builder.create_block();
            let is_zero = builder.ins().icmp_imm(IntCC::Equal, rhs, 0);
            builder.ins().brif(is_zero, zero_block, &[], ok_block, &[]);

            builder.switch_to_block(zero_block);
            builder.ins().call(panic_ref, &[]);
            builder.ins().trap(TrapCode::unwrap_user(1));

            builder.switch_to_block(ok_block);
            builder.ins().sdiv(lhs, rhs)
        }
        MirBinaryOp::Mod if lhs_ty.is_int() => {
            let panic_id = declare_void_panic_func(module, "__kea_panic_mod_zero")?;
            let panic_ref = module.declare_func_in_func(panic_id, builder.func);

            let zero_block = builder.create_block();
            let ok_block = builder.create_block();
            let is_zero = builder.ins().icmp_imm(IntCC::Equal, rhs, 0);
            builder.ins().brif(is_zero, zero_block, &[], ok_block, &[]);

            builder.switch_to_block(zero_block);
            builder.ins().call(panic_ref, &[]);
            builder.ins().trap(TrapCode::unwrap_user(1));

            builder.switch_to_block(ok_block);
            builder.ins().srem(lhs, rhs)
        }

        MirBinaryOp::Add if lhs_ty.is_float() => builder.ins().fadd(lhs, rhs),
        MirBinaryOp::Sub if lhs_ty.is_float() => builder.ins().fsub(lhs, rhs),
        MirBinaryOp::Mul if lhs_ty.is_float() => builder.ins().fmul(lhs, rhs),
        MirBinaryOp::Div if lhs_ty.is_float() => builder.ins().fdiv(lhs, rhs),

        MirBinaryOp::Eq if lhs_ty.is_int() => {
            let pred = builder.ins().icmp(IntCC::Equal, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Neq if lhs_ty.is_int() => {
            let pred = builder.ins().icmp(IntCC::NotEqual, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Lt if lhs_ty.is_int() => {
            let pred = builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Lte if lhs_ty.is_int() => {
            let pred = builder.ins().icmp(IntCC::SignedLessThanOrEqual, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Gt if lhs_ty.is_int() => {
            let pred = builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Gte if lhs_ty.is_int() => {
            let pred = builder
                .ins()
                .icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs);
            b1_to_i8(builder, pred)
        }

        MirBinaryOp::Eq if lhs_ty.is_float() => {
            let pred = builder.ins().fcmp(FloatCC::Equal, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Neq if lhs_ty.is_float() => {
            let pred = builder.ins().fcmp(FloatCC::NotEqual, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Lt if lhs_ty.is_float() => {
            let pred = builder.ins().fcmp(FloatCC::LessThan, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Lte if lhs_ty.is_float() => {
            let pred = builder.ins().fcmp(FloatCC::LessThanOrEqual, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Gt if lhs_ty.is_float() => {
            let pred = builder.ins().fcmp(FloatCC::GreaterThan, lhs, rhs);
            b1_to_i8(builder, pred)
        }
        MirBinaryOp::Gte if lhs_ty.is_float() => {
            let pred = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, lhs, rhs);
            b1_to_i8(builder, pred)
        }

        MirBinaryOp::And if lhs_ty.is_int() => builder.ins().band(lhs, rhs),
        MirBinaryOp::Or if lhs_ty.is_int() => builder.ins().bor(lhs, rhs),
        MirBinaryOp::BitAnd if lhs_ty.is_int() => builder.ins().band(lhs, rhs),
        MirBinaryOp::BitOr if lhs_ty.is_int() => builder.ins().bor(lhs, rhs),
        MirBinaryOp::BitXor if lhs_ty.is_int() => builder.ins().bxor(lhs, rhs),
        MirBinaryOp::ShiftLeft if lhs_ty.is_int() => builder.ins().ishl(lhs, rhs),
        MirBinaryOp::ShiftRight if lhs_ty.is_int() => builder.ins().sshr(lhs, rhs),
        MirBinaryOp::ShiftRightUnsigned if lhs_ty.is_int() => builder.ins().ushr(lhs, rhs),

        _ => {
            return Err(CodegenError::UnsupportedMir {
                function: function_name.to_string(),
                detail: format!(
                    "binary operation `{op:?}` unsupported for Cranelift type `{lhs_ty}`"
                ),
            });
        }
    };

    Ok(value)
}

fn lower_unary(
    builder: &mut FunctionBuilder,
    function_name: &str,
    op: MirUnaryOp,
    value: Value,
) -> Result<Value, CodegenError> {
    let value_ty = builder.func.dfg.value_type(value);
    let result = match op {
        MirUnaryOp::Neg if value_ty.is_int() => builder.ins().ineg(value),
        MirUnaryOp::Neg if value_ty.is_float() => builder.ins().fneg(value),
        MirUnaryOp::Not if value_ty.bits() == 1 => {
            let pred = builder.ins().bnot(value);
            b1_to_i8(builder, pred)
        }
        MirUnaryOp::Not if value_ty.is_int() => {
            let pred = builder.ins().icmp_imm(IntCC::Equal, value, 0);
            b1_to_i8(builder, pred)
        }
        MirUnaryOp::BitNot if value_ty.is_int() => builder.ins().bnot(value),
        MirUnaryOp::Popcount if value_ty.is_int() => builder.ins().popcnt(value),
        MirUnaryOp::LeadingZeros if value_ty.is_int() => builder.ins().clz(value),
        MirUnaryOp::TrailingZeros if value_ty.is_int() => builder.ins().ctz(value),
        MirUnaryOp::WidenSignedToInt if value_ty.is_int() && value_ty.bits() < 64 => {
            builder.ins().sextend(types::I64, value)
        }
        MirUnaryOp::WidenUnsignedToInt if value_ty.is_int() && value_ty.bits() < 64 => {
            builder.ins().uextend(types::I64, value)
        }
        MirUnaryOp::WidenSignedToInt if value_ty == types::I64 => value,
        MirUnaryOp::WidenUnsignedToInt if value_ty == types::I64 => value,
        _ => {
            return Err(CodegenError::UnsupportedMir {
                function: function_name.to_string(),
                detail: format!(
                    "unary operation `{op:?}` unsupported for Cranelift type `{value_ty}`"
                ),
            });
        }
    };
    Ok(result)
}

fn b1_to_i8(builder: &mut FunctionBuilder, predicate: Value) -> Value {
    let ty = builder.func.dfg.value_type(predicate);
    if ty == types::I8 {
        predicate
    } else if ty.bits() == 1 {
        builder.ins().uextend(types::I8, predicate)
    } else {
        predicate
    }
}

struct LowerTerminatorCtx<'a> {
    function_name: &'a str,
    function: &'a MirFunction,
    current_runtime_sig: &'a RuntimeFunctionSig,
    malloc_func_id: Option<FuncId>,
    values: &'a BTreeMap<MirValueId, Value>,
    block_map: &'a BTreeMap<kea_mir::MirBlockId, cranelift::prelude::Block>,
    func_ids: &'a BTreeMap<String, FuncId>,
}

fn lower_terminator(
    module: &mut impl Module,
    builder: &mut FunctionBuilder,
    block: &kea_mir::MirBlock,
    ctx: &LowerTerminatorCtx<'_>,
) -> Result<(), CodegenError> {
    if builder.is_unreachable() {
        // Instructions like `trap` terminate the block immediately.
        // Skip MIR terminator lowering for blocks that are already closed.
        return Ok(());
    }

    if let Some(tail_call) = detect_tail_self_call(ctx.function, block) {
        let callee_id =
            *ctx.func_ids
                .get(ctx.function_name)
                .ok_or_else(|| CodegenError::UnknownFunction {
                    function: ctx.function_name.to_string(),
                })?;
        let callee_ref = module.declare_func_in_func(callee_id, builder.func);
        let mut lowered_args = Vec::with_capacity(tail_call.args.len());
        for arg in &tail_call.args {
            lowered_args.push(get_value(ctx.values, ctx.function_name, arg)?);
        }
        builder.ins().return_call(callee_ref, &lowered_args);
        return Ok(());
    }

    match &block.terminator {
        MirTerminator::Return { value } => {
            if ctx.current_runtime_sig.fail_result_abi {
                let payload = if ctx.current_runtime_sig.logical_return == Type::Unit {
                    builder.ins().iconst(types::I8, 0)
                } else {
                    let value_id = value.as_ref().ok_or_else(|| CodegenError::UnsupportedMir {
                        function: ctx.function_name.to_string(),
                        detail:
                            "function declares a non-Unit return type but lowered body produced no return value; this shape is not yet supported in compiled lowering"
                                .to_string(),
                    })?;
                    get_value(ctx.values, ctx.function_name, value_id)?
                };
                let result_ptr = lower_result_allocation(
                    module,
                    builder,
                    ctx.function_name,
                    ctx.malloc_func_id,
                    0,
                    payload,
                    &ctx.current_runtime_sig.logical_return,
                )?;
                builder.ins().return_(&[result_ptr]);
                return Ok(());
            }

            if ctx.current_runtime_sig.runtime_return == Type::Unit {
                if ctx.function_name == "main" {
                    let zero = builder.ins().iconst(types::I32, 0);
                    builder.ins().return_(&[zero]);
                } else {
                    builder.ins().return_(&[]);
                }
                return Ok(());
            }

            let value_id = value.as_ref().ok_or_else(|| CodegenError::UnsupportedMir {
                function: ctx.function_name.to_string(),
                detail:
                    "function declares a non-Unit return type but lowered body produced no return value; this shape is not yet supported in compiled lowering"
                        .to_string(),
            })?;
            let mut value = get_value(ctx.values, ctx.function_name, value_id)?;
            let expected_ret_clif_ty =
                if ctx.function_name == "main" && ctx.current_runtime_sig.logical_return == Type::Int
                {
                    types::I32
                } else {
                    clif_type(&ctx.current_runtime_sig.runtime_return)?
                };
            value = coerce_value_to_clif_type(builder, value, expected_ret_clif_ty);
            builder.ins().return_(&[value]);
            Ok(())
        }
        MirTerminator::Jump { target, args } => {
            let target_block =
                *ctx.block_map
                    .get(target)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: ctx.function_name.to_string(),
                        detail: format!("jump target block {:?} not found", target),
                    })?;
            let mut lowered_args = Vec::with_capacity(args.len());
            for arg in args {
                lowered_args.push(get_value(ctx.values, ctx.function_name, arg)?);
            }
            builder.ins().jump(target_block, &lowered_args);
            Ok(())
        }
        MirTerminator::Branch {
            condition,
            then_block,
            else_block,
        } => {
            let cond = get_value(ctx.values, ctx.function_name, condition)?;
            let then_clif =
                *ctx.block_map
                    .get(then_block)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: ctx.function_name.to_string(),
                        detail: format!("then block {:?} not found", then_block),
                    })?;
            let else_clif =
                *ctx.block_map
                    .get(else_block)
                    .ok_or_else(|| CodegenError::UnsupportedMir {
                        function: ctx.function_name.to_string(),
                        detail: format!("else block {:?} not found", else_block),
                    })?;

            let cond_ty = builder.func.dfg.value_type(cond);
            let bool_pred = if cond_ty.bits() == 1 {
                cond
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, cond, 0)
            };
            builder
                .ins()
                .brif(bool_pred, then_clif, &[], else_clif, &[]);
            Ok(())
        }
        MirTerminator::Unreachable => {
            builder
                .ins()
                .trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
            Ok(())
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TailSelfCall {
    args: Vec<MirValueId>,
}

fn detect_tail_self_call(function: &MirFunction, block: &kea_mir::MirBlock) -> Option<TailSelfCall> {
    let MirInst::Call {
        callee: MirCallee::Local(callee_name),
        args,
        arg_types,
        result,
        ..
    } = block.instructions.last()?
    else {
        return None;
    };

    if callee_name != &function.name {
        return None;
    }

    if !forwards_handler_cell_args_unchanged(function, args, arg_types) {
        return None;
    }

    if matches!(
        (&block.terminator, result),
        (MirTerminator::Return { value: Some(ret) }, Some(call_result)) if ret == call_result
    ) {
        return Some(TailSelfCall { args: args.clone() });
    }

    if matches!((&block.terminator, result), (MirTerminator::Return { value: None }, None)) {
        return Some(TailSelfCall { args: args.clone() });
    }

    let (MirTerminator::Jump { target, args: jump_args }, Some(call_result)) = (&block.terminator, result) else {
        return None;
    };
    let target_block = function.blocks.iter().find(|candidate| candidate.id == *target)?;
    if !target_block
        .instructions
        .iter()
        .all(|inst| matches!(inst, MirInst::Nop))
    {
        return None;
    }
    if target_block.params.len() != jump_args.len() {
        return None;
    }
    let MirTerminator::Return { value: Some(ret) } = &target_block.terminator else {
        return None;
    };
    let ret_param_idx = target_block.params.iter().position(|param| &param.id == ret)?;
    if jump_args.get(ret_param_idx) != Some(call_result) {
        return None;
    }
    Some(TailSelfCall { args: args.clone() })
}

fn forwards_handler_cell_args_unchanged(
    function: &MirFunction,
    call_args: &[MirValueId],
    call_arg_types: &[Type],
) -> bool {
    let hidden_cell_count = function
        .signature
        .effects
        .row
        .fields
        .iter()
        .map(|(label, _)| label.as_str())
        .filter(|effect| *effect != "Fail")
        .filter(|effect| !is_direct_capability_effect(effect))
        .count();
    if hidden_cell_count == 0 {
        return true;
    }
    if call_args.len() < hidden_cell_count || call_arg_types.len() < hidden_cell_count {
        return false;
    }
    let hidden_start = call_args.len() - hidden_cell_count;
    for (idx, arg) in call_args.iter().enumerate().skip(hidden_start) {
        if *arg != MirValueId(idx as u32) {
            return false;
        }
        if call_arg_types.get(idx) != Some(&Type::Dynamic) {
            return false;
        }
        if function.signature.params.get(idx) != Some(&Type::Dynamic) {
            return false;
        }
    }
    true
}

fn get_value(
    values: &BTreeMap<MirValueId, Value>,
    function_name: &str,
    value_id: &MirValueId,
) -> Result<Value, CodegenError> {
    values
        .get(value_id)
        .copied()
        .ok_or_else(|| CodegenError::InvalidMirValue {
            function: function_name.to_string(),
            value: value_id.0,
        })
}

pub fn validate_abi_manifest(module: &MirModule, abi: &AbiManifest) -> Result<(), CodegenError> {
    for function in &module.functions {
        let Some(sig) = abi.get(&function.name) else {
            return Err(CodegenError::MissingAbiEntry {
                function: function.name.clone(),
            });
        };

        let expected_params = function.signature.params.len();
        let actual_params = sig.param_classes.len();
        if expected_params != actual_params {
            return Err(CodegenError::AbiParamCountMismatch {
                function: function.name.clone(),
                expected: expected_params,
                actual: actual_params,
            });
        }
    }
    Ok(())
}

fn validate_layout_catalog(module: &MirModule) -> Result<(), CodegenError> {
    let mut type_names = BTreeSet::new();

    for record in &module.layouts.records {
        if !type_names.insert(record.name.clone()) {
            return Err(CodegenError::DuplicateLayoutType {
                name: record.name.clone(),
            });
        }
        let mut seen_fields = BTreeSet::new();
        for field in &record.fields {
            if !seen_fields.insert(field.name.clone()) {
                return Err(CodegenError::DuplicateLayoutField {
                    type_name: record.name.clone(),
                    field: field.name.clone(),
                });
            }
        }
    }

    for sum in &module.layouts.sums {
        if !type_names.insert(sum.name.clone()) {
            return Err(CodegenError::DuplicateLayoutType {
                name: sum.name.clone(),
            });
        }
        let mut seen_variant_names = BTreeSet::new();
        let mut seen_tags = BTreeSet::new();
        for variant in &sum.variants {
            if !seen_variant_names.insert(variant.name.clone()) {
                return Err(CodegenError::DuplicateLayoutVariant {
                    type_name: sum.name.clone(),
                    variant: variant.name.clone(),
                });
            }
            seen_tags.insert(variant.tag);
        }

        let expected_tags: BTreeSet<u32> = (0..sum.variants.len() as u32).collect();
        if seen_tags != expected_tags {
            return Err(CodegenError::InvalidLayoutVariantTags {
                type_name: sum.name.clone(),
            });
        }
    }

    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct BackendLayoutPlan {
    records: BTreeMap<String, BackendRecordLayout>,
    sums: BTreeMap<String, BackendSumLayout>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BackendRecordLayout {
    size_bytes: u32,
    align_bytes: u32,
    field_offsets: BTreeMap<String, u32>,
    field_types: BTreeMap<String, Type>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BackendSumLayout {
    size_bytes: u32,
    align_bytes: u32,
    tag_offset: u32,
    payload_offset: u32,
    max_payload_fields: u32,
    variant_tags: BTreeMap<String, u32>,
    variant_field_counts: BTreeMap<String, u32>,
    variant_field_types: BTreeMap<String, Vec<Type>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct DropFunctionIds {
    records: BTreeMap<String, FuncId>,
    sums: BTreeMap<String, FuncId>,
}

fn align_up(value: u32, align: u32) -> u32 {
    if align == 0 {
        return value;
    }
    let rem = value % align;
    if rem == 0 {
        value
    } else {
        value + (align - rem)
    }
}

fn annotation_to_backend_type(
    annotation: &kea_ast::TypeAnnotation,
    record_names: &BTreeSet<String>,
    sum_names: &BTreeSet<String>,
) -> Type {
    match annotation {
        kea_ast::TypeAnnotation::Named(name) => match name.as_str() {
            "Int" => Type::Int,
            "Float" => Type::Float,
            "Bool" => Type::Bool,
            "String" => Type::String,
            "Unit" => Type::Unit,
            _ if record_names.contains(name) => Type::Record(RecordType {
                name: name.clone(),
                params: Vec::new(),
                row: kea_types::RowType::closed(Vec::new()),
            }),
            _ if sum_names.contains(name) => Type::Sum(SumType {
                name: name.clone(),
                type_args: Vec::new(),
                variants: Vec::new(),
            }),
            _ => Type::Dynamic,
        },
        kea_ast::TypeAnnotation::Applied(name, args) => {
            if name == "Option" && args.len() == 1 {
                let inner = annotation_to_backend_type(&args[0], record_names, sum_names);
                Type::Option(Box::new(inner))
            } else if name == "Result" && args.len() == 2 {
                let ok_ty = annotation_to_backend_type(&args[0], record_names, sum_names);
                let err_ty = annotation_to_backend_type(&args[1], record_names, sum_names);
                Type::Result(Box::new(ok_ty), Box::new(err_ty))
            } else if record_names.contains(name) {
                Type::Record(RecordType {
                    name: name.clone(),
                    params: Vec::new(),
                    row: kea_types::RowType::closed(Vec::new()),
                })
            } else if sum_names.contains(name) {
                Type::Sum(SumType {
                    name: name.clone(),
                    type_args: Vec::new(),
                    variants: Vec::new(),
                })
            } else {
                Type::Dynamic
            }
        }
        kea_ast::TypeAnnotation::Optional(inner) => Type::Option(Box::new(
            annotation_to_backend_type(inner, record_names, sum_names),
        )),
        _ => Type::Dynamic,
    }
}

fn plan_layout_catalog(module: &MirModule) -> Result<BackendLayoutPlan, CodegenError> {
    const WORD_BYTES: u32 = 8;
    const TAG_BYTES: u32 = 4;

    let mut plan = BackendLayoutPlan::default();
    let record_names: BTreeSet<String> = module
        .layouts
        .records
        .iter()
        .map(|record| record.name.clone())
        .collect();
    let sum_names: BTreeSet<String> = module
        .layouts
        .sums
        .iter()
        .map(|sum| sum.name.clone())
        .collect();

    for record in &module.layouts.records {
        let mut field_offsets = BTreeMap::new();
        let mut field_types = BTreeMap::new();
        for (idx, field) in record.fields.iter().enumerate() {
            field_offsets.insert(field.name.clone(), idx as u32 * WORD_BYTES);
            let field_ty = annotation_to_backend_type(&field.annotation, &record_names, &sum_names);
            field_types.insert(field.name.clone(), field_ty);
        }
        let size_bytes = record.fields.len() as u32 * WORD_BYTES;
        plan.records.insert(
            record.name.clone(),
            BackendRecordLayout {
                size_bytes,
                align_bytes: WORD_BYTES,
                field_offsets,
                field_types,
            },
        );
    }

    for sum in &module.layouts.sums {
        let mut variant_tags = BTreeMap::new();
        let mut variant_field_counts = BTreeMap::new();
        let mut variant_field_types = BTreeMap::new();
        let max_payload_fields = sum
            .variants
            .iter()
            .map(|variant| variant.fields.len() as u32)
            .max()
            .unwrap_or(0);
        for variant in &sum.variants {
            variant_tags.insert(variant.name.clone(), variant.tag);
            variant_field_counts.insert(variant.name.clone(), variant.fields.len() as u32);
            let fields = variant
                .fields
                .iter()
                .map(|field| annotation_to_backend_type(&field.annotation, &record_names, &sum_names))
                .collect::<Vec<_>>();
            variant_field_types.insert(variant.name.clone(), fields);
        }
        let payload_offset = align_up(TAG_BYTES, WORD_BYTES);
        let size_bytes = payload_offset + max_payload_fields * WORD_BYTES;
        plan.sums.insert(
            sum.name.clone(),
            BackendSumLayout {
                size_bytes,
                align_bytes: WORD_BYTES,
                tag_offset: 0,
                payload_offset,
                max_payload_fields,
                variant_tags,
                variant_field_counts,
                variant_field_types,
            },
        );
    }

    Ok(plan)
}

fn is_fail_only_effect_row(row: &EffectRow) -> bool {
    row.row.rest.is_none()
        && !row.row.fields.is_empty()
        && row
            .row
            .fields
            .iter()
            .all(|(label, _)| label.as_str() == "Fail")
}

fn validate_fail_only_invariants(module: &MirModule) -> Result<(), CodegenError> {
    for function in &module.functions {
        if !is_fail_only_effect_row(&function.signature.effects) {
            continue;
        }

        for block in &function.blocks {
            for inst in &block.instructions {
                match inst {
                    MirInst::EffectOp {
                        class,
                        effect,
                        operation,
                        result,
                        ..
                    } => {
                        if effect != "Fail" {
                            return Err(CodegenError::FailOnlyInvariantViolation {
                                function: function.name.clone(),
                                detail: format!(
                                    "block {} performs non-Fail effect op `{effect}.{operation}`",
                                    block.id.0
                                ),
                            });
                        }

                        if *class != MirEffectOpClass::ZeroResume {
                            return Err(CodegenError::FailOnlyInvariantViolation {
                                function: function.name.clone(),
                                detail: format!(
                                    "block {} lowers `Fail.{operation}` as {class:?}; expected ZeroResume Result path",
                                    block.id.0
                                ),
                            });
                        }
                        if result.is_some() {
                            return Err(CodegenError::FailOnlyInvariantViolation {
                                function: function.name.clone(),
                                detail: format!(
                                    "block {} lowers `Fail.{operation}` with a result value; zero-resume Fail must not return",
                                    block.id.0
                                ),
                            });
                        }
                    }
                    MirInst::HandlerEnter { effect } => {
                        return Err(CodegenError::FailOnlyInvariantViolation {
                            function: function.name.clone(),
                            detail: format!(
                                "block {} enters handler `{effect}` in Fail-only function",
                                block.id.0
                            ),
                        });
                    }
                    MirInst::HandlerExit { effect } => {
                        return Err(CodegenError::FailOnlyInvariantViolation {
                            function: function.name.clone(),
                            detail: format!(
                                "block {} exits handler `{effect}` in Fail-only function",
                                block.id.0
                            ),
                        });
                    }
                    MirInst::Resume { .. } => {
                        return Err(CodegenError::FailOnlyInvariantViolation {
                            function: function.name.clone(),
                            detail: format!(
                                "block {} uses `resume` in Fail-only function",
                                block.id.0
                            ),
                        });
                    }
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

pub fn collect_pass_stats(module: &MirModule) -> PassStats {
    let per_function = module
        .functions
        .iter()
        .map(collect_function_stats)
        .collect::<Vec<_>>();
    PassStats { per_function }
}

fn collect_function_stats(function: &MirFunction) -> FunctionPassStats {
    let mut stats = FunctionPassStats {
        function: function.name.clone(),
        ..FunctionPassStats::default()
    };

    for block in &function.blocks {
        if detect_tail_self_call(function, block).is_some() {
            stats.tail_self_call_count += 1;
        }
        for inst in &block.instructions {
            match inst {
                MirInst::Retain { .. } => stats.retain_count += 1,
                MirInst::Release { .. } => stats.release_count += 1,
                MirInst::ReuseToken { .. } => {
                    stats.release_count += 1;
                    stats.reuse_token_produced_count += 1;
                }
                MirInst::Call { .. } => {}
                MirInst::HandlerEnter { .. } => stats.handler_enter_count += 1,
                MirInst::HandlerExit { .. } => stats.handler_exit_count += 1,
                MirInst::Resume { .. } => stats.resume_count += 1,
                MirInst::EffectOp { class, .. } => match class {
                    MirEffectOpClass::Direct => stats.effect_op_direct_count += 1,
                    MirEffectOpClass::Dispatch => stats.effect_op_dispatch_count += 1,
                    MirEffectOpClass::ZeroResume => stats.effect_op_zero_resume_count += 1,
                },
                MirInst::RecordInitReuse { .. } => {
                    stats.alloc_count += 1;
                    stats.reuse_count += 1;
                }
                MirInst::SumInitReuse { .. } => {
                    stats.alloc_count += 1;
                    stats.reuse_count += 1;
                }
                MirInst::RecordInitFromToken { .. } | MirInst::SumInitFromToken { .. } => {
                    stats.alloc_count += 1;
                    stats.reuse_token_consumed_count += 1;
                }
                MirInst::CowUpdate { .. }
                | MirInst::RecordInit { .. }
                | MirInst::SumInit { .. }
                | MirInst::ClosureInit { .. }
                | MirInst::StateCellNew { .. } => stats.alloc_count += 1,
                MirInst::Const { .. }
                | MirInst::Binary { .. }
                | MirInst::Unary { .. }
                | MirInst::StateCellLoad { .. }
                | MirInst::StateCellStore { .. }
                | MirInst::SumTagLoad { .. }
                | MirInst::SumPayloadLoad { .. }
                | MirInst::RecordFieldLoad { .. }
                | MirInst::ClosureCaptureLoad { .. }
                | MirInst::FunctionRef { .. }
                | MirInst::Unsupported { .. }
                | MirInst::Move { .. }
                | MirInst::Borrow { .. }
                | MirInst::TryClaim { .. }
                | MirInst::Freeze { .. }
                | MirInst::Nop => {}
            }
        }
    }

    let layout_keys = infer_heap_layout_keys_for_stats(function);
    stats.reuse_token_candidate_count =
        collect_reuse_token_candidate_count(function, &layout_keys);
    stats.trmc_candidate_count = collect_trmc_candidate_count(function);

    stats
}

fn collect_trmc_candidate_count(function: &MirFunction) -> usize {
    function
        .blocks
        .iter()
        .filter(|block| block_contains_trmc_candidate(function, block))
        .count()
}

fn block_contains_trmc_candidate(function: &MirFunction, block: &kea_mir::MirBlock) -> bool {
    let Some(return_value) = block_return_value(function, block) else {
        return false;
    };
    for (idx, inst) in block.instructions.iter().enumerate().rev() {
        let recursive_value = match inst {
            MirInst::RecordInit { dest, fields, .. } if dest == &return_value => fields
                .iter()
                .find_map(|(_, value)| {
                    inst_is_recursive_self_call_result(function, &block.instructions[..idx], value)
                }),
            MirInst::SumInit { dest, fields, .. } if dest == &return_value => fields
                .iter()
                .find_map(|value| {
                    inst_is_recursive_self_call_result(function, &block.instructions[..idx], value)
                }),
            _ => None,
        };
        if recursive_value.is_some() {
            return true;
        }
        if inst_defines_value(inst, &return_value) {
            break;
        }
    }
    false
}

fn block_return_value(function: &MirFunction, block: &kea_mir::MirBlock) -> Option<MirValueId> {
    match &block.terminator {
        MirTerminator::Return { value: Some(value) } => Some(value.clone()),
        MirTerminator::Jump { target, args } => {
            let target_block = function.blocks.iter().find(|candidate| candidate.id == *target)?;
            if !target_block
                .instructions
                .iter()
                .all(|inst| matches!(inst, MirInst::Nop))
            {
                return None;
            }
            let MirTerminator::Return {
                value: Some(target_return_value),
            } = &target_block.terminator
            else {
                return None;
            };
            let return_param_idx = target_block
                .params
                .iter()
                .position(|param| &param.id == target_return_value)?;
            args.get(return_param_idx).cloned()
        }
        _ => None,
    }
}

fn inst_is_recursive_self_call_result(
    function: &MirFunction,
    prefix: &[MirInst],
    value: &MirValueId,
) -> Option<MirValueId> {
    prefix.iter().rev().find_map(|inst| match inst {
        MirInst::Call {
            callee: MirCallee::Local(callee_name),
            result: Some(result_value),
            ..
        } if callee_name == &function.name && result_value == value => Some(result_value.clone()),
        _ => None,
    })
}

fn inst_defines_value(inst: &MirInst, value: &MirValueId) -> bool {
    match inst {
        MirInst::Const { dest, .. }
        | MirInst::Binary { dest, .. }
        | MirInst::Unary { dest, .. }
        | MirInst::RecordInit { dest, .. }
        | MirInst::RecordInitReuse { dest, .. }
        | MirInst::ReuseToken { dest, .. }
        | MirInst::RecordInitFromToken { dest, .. }
        | MirInst::SumInit { dest, .. }
        | MirInst::SumInitReuse { dest, .. }
        | MirInst::SumInitFromToken { dest, .. }
        | MirInst::SumTagLoad { dest, .. }
        | MirInst::SumPayloadLoad { dest, .. }
        | MirInst::RecordFieldLoad { dest, .. }
        | MirInst::FunctionRef { dest, .. }
        | MirInst::ClosureInit { dest, .. }
        | MirInst::ClosureCaptureLoad { dest, .. }
        | MirInst::StateCellNew { dest, .. }
        | MirInst::StateCellLoad { dest, .. }
        | MirInst::Move { dest, .. }
        | MirInst::Borrow { dest, .. }
        | MirInst::TryClaim { dest, .. }
        | MirInst::Freeze { dest, .. } => dest == value,
        MirInst::StateCellStore { .. }
        | MirInst::Retain { .. }
        | MirInst::Release { .. }
        | MirInst::CowUpdate { .. }
        | MirInst::EffectOp { .. }
        | MirInst::HandlerExit { .. }
        | MirInst::Resume { .. }
        | MirInst::Unsupported { .. }
        | MirInst::Nop => false,
        MirInst::Call { result, .. } => result.as_ref() == Some(value),
        MirInst::HandlerEnter { .. } => false,
    }
}

fn collect_reuse_token_candidate_count(
    function: &MirFunction,
    layout_keys: &BTreeMap<MirValueId, String>,
) -> usize {
    let block_index_by_id = function
        .blocks
        .iter()
        .enumerate()
        .map(|(idx, block)| (block.id.clone(), idx))
        .collect::<BTreeMap<_, _>>();

    let mut count = 0;
    for (block_idx, block) in function.blocks.iter().enumerate() {
        for (inst_idx, inst) in block.instructions.iter().enumerate() {
            let MirInst::Release { value } = inst else {
                continue;
            };
            let Some(layout) = layout_keys.get(value) else {
                continue;
            };
            if has_reachable_unfused_alloc_of_layout(
                function,
                &block_index_by_id,
                block_idx,
                inst_idx + 1,
                layout,
            ) {
                count += 1;
            }
        }
    }
    count
}

fn has_reachable_unfused_alloc_of_layout(
    function: &MirFunction,
    block_index_by_id: &BTreeMap<MirBlockId, usize>,
    start_block_idx: usize,
    start_inst_idx: usize,
    target_layout: &str,
) -> bool {
    let mut stack = vec![(start_block_idx, start_inst_idx)];
    let mut visited = BTreeSet::<(usize, usize)>::new();
    while let Some((block_idx, inst_idx)) = stack.pop() {
        if !visited.insert((block_idx, inst_idx)) {
            continue;
        }
        let block = &function.blocks[block_idx];
        for inst in block.instructions.iter().skip(inst_idx) {
            if inst_alloc_layout_key(inst).is_some_and(|layout| layout == target_layout) {
                return true;
            }
        }

        match &block.terminator {
            MirTerminator::Jump { target, .. } => {
                if let Some(next_idx) = block_index_by_id.get(target).copied() {
                    stack.push((next_idx, 0));
                }
            }
            MirTerminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                if let Some(next_idx) = block_index_by_id.get(then_block).copied() {
                    stack.push((next_idx, 0));
                }
                if let Some(next_idx) = block_index_by_id.get(else_block).copied() {
                    stack.push((next_idx, 0));
                }
            }
            MirTerminator::Return { .. } | MirTerminator::Unreachable => {}
        }
    }
    false
}

fn inst_alloc_layout_key(inst: &MirInst) -> Option<String> {
    match inst {
        MirInst::RecordInit { record_type, .. }
        | MirInst::RecordInitFromToken { record_type, .. } => Some(format!("record:{record_type}")),
        MirInst::SumInit { sum_type, .. } | MirInst::SumInitFromToken { sum_type, .. } => {
            Some(format!("sum:{sum_type}"))
        }
        _ => None,
    }
}

fn infer_heap_layout_keys_for_stats(function: &MirFunction) -> BTreeMap<MirValueId, String> {
    let mut layout_keys = BTreeMap::new();
    let block_index_by_id = function
        .blocks
        .iter()
        .enumerate()
        .map(|(idx, block)| (block.id.clone(), idx))
        .collect::<BTreeMap<_, _>>();

    for block in &function.blocks {
        for param in &block.params {
            if let Some(layout) = heap_layout_key_from_type(&param.ty) {
                layout_keys.insert(param.id.clone(), layout);
            }
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in &function.blocks {
            for inst in &block.instructions {
                match inst {
                    MirInst::RecordInit {
                        dest, record_type, ..
                    }
                    | MirInst::RecordInitReuse {
                        dest, record_type, ..
                    }
                    | MirInst::RecordInitFromToken {
                        dest, record_type, ..
                    } => {
                        let layout = format!("record:{record_type}");
                        if layout_keys.get(dest) != Some(&layout) {
                            layout_keys.insert(dest.clone(), layout);
                            changed = true;
                        }
                    }
                    MirInst::SumInit { dest, sum_type, .. }
                    | MirInst::SumInitReuse { dest, sum_type, .. }
                    | MirInst::SumInitFromToken { dest, sum_type, .. } => {
                        let layout = format!("sum:{sum_type}");
                        if layout_keys.get(dest) != Some(&layout) {
                            layout_keys.insert(dest.clone(), layout);
                            changed = true;
                        }
                    }
                    MirInst::Move { dest, src }
                    | MirInst::Borrow { dest, src }
                    | MirInst::TryClaim { dest, src }
                    | MirInst::Freeze { dest, src }
                    | MirInst::ReuseToken {
                        dest, source: src, ..
                    } => {
                        if let Some(layout) = layout_keys.get(src).cloned()
                            && layout_keys.get(dest) != Some(&layout)
                        {
                            layout_keys.insert(dest.clone(), layout);
                            changed = true;
                        }
                    }
                    _ => {}
                }
            }

            if let MirTerminator::Jump { target, args } = &block.terminator
                && let Some(target_idx) = block_index_by_id.get(target).copied()
            {
                let target_block = &function.blocks[target_idx];
                for (arg, param) in args.iter().zip(target_block.params.iter()) {
                    match (
                        layout_keys.get(arg).cloned(),
                        layout_keys.get(&param.id).cloned(),
                    ) {
                        (Some(layout), None) => {
                            layout_keys.insert(param.id.clone(), layout);
                            changed = true;
                        }
                        (None, Some(layout)) => {
                            layout_keys.insert(arg.clone(), layout);
                            changed = true;
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    layout_keys
}

fn heap_layout_key_from_type(ty: &Type) -> Option<String> {
    match ty {
        Type::Record(record) => Some(format!("record:{}", record.name)),
        Type::Sum(sum) => Some(format!("sum:{}", sum.name)),
        Type::Option(_) => Some("sum:Option".to_string()),
        Type::Result(_, _) => Some("sum:Result".to_string()),
        _ => None,
    }
}

pub fn default_abi_manifest(module: &MirModule) -> AbiManifest {
    let functions = module
        .functions
        .iter()
        .map(|function| {
            let effect_evidence = if function.signature.effects.is_pure() {
                AbiEffectEvidencePlacement::None
            } else {
                AbiEffectEvidencePlacement::TrailingParam
            };

            (
                function.name.clone(),
                AbiFunctionSignature {
                    param_classes: vec![AbiParamClass::Value; function.signature.params.len()],
                    return_style: AbiReturnStyle::Value,
                    effect_evidence,
                    effects: function.signature.effects.clone(),
                },
            )
        })
        .collect();

    AbiManifest { functions }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kea_hir::{HirDecl, HirExpr, HirExprKind, HirFunction, HirParam};
    use kea_mir::{
        MirBlock, MirBlockId, MirBlockParam, MirFunctionSignature, MirLayoutCatalog, MirRecordFieldLayout,
        MirRecordLayout, MirSumLayout, MirTerminator, MirVariantFieldLayout, MirVariantLayout,
    };
    use kea_types::{FunctionType, Label, RecordType, RowType, SumType};

    #[test]
    fn clif_type_maps_precision_int_widths() {
        assert_eq!(
            clif_type(&Type::IntN(IntWidth::I8, Signedness::Signed)).unwrap(),
            types::I8
        );
        assert_eq!(
            clif_type(&Type::IntN(IntWidth::I16, Signedness::Unsigned)).unwrap(),
            types::I16
        );
        assert_eq!(
            clif_type(&Type::IntN(IntWidth::I32, Signedness::Signed)).unwrap(),
            types::I32
        );
        assert_eq!(
            clif_type(&Type::IntN(IntWidth::I64, Signedness::Unsigned)).unwrap(),
            types::I64
        );
    }

    #[test]
    fn clif_type_maps_precision_float_widths() {
        assert_eq!(clif_type(&Type::FloatN(FloatWidth::F32)).unwrap(), types::F32);
        assert_eq!(clif_type(&Type::FloatN(FloatWidth::F64)).unwrap(), types::F64);
    }

    fn sample_stats_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "stats_only".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Int],
                    ret: Type::Unit,
                    effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Retain {
                            value: MirValueId(0),
                        },
                        MirInst::Release {
                            value: MirValueId(0),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "IO".to_string(),
                            operation: "stdout".to_string(),
                            args: vec![MirValueId(0)],
                            result: None,
                        },
                    ],
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_stdout_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "print_hello".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Unit,
                    effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::String("hello".to_string()),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "IO".to_string(),
                            operation: "stdout".to_string(),
                            args: vec![MirValueId(0)],
                            result: None,
                        },
                    ],
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_stderr_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "print_err".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Unit,
                    effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::String("oops".to_string()),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "IO".to_string(),
                            operation: "stderr".to_string(),
                            args: vec![MirValueId(0)],
                            result: None,
                        },
                    ],
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_io_read_file_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "read_file".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::String,
                    effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::String("config".to_string()),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "IO".to_string(),
                            operation: "read_file".to_string(),
                            args: vec![MirValueId(0)],
                            result: Some(MirValueId(1)),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_io_write_file_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "write_file".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Unit,
                    effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::String("config".to_string()),
                        },
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::String("hello".to_string()),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "IO".to_string(),
                            operation: "write_file".to_string(),
                            args: vec![MirValueId(0), MirValueId(1)],
                            result: None,
                        },
                    ],
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_stdout_concat_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "print_joined".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Unit,
                    effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::String("hello ".to_string()),
                        },
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::String("world".to_string()),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Concat,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "IO".to_string(),
                            operation: "stdout".to_string(),
                            args: vec![MirValueId(2)],
                            result: None,
                        },
                    ],
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_clock_now_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "clock_now".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::closed(vec![(Label::new("Clock"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect: "Clock".to_string(),
                        operation: "now".to_string(),
                        args: vec![],
                        result: Some(MirValueId(0)),
                    }],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(0)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_clock_monotonic_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "clock_monotonic".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::closed(vec![(Label::new("Clock"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect: "Clock".to_string(),
                        operation: "monotonic".to_string(),
                        args: vec![],
                        result: Some(MirValueId(0)),
                    }],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(0)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_rand_int_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "rand_int".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::closed(vec![(Label::new("Rand"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect: "Rand".to_string(),
                        operation: "int".to_string(),
                        args: vec![],
                        result: Some(MirValueId(0)),
                    }],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(0)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_rand_seed_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "seed_rand".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Unit,
                    effects: EffectRow::closed(vec![(Label::new("Rand"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(123),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "Rand".to_string(),
                            operation: "seed".to_string(),
                            args: vec![MirValueId(0)],
                            result: None,
                        },
                    ],
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_net_connect_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "net_connect".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::closed(vec![(Label::new("Net"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::String("127.0.0.1:0".to_string()),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "Net".to_string(),
                            operation: "connect".to_string(),
                            args: vec![MirValueId(0)],
                            result: Some(MirValueId(1)),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_net_send_recv_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "net_send_recv".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::closed(vec![(Label::new("Net"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::String("ping".to_string()),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "Net".to_string(),
                            operation: "send".to_string(),
                            args: vec![MirValueId(0), MirValueId(1)],
                            result: None,
                        },
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(4),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "Net".to_string(),
                            operation: "recv".to_string(),
                            args: vec![MirValueId(0), MirValueId(2)],
                            result: Some(MirValueId(3)),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(3)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_codegen_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "add".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(40),
                        },
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(2),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Add,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(2)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_cfg_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "branchy".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![
                    MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Bool(true),
                        }],
                        terminator: MirTerminator::Branch {
                            condition: MirValueId(0),
                            then_block: MirBlockId(1),
                            else_block: MirBlockId(2),
                        },
                    },
                    MirBlock {
                        id: MirBlockId(1),
                        params: vec![],
                        instructions: vec![MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(1),
                        }],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(1)),
                        },
                    },
                    MirBlock {
                        id: MirBlockId(2),
                        params: vec![],
                        instructions: vec![MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(0),
                        }],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(2)),
                        },
                    },
                ],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_string_literal_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "string_literal".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::String,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::String("hello".to_string()),
                    }],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(0)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_release_string_main_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "main".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::String("drop me".to_string()),
                        },
                        MirInst::Release {
                            value: MirValueId(0),
                        },
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(0),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_tail_recursive_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "countdown".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Int],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::Call {
                        callee: MirCallee::Local("countdown".to_string()),
                        args: vec![MirValueId(0)],
                        arg_types: vec![Type::Int],
                        result: Some(MirValueId(1)),
                        ret_type: Type::Int,
                        callee_fail_result_abi: false,
                        capture_fail_result: false,
                        cc_manifest_id: "default".to_string(),
                    }],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_tail_recursive_with_release_prefix_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "drop_and_recurse".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Int],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Release {
                            value: MirValueId(0),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("drop_and_recurse".to_string()),
                            args: vec![MirValueId(0)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(1)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_trmc_candidate_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "build".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Int],
                    ret: Type::Dynamic,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(0)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(2)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(3),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(1), MirValueId(2)],
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(3)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_tail_recursive_through_join_return_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "count".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Int, Type::Int],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![
                    MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![],
                        terminator: MirTerminator::Branch {
                            condition: MirValueId(0),
                            then_block: MirBlockId(1),
                            else_block: MirBlockId(2),
                        },
                    },
                    MirBlock {
                        id: MirBlockId(1),
                        params: vec![],
                        instructions: vec![],
                        terminator: MirTerminator::Jump {
                            target: MirBlockId(3),
                            args: vec![MirValueId(1)],
                        },
                    },
                    MirBlock {
                        id: MirBlockId(2),
                        params: vec![],
                        instructions: vec![MirInst::Call {
                            callee: MirCallee::Local("count".to_string()),
                            args: vec![MirValueId(0), MirValueId(1)],
                            arg_types: vec![Type::Int, Type::Int],
                            result: Some(MirValueId(2)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        }],
                        terminator: MirTerminator::Jump {
                            target: MirBlockId(3),
                            args: vec![MirValueId(2)],
                        },
                    },
                    MirBlock {
                        id: MirBlockId(3),
                        params: vec![MirBlockParam {
                            id: MirValueId(3),
                            ty: Type::Int,
                        }],
                        instructions: vec![MirInst::Nop],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(3)),
                        },
                    },
                ],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_handler_cell_tail_recursive_through_join_return_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "count".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Int, Type::Dynamic],
                    ret: Type::Int,
                    effects: EffectRow::closed(vec![(Label::new("State"), Type::Int)]),
                },
                entry: MirBlockId(0),
                blocks: vec![
                    MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![],
                        terminator: MirTerminator::Branch {
                            condition: MirValueId(0),
                            then_block: MirBlockId(1),
                            else_block: MirBlockId(2),
                        },
                    },
                    MirBlock {
                        id: MirBlockId(1),
                        params: vec![],
                        instructions: vec![],
                        terminator: MirTerminator::Jump {
                            target: MirBlockId(3),
                            args: vec![MirValueId(0)],
                        },
                    },
                    MirBlock {
                        id: MirBlockId(2),
                        params: vec![],
                        instructions: vec![MirInst::Call {
                            callee: MirCallee::Local("count".to_string()),
                            args: vec![MirValueId(0), MirValueId(1)],
                            arg_types: vec![Type::Int, Type::Dynamic],
                            result: Some(MirValueId(2)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        }],
                        terminator: MirTerminator::Jump {
                            target: MirBlockId(3),
                            args: vec![MirValueId(2)],
                        },
                    },
                    MirBlock {
                        id: MirBlockId(3),
                        params: vec![MirBlockParam {
                            id: MirValueId(3),
                            ty: Type::Int,
                        }],
                        instructions: vec![MirInst::Nop],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(3)),
                        },
                    },
                ],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_handler_cell_tail_recursive_with_rewritten_cell_arg_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "count".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Int, Type::Dynamic],
                    ret: Type::Int,
                    effects: EffectRow::closed(vec![(Label::new("State"), Type::Int)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("count".to_string()),
                            args: vec![MirValueId(0), MirValueId(2)],
                            arg_types: vec![Type::Int, Type::Dynamic],
                            result: Some(MirValueId(3)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(3)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_external_call_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "call_ext".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(7),
                        },
                        MirInst::Call {
                            callee: MirCallee::External("List.len".to_string()),
                            args: vec![MirValueId(0)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(1)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_external_conflicting_signature_module() -> MirModule {
        MirModule {
            functions: vec![
                MirFunction {
                    name: "call_ext_int".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![],
                        ret: Type::Int,
                        effects: EffectRow::pure(),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![
                            MirInst::Const {
                                dest: MirValueId(0),
                                literal: MirLiteral::Int(7),
                            },
                            MirInst::Call {
                                callee: MirCallee::External("List.len".to_string()),
                                args: vec![MirValueId(0)],
                                arg_types: vec![Type::Int],
                                result: Some(MirValueId(1)),
                                ret_type: Type::Int,
                                callee_fail_result_abi: false,
                                capture_fail_result: false,
                                cc_manifest_id: "default".to_string(),
                            },
                        ],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(1)),
                        },
                    }],
                },
                MirFunction {
                    name: "call_ext_float".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![],
                        ret: Type::Int,
                        effects: EffectRow::pure(),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![
                            MirInst::Const {
                                dest: MirValueId(0),
                                literal: MirLiteral::Float(7.0),
                            },
                            MirInst::Call {
                                callee: MirCallee::External("List.len".to_string()),
                                args: vec![MirValueId(0)],
                                arg_types: vec![Type::Float],
                                result: Some(MirValueId(1)),
                                ret_type: Type::Int,
                                callee_fail_result_abi: false,
                                capture_fail_result: false,
                                cc_manifest_id: "default".to_string(),
                            },
                        ],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(1)),
                        },
                    }],
                },
            ],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_record_field_load_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "get_age".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Record(RecordType {
                        name: "User".to_string(),
                        params: vec![],
                        row: RowType::closed(vec![
                            (Label::new("age"), Type::Int),
                            (Label::new("name"), Type::String),
                        ]),
                    })],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::RecordFieldLoad {
                        dest: MirValueId(1),
                        record: MirValueId(0),
                        record_type: "User".to_string(),
                        field: "age".to_string(),
                        field_ty: Type::Int,
                    }],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog {
                records: vec![MirRecordLayout {
                    name: "User".to_string(),
                    fields: vec![
                        MirRecordFieldLayout {
                            name: "name".to_string(),
                            annotation: kea_ast::TypeAnnotation::Named("String".to_string()),
                        },
                        MirRecordFieldLayout {
                            name: "age".to_string(),
                            annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                        },
                    ],
                }],
                sums: vec![],
            },
        }
    }

    fn sample_record_init_and_load_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "make_and_get_age".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(42),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(1),
                            record_type: "User".to_string(),
                            fields: vec![("age".to_string(), MirValueId(0))],
                        },
                        MirInst::RecordFieldLoad {
                            dest: MirValueId(2),
                            record: MirValueId(1),
                            record_type: "User".to_string(),
                            field: "age".to_string(),
                            field_ty: Type::Int,
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(2)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog {
                records: vec![MirRecordLayout {
                    name: "User".to_string(),
                    fields: vec![MirRecordFieldLayout {
                        name: "age".to_string(),
                        annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                    }],
                }],
                sums: vec![],
            },
        }
    }

    fn sample_record_init_reuse_and_load_main_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "main".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(42),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(1),
                            record_type: "User".to_string(),
                            fields: vec![("age".to_string(), MirValueId(0))],
                        },
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(7),
                        },
                        MirInst::RecordInitReuse {
                            dest: MirValueId(3),
                            source: MirValueId(1),
                            record_type: "User".to_string(),
                            fields: vec![("age".to_string(), MirValueId(2))],
                        },
                        MirInst::RecordFieldLoad {
                            dest: MirValueId(4),
                            record: MirValueId(3),
                            record_type: "User".to_string(),
                            field: "age".to_string(),
                            field_ty: Type::Int,
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(4)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog {
                records: vec![MirRecordLayout {
                    name: "User".to_string(),
                    fields: vec![MirRecordFieldLayout {
                        name: "age".to_string(),
                        annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                    }],
                }],
                sums: vec![],
            },
        }
    }

    fn sample_record_init_from_token_and_load_main_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "main".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(42),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(1),
                            record_type: "User".to_string(),
                            fields: vec![("age".to_string(), MirValueId(0))],
                        },
                        MirInst::ReuseToken {
                            dest: MirValueId(2),
                            source: MirValueId(1),
                        },
                        MirInst::Const {
                            dest: MirValueId(3),
                            literal: MirLiteral::Int(7),
                        },
                        MirInst::RecordInitFromToken {
                            dest: MirValueId(4),
                            token: MirValueId(2),
                            record_type: "User".to_string(),
                            fields: vec![("age".to_string(), MirValueId(3))],
                        },
                        MirInst::RecordFieldLoad {
                            dest: MirValueId(5),
                            record: MirValueId(4),
                            record_type: "User".to_string(),
                            field: "age".to_string(),
                            field_ty: Type::Int,
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(5)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog {
                records: vec![MirRecordLayout {
                    name: "User".to_string(),
                    fields: vec![MirRecordFieldLayout {
                        name: "age".to_string(),
                        annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                    }],
                }],
                sums: vec![],
            },
        }
    }

    fn sample_reuse_token_candidate_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "main".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![
                    MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![
                            MirInst::Const {
                                dest: MirValueId(0),
                                literal: MirLiteral::Int(1),
                            },
                            MirInst::RecordInit {
                                dest: MirValueId(1),
                                record_type: "User".to_string(),
                                fields: vec![("age".to_string(), MirValueId(0))],
                            },
                            MirInst::Release {
                                value: MirValueId(1),
                            },
                        ],
                        terminator: MirTerminator::Jump {
                            target: MirBlockId(1),
                            args: vec![MirValueId(1)],
                        },
                    },
                    MirBlock {
                        id: MirBlockId(1),
                        params: vec![MirBlockParam {
                            id: MirValueId(10),
                            ty: Type::Record(RecordType {
                                name: "User".to_string(),
                                params: vec![],
                                row: RowType::closed(vec![(Label::new("age"), Type::Int)]),
                            }),
                        }],
                        instructions: vec![
                            MirInst::Const {
                                dest: MirValueId(2),
                                literal: MirLiteral::Int(7),
                            },
                            MirInst::RecordInit {
                                dest: MirValueId(3),
                                record_type: "User".to_string(),
                                fields: vec![("age".to_string(), MirValueId(2))],
                            },
                            MirInst::RecordFieldLoad {
                                dest: MirValueId(4),
                                record: MirValueId(3),
                                record_type: "User".to_string(),
                                field: "age".to_string(),
                                field_ty: Type::Int,
                            },
                        ],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(4)),
                        },
                    },
                ],
            }],
            layouts: MirLayoutCatalog {
                records: vec![MirRecordLayout {
                    name: "User".to_string(),
                    fields: vec![MirRecordFieldLayout {
                        name: "age".to_string(),
                        annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                    }],
                }],
                sums: vec![],
            },
        }
    }

    fn sample_sum_init_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "make_some".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Sum(SumType {
                        name: "Option".to_string(),
                        type_args: vec![Type::Int],
                        variants: vec![
                            ("Some".to_string(), vec![Type::Int]),
                            ("None".to_string(), vec![]),
                        ],
                    }),
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(7),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(1),
                            sum_type: "Option".to_string(),
                            variant: "Some".to_string(),
                            tag: 0,
                            fields: vec![MirValueId(0)],
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog {
                records: vec![],
                sums: vec![MirSumLayout {
                    name: "Option".to_string(),
                    variants: vec![
                        MirVariantLayout {
                            name: "Some".to_string(),
                            tag: 0,
                            fields: vec![MirVariantFieldLayout {
                                name: None,
                                annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                            }],
                        },
                        MirVariantLayout {
                            name: "None".to_string(),
                            tag: 1,
                            fields: vec![],
                        },
                    ],
                }],
            },
        }
    }

    fn sample_sum_init_reuse_and_tag_load_main_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "main".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(7),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(1),
                            sum_type: "Pairish".to_string(),
                            variant: "Left".to_string(),
                            tag: 0,
                            fields: vec![MirValueId(0)],
                        },
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(9),
                        },
                        MirInst::SumInitReuse {
                            dest: MirValueId(3),
                            source: MirValueId(1),
                            sum_type: "Pairish".to_string(),
                            variant: "Right".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(2)],
                        },
                        MirInst::SumTagLoad {
                            dest: MirValueId(4),
                            sum: MirValueId(3),
                            sum_type: "Pairish".to_string(),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(4)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog {
                records: vec![],
                sums: vec![MirSumLayout {
                    name: "Pairish".to_string(),
                    variants: vec![
                        MirVariantLayout {
                            name: "Left".to_string(),
                            tag: 0,
                            fields: vec![MirVariantFieldLayout {
                                name: None,
                                annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                            }],
                        },
                        MirVariantLayout {
                            name: "Right".to_string(),
                            tag: 1,
                            fields: vec![MirVariantFieldLayout {
                                name: None,
                                annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                            }],
                        },
                    ],
                }],
            },
        }
    }

    fn sample_sum_tag_load_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "is_some".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Sum(SumType {
                        name: "Option".to_string(),
                        type_args: vec![Type::Int],
                        variants: vec![
                            ("Some".to_string(), vec![Type::Int]),
                            ("None".to_string(), vec![]),
                        ],
                    })],
                    ret: Type::Bool,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::SumTagLoad {
                            dest: MirValueId(1),
                            sum: MirValueId(0),
                            sum_type: "Option".to_string(),
                        },
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(3),
                            op: MirBinaryOp::Eq,
                            left: MirValueId(1),
                            right: MirValueId(2),
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(3)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog {
                records: vec![],
                sums: vec![MirSumLayout {
                    name: "Option".to_string(),
                    variants: vec![
                        MirVariantLayout {
                            name: "Some".to_string(),
                            tag: 0,
                            fields: vec![MirVariantFieldLayout {
                                name: None,
                                annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                            }],
                        },
                        MirVariantLayout {
                            name: "None".to_string(),
                            tag: 1,
                            fields: vec![],
                        },
                    ],
                }],
            },
        }
    }

    fn sample_sum_payload_load_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "unwrap_some".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Sum(SumType {
                        name: "Option".to_string(),
                        type_args: vec![Type::Int],
                        variants: vec![
                            ("Some".to_string(), vec![Type::Int]),
                            ("None".to_string(), vec![]),
                        ],
                    })],
                    ret: Type::Int,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::SumPayloadLoad {
                        dest: MirValueId(1),
                        sum: MirValueId(0),
                        sum_type: "Option".to_string(),
                        variant: "Some".to_string(),
                        field_index: 0,
                        field_ty: Type::Int,
                    }],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog {
                records: vec![],
                sums: vec![MirSumLayout {
                    name: "Option".to_string(),
                    variants: vec![
                        MirVariantLayout {
                            name: "Some".to_string(),
                            tag: 0,
                            fields: vec![MirVariantFieldLayout {
                                name: None,
                                annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                            }],
                        },
                        MirVariantLayout {
                            name: "None".to_string(),
                            tag: 1,
                            fields: vec![],
                        },
                    ],
                }],
            },
        }
    }

    fn sample_record_handle_signature_module() -> MirModule {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
            row: RowType::closed(vec![
                (Label::new("name"), Type::String),
                (Label::new("age"), Type::Int),
            ]),
        });
        MirModule {
            functions: vec![MirFunction {
                name: "id_user".to_string(),
                signature: MirFunctionSignature {
                    params: vec![user_ty.clone()],
                    ret: user_ty,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(0)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_sum_handle_signature_module() -> MirModule {
        let option_ty = Type::Sum(SumType {
            name: "Option".to_string(),
            type_args: vec![Type::Int],
            variants: vec![
                ("Some".to_string(), vec![Type::Int]),
                ("None".to_string(), vec![]),
            ],
        });
        MirModule {
            functions: vec![MirFunction {
                name: "id_option".to_string(),
                signature: MirFunctionSignature {
                    params: vec![option_ty.clone()],
                    ret: option_ty,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(0)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_fail_only_module_with_inst(inst: MirInst) -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "fail_only".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Unit,
                    effects: EffectRow::closed(vec![(Label::new("Fail"), Type::String)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![inst],
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_handler_marker_module(instructions: Vec<MirInst>) -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "handler_markers".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Unit,
                    effects: EffectRow::closed(vec![(Label::new("State"), Type::Int)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions,
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_fail_only_result_module_with_insts(instructions: Vec<MirInst>) -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "fail_only".to_string(),
                signature: MirFunctionSignature {
                    params: vec![],
                    ret: Type::Result(Box::new(Type::Int), Box::new(Type::Int)),
                    effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions,
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_fail_only_call_propagation_err_module() -> MirModule {
        MirModule {
            functions: vec![
                MirFunction {
                    name: "leaf".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![],
                        ret: Type::Int,
                        effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![
                            MirInst::Const {
                                dest: MirValueId(0),
                                literal: MirLiteral::Int(42),
                            },
                            MirInst::EffectOp {
                                class: MirEffectOpClass::ZeroResume,
                                effect: "Fail".to_string(),
                                operation: "fail".to_string(),
                                args: vec![MirValueId(0)],
                                result: None,
                            },
                        ],
                        terminator: MirTerminator::Unreachable,
                    }],
                },
                MirFunction {
                    name: "caller".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![],
                        ret: Type::Int,
                        effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![MirInst::Call {
                            callee: MirCallee::Local("leaf".to_string()),
                            args: vec![],
                            arg_types: vec![],
                            result: Some(MirValueId(0)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        }],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(0)),
                        },
                    }],
                },
            ],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_fail_only_call_propagation_ok_module() -> MirModule {
        MirModule {
            functions: vec![
                MirFunction {
                    name: "leaf".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![],
                        ret: Type::Int,
                        effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![MirInst::Const {
                            dest: MirValueId(0),
                            literal: MirLiteral::Int(7),
                        }],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(0)),
                        },
                    }],
                },
                MirFunction {
                    name: "caller".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![],
                        ret: Type::Int,
                        effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![
                            MirInst::Call {
                                callee: MirCallee::Local("leaf".to_string()),
                                args: vec![],
                                arg_types: vec![],
                                result: Some(MirValueId(0)),
                                ret_type: Type::Int,
                                callee_fail_result_abi: false,
                                capture_fail_result: false,
                                cc_manifest_id: "default".to_string(),
                            },
                            MirInst::Const {
                                dest: MirValueId(1),
                                literal: MirLiteral::Int(1),
                            },
                            MirInst::Binary {
                                dest: MirValueId(2),
                                op: MirBinaryOp::Add,
                                left: MirValueId(0),
                                right: MirValueId(1),
                            },
                        ],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(2)),
                        },
                    }],
                },
            ],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_indirect_function_call_module() -> MirModule {
        let unary_fn_ty = Type::Function(FunctionType::pure(vec![Type::Int], Type::Int));
        MirModule {
            functions: vec![
                MirFunction {
                    name: "inc".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![Type::Int],
                        ret: Type::Int,
                        effects: EffectRow::pure(),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![
                            MirInst::Const {
                                dest: MirValueId(1),
                                literal: MirLiteral::Int(1),
                            },
                            MirInst::Binary {
                                dest: MirValueId(2),
                                op: MirBinaryOp::Add,
                                left: MirValueId(0),
                                right: MirValueId(1),
                            },
                        ],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(2)),
                        },
                    }],
                },
                MirFunction {
                    name: "inc_entry".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![Type::Dynamic, Type::Int],
                        ret: Type::Int,
                        effects: EffectRow::pure(),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![MirInst::Call {
                            callee: MirCallee::Local("inc".to_string()),
                            args: vec![MirValueId(1)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(2)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        }],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(2)),
                        },
                    }],
                },
                MirFunction {
                    name: "apply_twice".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![unary_fn_ty.clone(), Type::Int],
                        ret: Type::Int,
                        effects: EffectRow::pure(),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![
                            MirInst::Call {
                                callee: MirCallee::Value(MirValueId(0)),
                                args: vec![MirValueId(1)],
                                arg_types: vec![Type::Int],
                                result: Some(MirValueId(2)),
                                ret_type: Type::Int,
                                callee_fail_result_abi: false,
                                capture_fail_result: false,
                                cc_manifest_id: "default".to_string(),
                            },
                            MirInst::Call {
                                callee: MirCallee::Value(MirValueId(0)),
                                args: vec![MirValueId(2)],
                                arg_types: vec![Type::Int],
                                result: Some(MirValueId(3)),
                                ret_type: Type::Int,
                                callee_fail_result_abi: false,
                                capture_fail_result: false,
                                cc_manifest_id: "default".to_string(),
                            },
                        ],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(3)),
                        },
                    }],
                },
                MirFunction {
                    name: "run".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![Type::Int],
                        ret: Type::Int,
                        effects: EffectRow::pure(),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![
                            MirInst::FunctionRef {
                                dest: MirValueId(1),
                                function: "inc_entry".to_string(),
                            },
                            MirInst::ClosureInit {
                                dest: MirValueId(2),
                                entry: MirValueId(1),
                                captures: vec![],
                                capture_types: vec![],
                            },
                            MirInst::Call {
                                callee: MirCallee::Local("apply_twice".to_string()),
                                args: vec![MirValueId(2), MirValueId(0)],
                                arg_types: vec![unary_fn_ty, Type::Int],
                                result: Some(MirValueId(3)),
                                ret_type: Type::Int,
                                callee_fail_result_abi: false,
                                capture_fail_result: false,
                                cc_manifest_id: "default".to_string(),
                            },
                        ],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(3)),
                        },
                    }],
                },
            ],
            layouts: MirLayoutCatalog::default(),
        }
    }

    fn sample_fail_indirect_function_call_module() -> MirModule {
        let fail_fn_ty = Type::Function(FunctionType::with_effects(
            vec![Type::Int],
            Type::Int,
            EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
        ));
        MirModule {
            functions: vec![
                MirFunction {
                    name: "failer".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![Type::Int],
                        ret: Type::Int,
                        effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![MirInst::EffectOp {
                            class: MirEffectOpClass::ZeroResume,
                            effect: "Fail".to_string(),
                            operation: "fail".to_string(),
                            args: vec![MirValueId(0)],
                            result: None,
                        }],
                        terminator: MirTerminator::Unreachable,
                    }],
                },
                MirFunction {
                    name: "failer_entry".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![Type::Dynamic, Type::Int],
                        ret: Type::Int,
                        effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![MirInst::Call {
                            callee: MirCallee::Local("failer".to_string()),
                            args: vec![MirValueId(1)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(2)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: true,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        }],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(2)),
                        },
                    }],
                },
                MirFunction {
                    name: "apply_once".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![fail_fn_ty.clone(), Type::Int],
                        ret: Type::Int,
                        effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![MirInst::Call {
                            callee: MirCallee::Value(MirValueId(0)),
                            args: vec![MirValueId(1)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(2)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: true,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        }],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(2)),
                        },
                    }],
                },
                MirFunction {
                    name: "driver".to_string(),
                    signature: MirFunctionSignature {
                        params: vec![Type::Int],
                        ret: Type::Int,
                        effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                    },
                    entry: MirBlockId(0),
                    blocks: vec![MirBlock {
                        id: MirBlockId(0),
                        params: vec![],
                        instructions: vec![
                            MirInst::FunctionRef {
                                dest: MirValueId(1),
                                function: "failer_entry".to_string(),
                            },
                            MirInst::ClosureInit {
                                dest: MirValueId(2),
                                entry: MirValueId(1),
                                captures: vec![],
                                capture_types: vec![],
                            },
                            MirInst::Call {
                                callee: MirCallee::Local("apply_once".to_string()),
                                args: vec![MirValueId(2), MirValueId(0)],
                                arg_types: vec![fail_fn_ty, Type::Int],
                                result: Some(MirValueId(3)),
                                ret_type: Type::Int,
                                callee_fail_result_abi: false,
                                capture_fail_result: false,
                                cc_manifest_id: "default".to_string(),
                            },
                        ],
                        terminator: MirTerminator::Return {
                            value: Some(MirValueId(3)),
                        },
                    }],
                },
            ],
            layouts: MirLayoutCatalog::default(),
        }
    }

    #[test]
    fn validate_abi_manifest_reports_missing_function() {
        let module = sample_stats_module();
        let empty_manifest = AbiManifest {
            functions: BTreeMap::new(),
        };

        let err = validate_abi_manifest(&module, &empty_manifest).expect_err("should fail");
        assert!(matches!(err, CodegenError::MissingAbiEntry { .. }));
    }

    #[test]
    fn validate_layout_catalog_rejects_duplicate_record_field() {
        let mut module = sample_codegen_module();
        module.layouts.records.push(MirRecordLayout {
            name: "User".to_string(),
            fields: vec![
                MirRecordFieldLayout {
                    name: "name".to_string(),
                    annotation: kea_ast::TypeAnnotation::Named("String".to_string()),
                },
                MirRecordFieldLayout {
                    name: "name".to_string(),
                    annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                },
            ],
        });

        let err = validate_layout_catalog(&module).expect_err("should reject duplicate field");
        assert!(matches!(
            err,
            CodegenError::DuplicateLayoutField {
                type_name,
                field
            } if type_name == "User" && field == "name"
        ));
    }

    #[test]
    fn validate_layout_catalog_rejects_non_contiguous_sum_tags() {
        let mut module = sample_codegen_module();
        module.layouts.sums.push(MirSumLayout {
            name: "Option".to_string(),
            variants: vec![
                MirVariantLayout {
                    name: "Some".to_string(),
                    tag: 0,
                    fields: vec![MirVariantFieldLayout {
                        name: None,
                        annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                    }],
                },
                MirVariantLayout {
                    name: "None".to_string(),
                    tag: 2,
                    fields: vec![],
                },
            ],
        });

        let err = validate_layout_catalog(&module).expect_err("should reject non-contiguous tags");
        assert!(matches!(
            err,
            CodegenError::InvalidLayoutVariantTags { type_name } if type_name == "Option"
        ));
    }

    #[test]
    fn plan_layout_catalog_computes_record_offsets_in_declaration_order() {
        let mut module = sample_codegen_module();
        module.layouts.records.push(MirRecordLayout {
            name: "User".to_string(),
            fields: vec![
                MirRecordFieldLayout {
                    name: "name".to_string(),
                    annotation: kea_ast::TypeAnnotation::Named("String".to_string()),
                },
                MirRecordFieldLayout {
                    name: "age".to_string(),
                    annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                },
                MirRecordFieldLayout {
                    name: "active".to_string(),
                    annotation: kea_ast::TypeAnnotation::Named("Bool".to_string()),
                },
            ],
        });

        let plan = plan_layout_catalog(&module).expect("layout planning should succeed");
        let user = plan.records.get("User").expect("User record layout");
        assert_eq!(user.align_bytes, 8);
        assert_eq!(user.size_bytes, 24);
        assert_eq!(user.field_offsets.get("name"), Some(&0));
        assert_eq!(user.field_offsets.get("age"), Some(&8));
        assert_eq!(user.field_offsets.get("active"), Some(&16));
        assert_eq!(user.field_types.get("name"), Some(&Type::String));
        assert_eq!(user.field_types.get("age"), Some(&Type::Int));
        assert_eq!(user.field_types.get("active"), Some(&Type::Bool));
    }

    #[test]
    fn plan_layout_catalog_computes_sum_tag_and_payload_layout() {
        let mut module = sample_codegen_module();
        module.layouts.sums.push(MirSumLayout {
            name: "Result".to_string(),
            variants: vec![
                MirVariantLayout {
                    name: "Ok".to_string(),
                    tag: 0,
                    fields: vec![MirVariantFieldLayout {
                        name: None,
                        annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                    }],
                },
                MirVariantLayout {
                    name: "Err".to_string(),
                    tag: 1,
                    fields: vec![
                        MirVariantFieldLayout {
                            name: None,
                            annotation: kea_ast::TypeAnnotation::Named("Int".to_string()),
                        },
                        MirVariantFieldLayout {
                            name: None,
                            annotation: kea_ast::TypeAnnotation::Named("String".to_string()),
                        },
                    ],
                },
            ],
        });

        let plan = plan_layout_catalog(&module).expect("layout planning should succeed");
        let result = plan.sums.get("Result").expect("Result sum layout");
        assert_eq!(result.align_bytes, 8);
        assert_eq!(result.tag_offset, 0);
        assert_eq!(result.payload_offset, 8);
        assert_eq!(result.max_payload_fields, 2);
        assert_eq!(result.size_bytes, 24);
        assert_eq!(result.variant_tags.get("Ok"), Some(&0));
        assert_eq!(result.variant_tags.get("Err"), Some(&1));
        assert_eq!(result.variant_field_counts.get("Ok"), Some(&1));
        assert_eq!(result.variant_field_counts.get("Err"), Some(&2));
        assert_eq!(
            result.variant_field_types.get("Ok"),
            Some(&vec![Type::Int])
        );
        assert_eq!(
            result.variant_field_types.get("Err"),
            Some(&vec![Type::Int, Type::String])
        );
    }

    #[test]
    fn infer_mir_value_types_resolves_dynamic_sum_payload_from_layout() {
        let module = MirModule {
            functions: vec![MirFunction {
                name: "payload".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::Sum(SumType {
                        name: "MaybeText".to_string(),
                        type_args: vec![],
                        variants: vec![
                            ("Some".to_string(), vec![Type::String]),
                            ("None".to_string(), vec![]),
                        ],
                    })],
                    ret: Type::String,
                    effects: EffectRow::pure(),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::SumPayloadLoad {
                        dest: MirValueId(1),
                        sum: MirValueId(0),
                        sum_type: "MaybeText".to_string(),
                        variant: "Some".to_string(),
                        field_index: 0,
                        field_ty: Type::Dynamic,
                    }],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(1)),
                    },
                }],
            }],
            layouts: MirLayoutCatalog {
                records: vec![],
                sums: vec![MirSumLayout {
                    name: "MaybeText".to_string(),
                    variants: vec![
                        MirVariantLayout {
                            name: "Some".to_string(),
                            tag: 0,
                            fields: vec![MirVariantFieldLayout {
                                name: None,
                                annotation: kea_ast::TypeAnnotation::Named("String".to_string()),
                            }],
                        },
                        MirVariantLayout {
                            name: "None".to_string(),
                            tag: 1,
                            fields: vec![],
                        },
                    ],
                }],
            },
        };
        let plan = plan_layout_catalog(&module).expect("layout planning should succeed");
        let function = &module.functions[0];
        let value_types = infer_mir_value_types(function, &plan);

        assert_eq!(
            value_types.get(&MirValueId(0)),
            Some(&Type::Sum(SumType {
                name: "MaybeText".to_string(),
                type_args: vec![],
                variants: vec![
                    ("Some".to_string(), vec![Type::String]),
                    ("None".to_string(), vec![]),
                ],
            }))
        );
        assert_eq!(value_types.get(&MirValueId(1)), Some(&Type::String));
    }

    #[test]
    fn validate_fail_only_invariants_rejects_non_zero_resume_fail_op() {
        let module = sample_fail_only_module_with_inst(MirInst::EffectOp {
            class: MirEffectOpClass::Dispatch,
            effect: "Fail".to_string(),
            operation: "fail".to_string(),
            args: vec![MirValueId(0)],
            result: Some(MirValueId(1)),
        });

        let err = validate_fail_only_invariants(&module)
            .expect_err("should reject dispatch in Fail-only");
        assert!(matches!(
            err,
            CodegenError::FailOnlyInvariantViolation { function, .. } if function == "fail_only"
        ));
    }

    #[test]
    fn validate_fail_only_invariants_rejects_handler_ops() {
        let module = sample_fail_only_module_with_inst(MirInst::HandlerEnter {
            effect: "Fail".to_string(),
        });

        let err = validate_fail_only_invariants(&module)
            .expect_err("should reject handler ops in Fail-only");
        assert!(matches!(
            err,
            CodegenError::FailOnlyInvariantViolation { function, .. } if function == "fail_only"
        ));
    }

    #[test]
    fn validate_fail_only_invariants_accepts_zero_resume_fail_op() {
        let module = sample_fail_only_module_with_inst(MirInst::EffectOp {
            class: MirEffectOpClass::ZeroResume,
            effect: "Fail".to_string(),
            operation: "fail".to_string(),
            args: vec![],
            result: None,
        });

        validate_fail_only_invariants(&module)
            .expect("ZeroResume Fail operation should satisfy Fail-only invariant");
    }

    #[test]
    fn validate_fail_only_invariants_rejects_zero_resume_fail_result_value() {
        let module = sample_fail_only_module_with_inst(MirInst::EffectOp {
            class: MirEffectOpClass::ZeroResume,
            effect: "Fail".to_string(),
            operation: "fail".to_string(),
            args: vec![],
            result: Some(MirValueId(0)),
        });

        let err = validate_fail_only_invariants(&module)
            .expect_err("zero-resume Fail with result value should be rejected");
        assert!(matches!(
            err,
            CodegenError::FailOnlyInvariantViolation { function, .. } if function == "fail_only"
        ));
    }

    #[test]
    fn cranelift_backend_allows_handler_scope_markers_as_noop() {
        let module = sample_handler_marker_module(vec![
            MirInst::HandlerEnter {
                effect: "State".to_string(),
            },
            MirInst::HandlerExit {
                effect: "State".to_string(),
            },
        ]);
        let abi = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        backend
            .compile_module(
                &module,
                &abi,
                &BackendConfig {
                    mode: CodegenMode::Jit,
                    ..BackendConfig::default()
                },
            )
            .expect("handler scope markers should lower as no-op");
    }

    #[test]
    fn cranelift_backend_reports_non_tail_resume_not_supported() {
        let module = sample_handler_marker_module(vec![
            MirInst::HandlerEnter {
                effect: "State".to_string(),
            },
            MirInst::Resume {
                value: MirValueId(0),
            },
            MirInst::HandlerExit {
                effect: "State".to_string(),
            },
        ]);
        let abi = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        let err = backend
            .compile_module(
                &module,
                &abi,
                &BackendConfig {
                    mode: CodegenMode::Jit,
                    ..BackendConfig::default()
                },
            )
            .expect_err("resume should report compiler bug");
        assert!(matches!(
            err,
            CodegenError::UnsupportedMir { function, ref detail }
                if function == "handler_markers"
                    && detail.contains("Resume instruction reached codegen")
        ));
    }

    #[test]
    fn default_abi_manifest_marks_effect_evidence_for_effectful_functions() {
        let module = sample_stats_module();
        let manifest = default_abi_manifest(&module);

        let sig = manifest.get("stats_only").expect("stats_only signature");
        assert_eq!(
            sig.effect_evidence,
            AbiEffectEvidencePlacement::TrailingParam
        );
    }

    #[test]
    fn collect_pass_stats_counts_effect_ops() {
        let module = sample_stats_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.retain_count, 1);
        assert_eq!(function.release_count, 1);
        assert_eq!(function.reuse_count, 0);
        assert_eq!(function.reuse_token_candidate_count, 0);
        assert_eq!(function.effect_op_direct_count, 1);
    }

    #[test]
    fn collect_pass_stats_counts_record_reuse_ops() {
        let module = sample_record_init_reuse_and_load_main_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.reuse_count, 1);
        assert_eq!(function.reuse_token_candidate_count, 0);
        assert_eq!(function.alloc_count, 2);
    }

    #[test]
    fn collect_pass_stats_counts_reuse_token_candidates() {
        let module = sample_reuse_token_candidate_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.reuse_count, 0);
        assert_eq!(function.reuse_token_candidate_count, 1);
    }

    #[test]
    fn collect_pass_stats_counts_reuse_token_flow_ops() {
        let module = sample_record_init_from_token_and_load_main_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.reuse_token_produced_count, 1);
        assert_eq!(function.reuse_token_consumed_count, 1);
        assert_eq!(function.reuse_token_candidate_count, 0);
    }

    #[test]
    fn collect_pass_stats_counts_tail_self_calls() {
        let module = sample_tail_recursive_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.tail_self_call_count, 1);
    }

    #[test]
    fn collect_pass_stats_counts_trmc_candidates() {
        let module = sample_trmc_candidate_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.trmc_candidate_count, 1);
    }

    #[test]
    fn collect_pass_stats_detects_tail_self_call_with_release_prefix() {
        let module = sample_tail_recursive_with_release_prefix_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.tail_self_call_count, 1);
    }

    #[test]
    fn collect_pass_stats_detects_tail_self_call_through_join_return() {
        let module = sample_tail_recursive_through_join_return_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.tail_self_call_count, 1);
    }

    #[test]
    fn collect_pass_stats_detects_handler_cell_tail_self_call_through_join_return() {
        let module = sample_handler_cell_tail_recursive_through_join_return_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.tail_self_call_count, 1);
    }

    #[test]
    fn collect_pass_stats_rejects_tail_self_call_when_handler_cell_arg_is_rewritten() {
        let module = sample_handler_cell_tail_recursive_with_rewritten_cell_arg_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.tail_self_call_count, 0);
    }

    #[test]
    fn cranelift_backend_compiles_jit_pure_module() {
        let module = sample_codegen_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("compilation should succeed");

        assert_eq!(artifact.stats.per_function.len(), 1);
        assert!(
            artifact.object.is_empty(),
            "JIT mode should not emit object bytes"
        );
    }

    #[test]
    fn cranelift_backend_compiles_string_literal_module() {
        let module = sample_string_literal_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("string literal lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    fn cranelift_backend_executes_release_of_heap_value() {
        let module = sample_release_string_main_module();
        let exit_code =
            execute_mir_main_jit(&module, &BackendConfig::default()).expect("main should execute");
        assert_eq!(exit_code, 0);
    }

    #[test]
    fn cranelift_backend_compiles_io_stdout_effect_op_module() {
        let module = sample_stdout_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("IO.stdout lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn cranelift_backend_compiles_io_stderr_effect_op_module() {
        let module = sample_stderr_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("IO.stderr lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn cranelift_backend_compiles_io_read_file_effect_op_module() {
        let module = sample_io_read_file_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("IO.read_file lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn cranelift_backend_compiles_io_write_file_effect_op_module() {
        let module = sample_io_write_file_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("IO.write_file lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn cranelift_backend_compiles_clock_now_effect_op_module() {
        let module = sample_clock_now_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("Clock.now lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn cranelift_backend_compiles_clock_monotonic_effect_op_module() {
        let module = sample_clock_monotonic_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("Clock.monotonic lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn cranelift_backend_compiles_rand_int_effect_op_module() {
        let module = sample_rand_int_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("Rand.int lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn cranelift_backend_compiles_rand_seed_effect_op_module() {
        let module = sample_rand_seed_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("Rand.seed lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn cranelift_backend_compiles_net_connect_effect_op_module() {
        let module = sample_net_connect_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("Net.connect lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    #[cfg(not(target_os = "windows"))]
    fn cranelift_backend_compiles_net_send_recv_effect_ops_module() {
        let module = sample_net_send_recv_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("Net.send/Net.recv lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    fn cranelift_backend_compiles_string_concat_stdout_module() {
        let module = sample_stdout_concat_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("string concat lowering should compile");

        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    fn cranelift_backend_accepts_zero_resume_fail_effect_op() {
        let module = sample_fail_only_result_module_with_insts(vec![
            MirInst::Const {
                dest: MirValueId(0),
                literal: MirLiteral::Int(7),
            },
            MirInst::EffectOp {
                class: MirEffectOpClass::ZeroResume,
                effect: "Fail".to_string(),
                operation: "fail".to_string(),
                args: vec![MirValueId(0)],
                result: None,
            },
        ]);
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("zero-resume Fail effect op should lower in 0d");
    }

    #[test]
    fn cranelift_backend_zero_resume_fail_returns_err_for_result_signature() {
        let module = sample_fail_only_result_module_with_insts(vec![
            MirInst::Const {
                dest: MirValueId(0),
                literal: MirLiteral::Int(42),
            },
            MirInst::EffectOp {
                class: MirEffectOpClass::ZeroResume,
                effect: "Fail".to_string(),
                operation: "fail".to_string(),
                args: vec![MirValueId(0)],
                result: None,
            },
        ]);
        let layout_plan = plan_layout_catalog(&module).expect("layout planning should succeed");
        let isa = build_isa(&BackendConfig::default()).expect("host ISA should build");
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let mut jit_module = JITModule::new(builder);
        let func_ids = compile_into_module(&mut jit_module, &module, &layout_plan)
            .expect("fail-only result module should compile");
        jit_module
            .finalize_definitions()
            .expect("finalize definitions should succeed");

        let fail_only_id = *func_ids.get("fail_only").expect("fail_only function id");
        let fail_only_ptr = jit_module.get_finalized_function(fail_only_id);
        let fail_only: unsafe extern "C" fn() -> usize =
            unsafe { std::mem::transmute(fail_only_ptr) };
        let result_ptr = unsafe { fail_only() };
        assert_ne!(result_ptr, 0, "Fail result pointer should not be null");
        let tag = unsafe { *(result_ptr as *const i32) };
        assert_eq!(tag, 1, "Fail lowering should return Err tag");
        let payload = unsafe { *((result_ptr as *const u8).add(8) as *const i64) };
        assert_eq!(payload, 42, "Fail payload should be preserved in Err");
    }

    #[test]
    fn cranelift_backend_fail_only_local_call_propagates_err_result() {
        let module = sample_fail_only_call_propagation_err_module();
        let layout_plan = plan_layout_catalog(&module).expect("layout planning should succeed");
        let isa = build_isa(&BackendConfig::default()).expect("host ISA should build");
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let mut jit_module = JITModule::new(builder);
        let func_ids = compile_into_module(&mut jit_module, &module, &layout_plan)
            .expect("fail-only call propagation module should compile");
        jit_module
            .finalize_definitions()
            .expect("finalize definitions should succeed");

        let caller_id = *func_ids.get("caller").expect("caller function id");
        let caller_ptr = jit_module.get_finalized_function(caller_id);
        let caller: unsafe extern "C" fn() -> usize = unsafe { std::mem::transmute(caller_ptr) };
        let result_ptr = unsafe { caller() };
        assert_ne!(result_ptr, 0, "caller result pointer should not be null");
        let tag = unsafe { *(result_ptr as *const i32) };
        assert_eq!(tag, 1, "Fail-only local call should propagate Err tag");
        let payload = unsafe { *((result_ptr as *const u8).add(8) as *const i64) };
        assert_eq!(
            payload, 42,
            "Fail-only local call should preserve Err payload"
        );
    }

    #[test]
    fn cranelift_backend_fail_only_local_call_unwraps_ok_payload() {
        let module = sample_fail_only_call_propagation_ok_module();
        let layout_plan = plan_layout_catalog(&module).expect("layout planning should succeed");
        let isa = build_isa(&BackendConfig::default()).expect("host ISA should build");
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let mut jit_module = JITModule::new(builder);
        let func_ids = compile_into_module(&mut jit_module, &module, &layout_plan)
            .expect("fail-only call propagation module should compile");
        jit_module
            .finalize_definitions()
            .expect("finalize definitions should succeed");

        let caller_id = *func_ids.get("caller").expect("caller function id");
        let caller_ptr = jit_module.get_finalized_function(caller_id);
        let caller: unsafe extern "C" fn() -> usize = unsafe { std::mem::transmute(caller_ptr) };
        let result_ptr = unsafe { caller() };
        assert_ne!(result_ptr, 0, "caller result pointer should not be null");
        let tag = unsafe { *(result_ptr as *const i32) };
        assert_eq!(tag, 0, "successful local call should return Ok tag");
        let payload = unsafe { *((result_ptr as *const u8).add(8) as *const i64) };
        assert_eq!(
            payload, 8,
            "caller should unwrap Ok payload, continue computation, and re-wrap"
        );
    }

    #[test]
    fn cranelift_backend_compiles_indirect_function_pointer_calls() {
        let module = sample_indirect_function_call_module();
        let layout_plan = plan_layout_catalog(&module).expect("layout planning should succeed");
        let isa = build_isa(&BackendConfig::default()).expect("host ISA should build");
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let mut jit_module = JITModule::new(builder);
        let func_ids = compile_into_module(&mut jit_module, &module, &layout_plan)
            .expect("indirect call module should compile");
        jit_module
            .finalize_definitions()
            .expect("finalize definitions should succeed");

        let run_id = *func_ids.get("run").expect("run function id");
        let run_ptr = jit_module.get_finalized_function(run_id);
        let run: unsafe extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(run_ptr) };
        let out = unsafe { run(41) };
        assert_eq!(out, 43, "run should apply inc twice via function pointer");
    }

    #[test]
    fn cranelift_backend_propagates_fail_through_indirect_function_pointer_call() {
        let module = sample_fail_indirect_function_call_module();
        let layout_plan = plan_layout_catalog(&module).expect("layout planning should succeed");
        let isa = build_isa(&BackendConfig::default()).expect("host ISA should build");
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let mut jit_module = JITModule::new(builder);
        let func_ids = compile_into_module(&mut jit_module, &module, &layout_plan)
            .expect("fail-indirect module should compile");
        jit_module
            .finalize_definitions()
            .expect("finalize definitions should succeed");

        let driver_id = *func_ids.get("driver").expect("driver function id");
        let driver_ptr = jit_module.get_finalized_function(driver_id);
        let driver: unsafe extern "C" fn(i64) -> usize = unsafe { std::mem::transmute(driver_ptr) };
        let result_ptr = unsafe { driver(55) };
        assert_ne!(result_ptr, 0, "driver result pointer should not be null");
        let tag = unsafe { *(result_ptr as *const i32) };
        assert_eq!(tag, 1, "indirect fail call should propagate Err tag");
        let payload = unsafe { *((result_ptr as *const u8).add(8) as *const i64) };
        assert_eq!(
            payload, 55,
            "indirect fail call should preserve Err payload"
        );
    }

    #[test]
    fn cranelift_backend_emits_object_in_aot_mode() {
        let module = sample_codegen_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        let config = BackendConfig {
            mode: CodegenMode::Aot,
            ..BackendConfig::default()
        };

        let artifact = backend
            .compile_module(&module, &manifest, &config)
            .expect("AOT compilation should succeed");

        assert!(
            !artifact.object.is_empty(),
            "AOT mode should emit object bytes"
        );
    }

    #[test]
    fn cranelift_backend_supports_external_namespaced_calls_in_aot_mode() {
        let module = sample_external_call_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        let config = BackendConfig {
            mode: CodegenMode::Aot,
            ..BackendConfig::default()
        };

        let artifact = backend
            .compile_module(&module, &manifest, &config)
            .expect("external namespaced call should compile in AOT mode");
        assert!(!artifact.object.is_empty());
    }

    #[test]
    fn cranelift_backend_rejects_conflicting_external_call_signatures() {
        let module = sample_external_conflicting_signature_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        let config = BackendConfig {
            mode: CodegenMode::Aot,
            ..BackendConfig::default()
        };

        let err = backend
            .compile_module(&module, &manifest, &config)
            .expect_err("conflicting external signatures should fail");
        assert!(matches!(
            err,
            CodegenError::UnsupportedMir { ref detail, .. }
                if detail.contains("conflicting signatures")
        ));
    }

    #[test]
    fn cranelift_backend_lowers_record_field_load_from_layout_offsets() {
        let module = sample_record_field_load_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        let config = BackendConfig {
            mode: CodegenMode::Aot,
            ..BackendConfig::default()
        };

        let artifact = backend
            .compile_module(&module, &manifest, &config)
            .expect("record field load lowering should compile");
        assert!(!artifact.object.is_empty());
    }

    #[test]
    fn cranelift_backend_lowers_record_init_and_field_load() {
        let module = sample_record_init_and_load_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        let config = BackendConfig {
            mode: CodegenMode::Aot,
            ..BackendConfig::default()
        };

        let artifact = backend
            .compile_module(&module, &manifest, &config)
            .expect("record init + field load lowering should compile");
        assert!(!artifact.object.is_empty());
    }

    #[test]
    fn cranelift_backend_executes_record_init_reuse_and_field_load() {
        let module = sample_record_init_reuse_and_load_main_module();
        let exit_code =
            execute_mir_main_jit(&module, &BackendConfig::default()).expect("main should execute");
        assert_eq!(exit_code, 7);
    }

    #[test]
    fn cranelift_backend_executes_record_init_from_token_and_field_load() {
        let module = sample_record_init_from_token_and_load_main_module();
        let exit_code =
            execute_mir_main_jit(&module, &BackendConfig::default()).expect("main should execute");
        assert_eq!(exit_code, 7);
    }

    #[test]
    fn cranelift_backend_executes_sum_init_reuse_and_tag_load() {
        let module = sample_sum_init_reuse_and_tag_load_main_module();
        let exit_code =
            execute_mir_main_jit(&module, &BackendConfig::default()).expect("main should execute");
        assert_eq!(exit_code, 1);
    }

    #[test]
    fn cranelift_backend_lowers_sum_init() {
        let module = sample_sum_init_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        let config = BackendConfig {
            mode: CodegenMode::Aot,
            ..BackendConfig::default()
        };

        let artifact = backend
            .compile_module(&module, &manifest, &config)
            .expect("sum init lowering should compile");
        assert!(!artifact.object.is_empty());
    }

    #[test]
    fn cranelift_backend_lowers_sum_tag_load() {
        let module = sample_sum_tag_load_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        let config = BackendConfig {
            mode: CodegenMode::Aot,
            ..BackendConfig::default()
        };

        let artifact = backend
            .compile_module(&module, &manifest, &config)
            .expect("sum tag load lowering should compile");
        assert!(!artifact.object.is_empty());
    }

    #[test]
    fn cranelift_backend_lowers_sum_payload_load() {
        let module = sample_sum_payload_load_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;
        let config = BackendConfig {
            mode: CodegenMode::Aot,
            ..BackendConfig::default()
        };

        let artifact = backend
            .compile_module(&module, &manifest, &config)
            .expect("sum payload load lowering should compile");
        assert!(!artifact.object.is_empty());
    }

    #[test]
    fn cranelift_backend_compiles_branch_terminators() {
        let module = sample_cfg_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("branch lowering should compile");
    }

    #[test]
    fn cranelift_backend_accepts_record_handle_signatures() {
        let module = sample_record_handle_signature_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("record handle signature should compile");
    }

    #[test]
    fn cranelift_backend_accepts_sum_handle_signatures() {
        let module = sample_sum_handle_signature_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("sum handle signature should compile");
    }

    #[test]
    fn cranelift_backend_compiles_tail_self_call_with_return_call() {
        let module = sample_tail_recursive_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("tail self-call lowering should compile");
        assert_eq!(artifact.stats.per_function[0].tail_self_call_count, 1);
    }

    #[test]
    fn cranelift_backend_compiles_handler_cell_tail_self_call_through_join_return() {
        let module = sample_handler_cell_tail_recursive_through_join_return_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("handler-cell tail self-call lowering should compile");
        assert_eq!(artifact.stats.per_function[0].tail_self_call_count, 1);
    }

    #[test]
    fn compile_hir_module_runs_pipeline() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "id".to_string(),
                params: vec![HirParam {
                    name: Some("x".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::Var("x".to_string()),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![Type::Int], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let artifact = compile_hir_module(&CraneliftBackend, &hir, &BackendConfig::default())
            .expect("pipeline should compile");
        assert_eq!(artifact.stats.per_function.len(), 1);
        assert_eq!(artifact.stats.per_function[0].function, "id");
    }

    #[test]
    fn compile_hir_module_lowers_unit_if_control_flow() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "gate".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::If {
                        condition: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Bool(true)),
                            ty: Type::Bool,
                            span: kea_ast::Span::synthetic(),
                        }),
                        then_branch: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Unit),
                            ty: Type::Unit,
                            span: kea_ast::Span::synthetic(),
                        }),
                        else_branch: Some(Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Unit),
                            ty: Type::Unit,
                            span: kea_ast::Span::synthetic(),
                        })),
                    },
                    ty: Type::Unit,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Unit)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let artifact = compile_hir_module(&CraneliftBackend, &hir, &BackendConfig::default())
            .expect("unit if pipeline should compile");
        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    fn compile_hir_module_lowers_value_if_control_flow() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "pick".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::If {
                        condition: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Bool(true)),
                            ty: Type::Bool,
                            span: kea_ast::Span::synthetic(),
                        }),
                        then_branch: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }),
                        else_branch: Some(Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(2)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        })),
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let artifact = compile_hir_module(&CraneliftBackend, &hir, &BackendConfig::default())
            .expect("value if pipeline should compile");
        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    fn compile_hir_module_lowers_unary_negation() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "negate".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Unary {
                        op: kea_ast::UnaryOp::Neg,
                        operand: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(3)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }),
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let artifact = compile_hir_module(&CraneliftBackend, &hir, &BackendConfig::default())
            .expect("unary lowering should compile");
        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    fn compile_hir_module_lowers_int_equality_condition() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::If {
                        condition: Box::new(HirExpr {
                            kind: HirExprKind::Binary {
                                op: kea_ast::BinOp::Eq,
                                left: Box::new(HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::Int(2)),
                                    ty: Type::Int,
                                    span: kea_ast::Span::synthetic(),
                                }),
                                right: Box::new(HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::Int(2)),
                                    ty: Type::Int,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::Bool,
                            span: kea_ast::Span::synthetic(),
                        }),
                        then_branch: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }),
                        else_branch: Some(Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(0)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        })),
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let artifact = compile_hir_module(&CraneliftBackend, &hir, &BackendConfig::default())
            .expect("int equality branch should compile");
        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    fn compile_hir_module_lowers_short_circuit_boolean_ops() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "both".to_string(),
                params: vec![
                    HirParam {
                        name: Some("x".to_string()),
                        span: kea_ast::Span::synthetic(),
                    },
                    HirParam {
                        name: Some("y".to_string()),
                        span: kea_ast::Span::synthetic(),
                    },
                ],
                body: HirExpr {
                    kind: HirExprKind::Binary {
                        op: kea_ast::BinOp::And,
                        left: Box::new(HirExpr {
                            kind: HirExprKind::Var("x".to_string()),
                            ty: Type::Bool,
                            span: kea_ast::Span::synthetic(),
                        }),
                        right: Box::new(HirExpr {
                            kind: HirExprKind::Var("y".to_string()),
                            ty: Type::Bool,
                            span: kea_ast::Span::synthetic(),
                        }),
                    },
                    ty: Type::Bool,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![Type::Bool, Type::Bool], Type::Bool)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let artifact = compile_hir_module(&CraneliftBackend, &hir, &BackendConfig::default())
            .expect("short-circuit boolean lowering should compile");
        assert_eq!(artifact.stats.per_function.len(), 1);
    }

    #[test]
    fn execute_hir_main_jit_returns_exit_code() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Lit(kea_ast::Lit::Int(7)),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let exit_code =
            execute_hir_main_jit(&hir, &BackendConfig::default()).expect("main should execute");
        assert_eq!(exit_code, 7);
    }

    #[test]
    fn execute_hir_main_jit_rejects_parameterized_main() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![HirParam {
                    name: Some("x".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::Var("x".to_string()),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![Type::Int], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let err = execute_hir_main_jit(&hir, &BackendConfig::default())
            .expect_err("parameterized main should be rejected");
        assert!(matches!(err, CodegenError::UnsupportedMir { .. }));
    }

    #[test]
    fn execute_hir_main_jit_supports_fail_only_main_ok_path() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Lit(kea_ast::Lit::Int(11)),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Int,
                    EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let exit_code = execute_hir_main_jit(&hir, &BackendConfig::default())
            .expect("fail-only main ok path should execute");
        assert_eq!(exit_code, 11);
    }

    #[test]
    fn execute_hir_main_jit_reports_fail_only_main_err_path() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("Fail.fail".to_string()),
                            ty: Type::Dynamic,
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(9)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Never,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Int,
                    EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                span: kea_ast::Span::synthetic(),
            })],
        };

        let err = execute_hir_main_jit(&hir, &BackendConfig::default())
            .expect_err("fail-only main err path should report unhandled fail");
        assert!(matches!(
            err,
            CodegenError::UnsupportedMir { function, ref detail }
                if function == "main" && detail.contains("unhandled Fail")
        ));
    }
}

//! Backend interface and Cranelift backend scaffold for Kea MIR.
//!
//! This crate defines the backend contract for 0d and provides a first
//! Cranelift-backed implementor. The API is backend-neutral: backends consume
//! MIR + ABI manifest + target config and return code artifacts,
//! diagnostics, and machine-readable pass stats.

use std::collections::{BTreeMap, BTreeSet};
use std::os::raw::c_char;
use std::sync::Arc;

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
    MirBinaryOp, MirCallee, MirEffectOpClass, MirFunction, MirInst, MirLiteral, MirModule,
    MirTerminator, MirUnaryOp, MirValueId, lower_hir_module,
};
use kea_types::{EffectRow, Type};

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
            logical_return: function.signature.ret.clone(),
            runtime_return: Type::Result(
                Box::new(function.signature.ret.clone()),
                Box::new(err_ty),
            ),
            fail_result_abi: true,
        };
    }

    RuntimeFunctionSig {
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

unsafe extern "C" fn kea_net_connect_stub(addr: *const c_char) -> i64 {
    if addr.is_null() { -1 } else { 1 }
}

unsafe extern "C" fn kea_net_send_stub(_conn: i64, _data: *const c_char) -> i8 {
    0
}

unsafe extern "C" fn kea_net_recv_stub(_conn: i64, size: i64) -> i64 {
    if size < 0 { 0 } else { size }
}

unsafe extern "C" fn kea_io_write_file_stub(_path: *const c_char, _data: *const c_char) -> i8 {
    0
}

unsafe extern "C" fn kea_io_read_file_stub(path: *const c_char) -> *const c_char {
    static EMPTY: &[u8] = b"\0";
    if path.is_null() {
        EMPTY.as_ptr() as *const c_char
    } else {
        path
    }
}

fn register_jit_runtime_symbols(builder: &mut JITBuilder) {
    builder.symbol("__kea_net_connect", kea_net_connect_stub as *const u8);
    builder.symbol("__kea_net_send", kea_net_send_stub as *const u8);
    builder.symbol("__kea_net_recv", kea_net_recv_stub as *const u8);
    builder.symbol("__kea_io_write_file", kea_io_write_file_stub as *const u8);
    builder.symbol("__kea_io_read_file", kea_io_read_file_stub as *const u8);
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
    let mut requires_clock_time = false;
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
                        | MirInst::ClosureInit { .. }
                        | MirInst::SumInit { .. }
                        | MirInst::Const {
                            literal: MirLiteral::String(_),
                            ..
                        }
                )
            })
        });
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "IO" && operation == "stdout"
                )
            })
        }) {
            requires_io_stdout = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "IO" && operation == "stderr"
                )
            })
        }) {
            requires_io_stderr = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "IO" && operation == "read_file"
                )
            })
        }) {
            requires_io_read_file = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "IO" && operation == "write_file"
                )
            })
        }) {
            requires_io_write_file = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "Clock" && matches!(operation.as_str(), "now" | "monotonic")
                )
            })
        }) {
            requires_clock_time = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "Rand" && operation == "int"
                )
            })
        }) {
            requires_rand_int = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "Rand" && operation == "seed"
                )
            })
        }) {
            requires_rand_seed = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "Net" && operation == "connect"
                )
            })
        }) {
            requires_net_connect = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "Net" && operation == "send"
                )
            })
        }) {
            requires_net_send = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::EffectOp {
                        class: MirEffectOpClass::Direct,
                        effect,
                        operation,
                        ..
                    } if effect == "Net" && operation == "recv"
                )
            })
        }) {
            requires_net_recv = true;
        }
        if function.blocks.iter().any(|block| {
            block.instructions.iter().any(|inst| {
                matches!(
                    inst,
                    MirInst::Binary {
                        op: MirBinaryOp::Concat,
                        ..
                    }
                )
            })
        }) {
            requires_string_concat = true;
            requires_heap_alloc = true;
        }
        if function.blocks.iter().any(|block| {
            block
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Release { .. }))
        }) {
            requires_free = true;
        }
        let needs_fail_result_alloc = runtime_sig.fail_result_abi
            || (matches!(runtime_sig.runtime_return, Type::Result(_, _))
                && function.blocks.iter().any(|block| {
                    block.instructions.iter().any(|inst| {
                        matches!(
                            inst,
                            MirInst::EffectOp {
                                class: MirEffectOpClass::ZeroResume,
                                effect,
                                operation,
                                ..
                            } if effect == "Fail" && operation == "fail"
                        )
                    })
                }));
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

    let time_func_id = if requires_clock_time {
        let ptr_ty = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(ptr_ty));
        signature.returns.push(AbiParam::new(ptr_ty));
        Some(
            module
                .declare_function("time", Linkage::Import, &signature)
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

                let tail_self_call = detect_tail_self_call(&function.name, block);
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
                    time_func_id,
                    rand_func_id,
                    srand_func_id,
                    net_connect_func_id,
                    net_send_func_id,
                    net_recv_func_id,
                    strlen_func_id,
                    memcpy_func_id,
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
    if !matches!(main_runtime_sig.logical_return, Type::Int | Type::Unit) {
        return Err(CodegenError::UnsupportedMir {
            function: "main".to_string(),
            detail: format!(
                "JIT entrypoint only supports `main` returning Int or Unit (got `{}`)",
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
            .any(|block| detect_tail_self_call(&function.name, block).is_some())
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
    let mut signatures: BTreeMap<String, (Vec<Type>, Type)> = BTreeMap::new();

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

                match signatures.get(name) {
                    Some((existing_params, existing_ret))
                        if existing_params != arg_types || existing_ret != ret_type =>
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
                        signatures.insert(name.clone(), (arg_types.clone(), ret_type.clone()));
                    }
                }
            }
        }
    }

    let mut clif_signatures = BTreeMap::new();
    for (name, (params, ret)) in signatures {
        let mut signature = module.make_signature();
        for param in params {
            signature.params.push(AbiParam::new(clif_type(&param)?));
        }
        if ret != Type::Unit {
            signature.returns.push(AbiParam::new(clif_type(&ret)?));
        }
        clif_signatures.insert(name, signature);
    }
    Ok(clif_signatures)
}

fn clif_type(ty: &Type) -> Result<cranelift::prelude::Type, CodegenError> {
    match ty {
        Type::Int => Ok(types::I64),
        Type::Float => Ok(types::F64),
        Type::Bool => Ok(types::I8),
        Type::Unit => Ok(types::I8),
        Type::String => Ok(types::I64),
        Type::Dynamic => Ok(types::I64),
        // 0d bootstrap aggregate/runtime representation:
        // nominal records/sums and Result-like carriers flow through ABI as
        // opaque machine-word handles until full aggregate lowering lands.
        Type::Record(_)
        | Type::AnonRecord(_)
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
    let payload_clif_ty = clif_type(payload_ty)?;
    let payload = coerce_value_to_clif_type(builder, payload, payload_clif_ty);
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
    time_func_id: Option<FuncId>,
    rand_func_id: Option<FuncId>,
    srand_func_id: Option<FuncId>,
    net_connect_func_id: Option<FuncId>,
    net_send_func_id: Option<FuncId>,
    net_recv_func_id: Option<FuncId>,
    strlen_func_id: Option<FuncId>,
    memcpy_func_id: Option<FuncId>,
    runtime_signatures: &'a BTreeMap<String, RuntimeFunctionSig>,
    current_runtime_sig: &'a RuntimeFunctionSig,
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
                lower_binary(builder, function_name, *op, lhs, rhs)?
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
                    detail: format!(
                        "record field `{record_type}.{field_name}` offset does not fit i32"
                    ),
                })?;
                builder
                    .ins()
                    .store(MemFlags::new(), field_value, base_ptr, offset);
            }
            values.insert(dest.clone(), base_ptr);
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
            let expected_fields = *layout.variant_field_counts.get(variant).ok_or_else(|| {
                CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "sum layout `{sum_type}` missing variant `{variant}` during init"
                    ),
                }
            })?;
            if expected_fields as usize != fields.len() {
                return Err(CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!(
                        "sum init `{sum_type}.{variant}` expected {} fields but got {}",
                        expected_fields,
                        fields.len()
                    ),
                });
            }
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

            let tag_offset =
                i32::try_from(layout.tag_offset).map_err(|_| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("sum tag offset for `{sum_type}` does not fit i32"),
                })?;
            let tag_value = builder.ins().iconst(types::I32, i64::from(*tag));
            builder
                .ins()
                .store(MemFlags::new(), tag_value, base_ptr, tag_offset);

            for (idx, field_value_id) in fields.iter().enumerate() {
                let field_value = get_value(values, function_name, field_value_id)?;
                let field_offset = layout.payload_offset + (idx as u32 * 8);
                let field_offset =
                    i32::try_from(field_offset).map_err(|_| CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "sum payload offset `{sum_type}.{variant}[{idx}]` does not fit i32"
                        ),
                    })?;
                builder
                    .ins()
                    .store(MemFlags::new(), field_value, base_ptr, field_offset);
            }
            values.insert(dest.clone(), base_ptr);
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
            let mut lowered_args = Vec::with_capacity(args.len());
            for arg in args {
                lowered_args.push(get_value(values, function_name, arg)?);
            }

            let mut callee_uses_fail_result_abi = false;
            let call_result = match callee {
                MirCallee::Local(name) => {
                    callee_uses_fail_result_abi = ctx
                        .runtime_signatures
                        .get(name)
                        .ok_or_else(|| CodegenError::UnknownFunction {
                            function: name.clone(),
                        })?
                        .fail_result_abi;
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
                    if arg_types.len() != args.len() {
                        return Err(CodegenError::UnsupportedMir {
                            function: function_name.to_string(),
                            detail: format!(
                                "external call `{name}` has {} args but {} arg types",
                                args.len(),
                                arg_types.len()
                            ),
                        });
                    }
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
                    if arg_types.len() != args.len() {
                        return Err(CodegenError::UnsupportedMir {
                            function: function_name.to_string(),
                            detail: format!(
                                "indirect call has {} args but {} arg types",
                                args.len(),
                                arg_types.len()
                            ),
                        });
                    }
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
                    if *ret_type != Type::Unit {
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
                                        detail:
                                            "IO.stdout expects exactly one string argument".to_string(),
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
                                        detail:
                                            "IO.stderr expects exactly one string argument".to_string(),
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
                                let write_ref = module.declare_func_in_func(write_func_id, builder.func);
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
                                        detail:
                                            "IO.write_file expects exactly two string arguments"
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
                                        detail:
                                            "IO.read_file expects exactly one string argument".to_string(),
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
                                    values.insert(dest.clone(), coerce_value_to_clif_type(builder, raw, ptr_ty));
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
                    } else if effect == "Clock" && matches!(operation.as_str(), "now" | "monotonic")
                    {
                    if !args.is_empty() {
                        return Err(CodegenError::UnsupportedMir {
                            function: function_name.to_string(),
                            detail: format!("Clock.{operation} expects no arguments"),
                        });
                    }
                    let time_func_id = ctx
                        .time_func_id
                        .ok_or_else(|| CodegenError::UnsupportedMir {
                            function: function_name.to_string(),
                            detail: format!(
                                "Clock.{operation} lowering requires imported `time` symbol"
                            ),
                        })?;
                    let time_ref = module.declare_func_in_func(time_func_id, builder.func);
                    let ptr_ty = module.target_config().pointer_type();
                    let null_ptr = builder.ins().iconst(ptr_ty, 0);
                    let time_call = builder.ins().call(time_ref, &[null_ptr]);
                    if let Some(dest) = result {
                        let timestamp = builder
                            .inst_results(time_call)
                            .first()
                            .copied()
                            .ok_or_else(|| CodegenError::UnsupportedMir {
                                function: function_name.to_string(),
                                detail: "time call returned no value".to_string(),
                            })?;
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
                            let rand_func_id = ctx
                                .rand_func_id
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
                            let seed_value_id = args.first().ok_or_else(|| CodegenError::UnsupportedMir {
                                function: function_name.to_string(),
                                detail: "Rand.seed expects one Int argument".to_string(),
                            })?;
                            if args.len() != 1 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Rand.seed expects exactly one Int argument".to_string(),
                                });
                            }
                            let seed_value = get_value(values, function_name, seed_value_id)?;
                            let seed_value = coerce_value_to_clif_type(builder, seed_value, types::I32);
                            let srand_func_id = ctx
                                .srand_func_id
                                .ok_or_else(|| CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Rand.seed lowering requires imported `srand` symbol"
                                        .to_string(),
                                })?;
                            let srand_ref = module.declare_func_in_func(srand_func_id, builder.func);
                            let _ = builder.ins().call(srand_ref, &[seed_value]);
                            if let Some(dest) = result {
                                values.insert(dest.clone(), builder.ins().iconst(types::I8, 0));
                            }
                            Ok(false)
                        }
                        _ => unreachable!("Rand branch is guarded by operation match"),
                    }
                } else if effect == "Net" && matches!(operation.as_str(), "connect" | "send" | "recv") {
                    match operation.as_str() {
                        "connect" => {
                            let addr_value_id = args.first().ok_or_else(|| CodegenError::UnsupportedMir {
                                function: function_name.to_string(),
                                detail: "Net.connect expects one String argument".to_string(),
                            })?;
                            if args.len() != 1 {
                                return Err(CodegenError::UnsupportedMir {
                                    function: function_name.to_string(),
                                    detail: "Net.connect expects exactly one String argument".to_string(),
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
                                values.insert(dest.clone(), coerce_value_to_clif_type(builder, conn, types::I64));
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
                            let conn_value = coerce_value_to_clif_type(builder, conn_value, types::I64);
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
                            let conn_value = coerce_value_to_clif_type(builder, conn_value, types::I64);
                            let size_value = coerce_value_to_clif_type(builder, size_value, types::I64);
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
                                values.insert(dest.clone(), coerce_value_to_clif_type(builder, received, types::I64));
                            }
                            Ok(false)
                        }
                        _ => unreachable!("Net branch is guarded by operation match"),
                    }
                } else {
                    Err(CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!("instruction `{inst:?}` not implemented in 0d pure lowering"),
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
            let rc_ptr = builder.ins().iadd_imm(payload_ptr, -8);
            let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
            let next = builder.ins().iadd_imm(rc_value, 1);
            builder.ins().store(MemFlags::new(), next, rc_ptr, 0);
            Ok(false)
        }
        MirInst::Release { value } => {
            let ptr_ty = module.target_config().pointer_type();
            let payload_ptr = get_value(values, function_name, value)?;
            let payload_ptr = coerce_value_to_clif_type(builder, payload_ptr, ptr_ty);
            let rc_ptr = builder.ins().iadd_imm(payload_ptr, -8);
            let rc_value = builder.ins().load(types::I64, MemFlags::new(), rc_ptr, 0);
            let next = builder.ins().iadd_imm(rc_value, -1);
            builder.ins().store(MemFlags::new(), next, rc_ptr, 0);

            let free_func_id = ctx
                .free_func_id
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: "release lowering requires imported `free` symbol".to_string(),
                })?;
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
            detail: "non-tail-resumptive handlers are not yet supported in compiled mode"
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

fn lower_binary(
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
        MirBinaryOp::Div if lhs_ty.is_int() => builder.ins().sdiv(lhs, rhs),
        MirBinaryOp::Mod if lhs_ty.is_int() => builder.ins().srem(lhs, rhs),

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

    if let Some(tail_call) = detect_tail_self_call(ctx.function_name, block) {
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
                        detail: "non-unit function returned without value".to_string(),
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
                detail: "non-unit function returned without value".to_string(),
            })?;
            let mut value = get_value(ctx.values, ctx.function_name, value_id)?;
            if ctx.function_name == "main" && ctx.current_runtime_sig.logical_return == Type::Int {
                value = coerce_value_to_clif_type(builder, value, types::I32);
            }
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

fn detect_tail_self_call(function_name: &str, block: &kea_mir::MirBlock) -> Option<TailSelfCall> {
    let MirInst::Call {
        callee: MirCallee::Local(callee_name),
        args,
        result,
        ..
    } = block.instructions.last()?
    else {
        return None;
    };

    if callee_name != function_name {
        return None;
    }

    match (&block.terminator, result) {
        (MirTerminator::Return { value: Some(ret) }, Some(call_result)) if ret == call_result => {
            Some(TailSelfCall { args: args.clone() })
        }
        (MirTerminator::Return { value: None }, None) => Some(TailSelfCall { args: args.clone() }),
        _ => None,
    }
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

fn plan_layout_catalog(module: &MirModule) -> Result<BackendLayoutPlan, CodegenError> {
    const WORD_BYTES: u32 = 8;
    const TAG_BYTES: u32 = 4;

    let mut plan = BackendLayoutPlan::default();

    for record in &module.layouts.records {
        let mut field_offsets = BTreeMap::new();
        let mut field_types = BTreeMap::new();
        for (idx, field) in record.fields.iter().enumerate() {
            field_offsets.insert(field.name.clone(), idx as u32 * WORD_BYTES);
            let field_ty = match &field.annotation {
                kea_ast::TypeAnnotation::Named(name) if name == "Int" => Type::Int,
                kea_ast::TypeAnnotation::Named(name) if name == "Float" => Type::Float,
                kea_ast::TypeAnnotation::Named(name) if name == "Bool" => Type::Bool,
                kea_ast::TypeAnnotation::Named(name) if name == "String" => Type::String,
                kea_ast::TypeAnnotation::Named(name) if name == "Unit" => Type::Unit,
                _ => Type::Dynamic,
            };
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
        let max_payload_fields = sum
            .variants
            .iter()
            .map(|variant| variant.fields.len() as u32)
            .max()
            .unwrap_or(0);
        for variant in &sum.variants {
            variant_tags.insert(variant.name.clone(), variant.tag);
            variant_field_counts.insert(variant.name.clone(), variant.fields.len() as u32);
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
        if detect_tail_self_call(&function.name, block).is_some() {
            stats.tail_self_call_count += 1;
        }
        for inst in &block.instructions {
            match inst {
                MirInst::Retain { .. } => stats.retain_count += 1,
                MirInst::Release { .. } => stats.release_count += 1,
                MirInst::Call { .. } => {}
                MirInst::HandlerEnter { .. } => stats.handler_enter_count += 1,
                MirInst::HandlerExit { .. } => stats.handler_exit_count += 1,
                MirInst::Resume { .. } => stats.resume_count += 1,
                MirInst::EffectOp { class, .. } => match class {
                    MirEffectOpClass::Direct => stats.effect_op_direct_count += 1,
                    MirEffectOpClass::Dispatch => stats.effect_op_dispatch_count += 1,
                    MirEffectOpClass::ZeroResume => stats.effect_op_zero_resume_count += 1,
                },
                MirInst::CowUpdate { .. }
                | MirInst::RecordInit { .. }
                | MirInst::SumInit { .. }
                | MirInst::ClosureInit { .. } => stats.alloc_count += 1,
                MirInst::Const { .. }
                | MirInst::Binary { .. }
                | MirInst::Unary { .. }
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

    stats
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
        MirBlock, MirBlockId, MirFunctionSignature, MirLayoutCatalog, MirRecordFieldLayout,
        MirRecordLayout, MirSumLayout, MirTerminator, MirVariantFieldLayout, MirVariantLayout,
    };
    use kea_types::{FunctionType, Label, RecordType, RowType, SumType};

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
            .expect_err("resume should report non-tail handler support gap");
        assert!(matches!(
            err,
            CodegenError::UnsupportedMir { function, ref detail }
                if function == "handler_markers"
                    && detail.contains("non-tail-resumptive handlers are not yet supported")
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
        assert_eq!(function.effect_op_direct_count, 1);
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
    fn collect_pass_stats_detects_tail_self_call_with_release_prefix() {
        let module = sample_tail_recursive_with_release_prefix_module();
        let stats = collect_pass_stats(&module);

        assert_eq!(stats.per_function.len(), 1);
        let function = &stats.per_function[0];
        assert_eq!(function.tail_self_call_count, 1);
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

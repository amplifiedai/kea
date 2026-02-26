//! Backend interface and Cranelift backend scaffold for Kea MIR.
//!
//! This crate defines the backend contract for 0d and provides a first
//! Cranelift-backed implementor. The API is backend-neutral: backends consume
//! MIR + ABI manifest + target config and return code artifacts,
//! diagnostics, and machine-readable pass stats.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use cranelift::prelude::{
    AbiParam, Configurable, FunctionBuilder, FunctionBuilderContext, InstBuilder, Value, types,
};
use cranelift_codegen::ir::{MemFlags, TrapCode};
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::{isa, settings};
use cranelift_codegen::isa::CallConv;
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
    #[error("ABI manifest parameter class count mismatch for `{function}`: expected {expected}, got {actual}")]
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

fn compile_with_jit(
    module: &MirModule,
    layout_plan: &BackendLayoutPlan,
    isa: &Arc<dyn isa::TargetIsa>,
    _config: &BackendConfig,
) -> Result<Vec<u8>, CodegenError> {
    let builder = JITBuilder::with_isa(isa.clone(), cranelift_module::default_libcall_names());
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
    let mut func_ids: BTreeMap<String, FuncId> = BTreeMap::new();
    let mut external_func_ids: BTreeMap<String, FuncId> = BTreeMap::new();
    let mut signatures: BTreeMap<String, cranelift_codegen::ir::Signature> = BTreeMap::new();
    let external_signatures = collect_external_call_signatures(module, mir)?;
    let requires_record_alloc = mir.functions.iter().any(|function| {
        function.blocks.iter().any(|block| {
            block
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::RecordInit { .. } | MirInst::SumInit { .. }))
        })
    });

    for function in &mir.functions {
        let signature = build_signature(module, function)?;
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

    let malloc_func_id = if requires_record_alloc {
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

    let mut builder_context = FunctionBuilderContext::new();

    for function in &mir.functions {
        let mut context = module.make_context();
        context.func.signature = signatures
            .get(&function.name)
            .cloned()
            .ok_or_else(|| CodegenError::UnknownFunction {
                function: function.name.clone(),
            })?;

        {
            let mut builder = FunctionBuilder::new(&mut context.func, &mut builder_context);
            let mut block_map = BTreeMap::new();
            for block in &function.blocks {
                block_map.insert(block.id.clone(), builder.create_block());
            }

            let entry_block = *block_map
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
                    for (index, value) in builder.block_params(clif_block).iter().copied().enumerate() {
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
                        return_ty: &function.signature.ret,
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

        let func_id = *func_ids
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
    if !main.signature.params.is_empty() {
        return Err(CodegenError::UnsupportedMir {
            function: "main".to_string(),
            detail: "JIT entrypoint requires zero-argument `main`".to_string(),
        });
    }
    if !matches!(main.signature.ret, Type::Int | Type::Unit) {
        return Err(CodegenError::UnsupportedMir {
            function: "main".to_string(),
            detail: format!(
                "JIT entrypoint only supports `main` returning Int or Unit (got `{}`)",
                main.signature.ret
            ),
        });
    }

    let isa = build_isa(config)?;
    let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
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
        match main.signature.ret {
            Type::Int => {
                let main_fn = std::mem::transmute::<*const u8, extern "C" fn() -> i64>(entrypoint);
                main_fn() as i32
            }
            Type::Unit => {
                let main_fn = std::mem::transmute::<*const u8, extern "C" fn()>(entrypoint);
                main_fn();
                0
            }
            _ => unreachable!("validated return type before JIT entrypoint dispatch"),
        }
    };
    Ok(exit_code)
}

fn build_signature<M: Module>(
    module: &M,
    function: &MirFunction,
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

    if function.signature.ret != Type::Unit {
        let ret_type = clif_type(&function.signature.ret)?;
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
        // 0d bootstrap aggregate/runtime representation:
        // nominal records/sums and Result-like carriers flow through ABI as
        // opaque machine-word handles until full aggregate lowering lands.
        Type::Record(_)
        | Type::AnonRecord(_)
        | Type::Sum(_)
        | Type::Option(_)
        | Type::Result(_, _)
        | Type::Opaque { .. } => Ok(types::I64),
        unsupported => Err(CodegenError::UnsupportedType {
            ty: unsupported.to_string(),
        }),
    }
}

struct LowerInstCtx<'a> {
    func_ids: &'a BTreeMap<String, FuncId>,
    external_func_ids: &'a BTreeMap<String, FuncId>,
    layout_plan: &'a BackendLayoutPlan,
    malloc_func_id: Option<FuncId>,
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
            let value = lower_literal(builder, literal, function_name)?;
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
            let result = lower_binary(builder, function_name, *op, lhs, rhs)?;
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
            let layout = ctx
                .layout_plan
                .records
                .get(record_type)
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("record layout `{record_type}` not found"),
                })?;
            let malloc_func_id = ctx.malloc_func_id.ok_or_else(|| CodegenError::UnsupportedMir {
                function: function_name.to_string(),
                detail: format!(
                    "record allocation requested for `{record_type}` but malloc import was not declared"
                ),
            })?;
            let malloc_ref = module.declare_func_in_func(malloc_func_id, builder.func);
            let ptr_ty = module.target_config().pointer_type();
            let alloc_size = i64::from(layout.size_bytes.max(1));
            let size_value = builder.ins().iconst(ptr_ty, alloc_size);
            let alloc_call = builder.ins().call(malloc_ref, &[size_value]);
            let base_ptr = builder
                .inst_results(alloc_call)
                .first()
                .copied()
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: "malloc call returned no pointer value".to_string(),
                })?;
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
            let layout = ctx
                .layout_plan
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
            let malloc_func_id = ctx.malloc_func_id.ok_or_else(|| CodegenError::UnsupportedMir {
                function: function_name.to_string(),
                detail: format!(
                    "sum allocation requested for `{sum_type}` but malloc import was not declared"
                ),
            })?;
            let malloc_ref = module.declare_func_in_func(malloc_func_id, builder.func);
            let ptr_ty = module.target_config().pointer_type();
            let alloc_size = i64::from(layout.size_bytes.max(1));
            let size_value = builder.ins().iconst(ptr_ty, alloc_size);
            let alloc_call = builder.ins().call(malloc_ref, &[size_value]);
            let base_ptr = builder
                .inst_results(alloc_call)
                .first()
                .copied()
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: "malloc call returned no pointer value".to_string(),
                })?;

            let tag_offset = i32::try_from(layout.tag_offset).map_err(|_| {
                CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("sum tag offset for `{sum_type}` does not fit i32"),
                }
            })?;
            let tag_value = builder.ins().iconst(types::I32, i64::from(*tag));
            builder
                .ins()
                .store(MemFlags::new(), tag_value, base_ptr, tag_offset);

            for (idx, field_value_id) in fields.iter().enumerate() {
                let field_value = get_value(values, function_name, field_value_id)?;
                let field_offset = layout.payload_offset + (idx as u32 * 8);
                let field_offset = i32::try_from(field_offset).map_err(|_| {
                    CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!(
                            "sum payload offset `{sum_type}.{variant}[{idx}]` does not fit i32"
                        ),
                    }
                })?;
                builder
                    .ins()
                    .store(MemFlags::new(), field_value, base_ptr, field_offset);
            }
            values.insert(dest.clone(), base_ptr);
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
            let layout = ctx
                .layout_plan
                .records
                .get(record_type)
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function_name.to_string(),
                    detail: format!("record layout `{record_type}` not found"),
                })?;
            let offset = *layout
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
                layout.field_types.get(field).cloned().unwrap_or(Type::Dynamic)
            } else {
                field_ty.clone()
            };
            let value_ty = clif_type(&resolved_field_ty)?;
            let value = builder.ins().load(value_ty, MemFlags::new(), addr, 0);
            values.insert(dest.clone(), value);
            Ok(false)
        }
        MirInst::Call {
            callee,
            args,
            arg_types,
            result,
            ret_type,
            ..
        } => {
            let mut lowered_args = Vec::with_capacity(args.len());
            for arg in args {
                lowered_args.push(get_value(values, function_name, arg)?);
            }

            let call_result = match callee {
                MirCallee::Local(name) => {
                    let callee_id = *ctx
                        .func_ids
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
                    let callee_id = *ctx
                        .external_func_ids
                        .get(name)
                        .ok_or_else(|| CodegenError::UnknownFunction {
                            function: name.clone(),
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
                    return Err(CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: "indirect function calls are not implemented in 0d".to_string(),
                    });
                }
            };

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
            result,
            ..
        } => {
            if *class == MirEffectOpClass::ZeroResume && effect == "Fail" && operation == "fail" {
                if result.is_some() {
                    return Err(CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail:
                            "Fail.zero-resume operation must not produce a value in 0d lowering"
                                .to_string(),
                    });
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
        MirInst::Nop => Ok(false),
        MirInst::Retain { .. }
        | MirInst::Release { .. }
        | MirInst::Move { .. }
        | MirInst::Borrow { .. }
        | MirInst::TryClaim { .. }
        | MirInst::Freeze { .. }
        | MirInst::CowUpdate { .. }
        | MirInst::HandlerEnter { .. }
        | MirInst::HandlerExit { .. }
        | MirInst::Resume { .. } => Err(CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: format!("instruction `{inst:?}` not implemented in 0d pure lowering"),
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
            let pred = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs);
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
                detail: format!("binary operation `{op:?}` unsupported for Cranelift type `{lhs_ty}`"),
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
    return_ty: &'a Type,
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
        let callee_id = *ctx
            .func_ids
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
            if *ctx.return_ty == Type::Unit {
                builder.ins().return_(&[]);
                return Ok(());
            }

            let value_id = value.as_ref().ok_or_else(|| CodegenError::UnsupportedMir {
                function: ctx.function_name.to_string(),
                detail: "non-unit function returned without value".to_string(),
            })?;
            let value = get_value(ctx.values, ctx.function_name, value_id)?;
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
            builder.ins().brif(bool_pred, then_clif, &[], else_clif, &[]);
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
                | MirInst::SumInit { .. } => stats.alloc_count += 1,
                MirInst::Const { .. }
                | MirInst::Binary { .. }
                | MirInst::Unary { .. }
                | MirInst::RecordFieldLoad { .. }
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
                            callee: MirCallee::External("List::len".to_string()),
                            args: vec![MirValueId(0)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(1)),
                            ret_type: Type::Int,
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
                                callee: MirCallee::External("List::len".to_string()),
                                args: vec![MirValueId(0)],
                                arg_types: vec![Type::Int],
                                result: Some(MirValueId(1)),
                                ret_type: Type::Int,
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
                                callee: MirCallee::External("List::len".to_string()),
                                args: vec![MirValueId(0)],
                                arg_types: vec![Type::Float],
                                result: Some(MirValueId(1)),
                                ret_type: Type::Int,
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

        let err =
            validate_fail_only_invariants(&module).expect_err("should reject dispatch in Fail-only");
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

        let err =
            validate_fail_only_invariants(&module).expect_err("should reject handler ops in Fail-only");
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
    fn default_abi_manifest_marks_effect_evidence_for_effectful_functions() {
        let module = sample_stats_module();
        let manifest = default_abi_manifest(&module);

        let sig = manifest.get("stats_only").expect("stats_only signature");
        assert_eq!(sig.effect_evidence, AbiEffectEvidencePlacement::TrailingParam);
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
        assert!(artifact.object.is_empty(), "JIT mode should not emit object bytes");
    }

    #[test]
    fn cranelift_backend_accepts_zero_resume_fail_effect_op() {
        let module = sample_fail_only_module_with_inst(MirInst::EffectOp {
            class: MirEffectOpClass::ZeroResume,
            effect: "Fail".to_string(),
            operation: "fail".to_string(),
            args: vec![],
            result: None,
        });
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("zero-resume Fail effect op should lower in 0d");
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

        assert!(!artifact.object.is_empty(), "AOT mode should emit object bytes");
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
}

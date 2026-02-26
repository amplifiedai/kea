//! Backend interface and Cranelift backend scaffold for Kea MIR.
//!
//! This crate defines the backend contract for 0d and provides a first
//! Cranelift-backed implementor. The API is backend-neutral: backends consume
//! MIR + ABI manifest + target config and return code artifacts,
//! diagnostics, and machine-readable pass stats.

use std::collections::BTreeMap;
use std::sync::Arc;

use cranelift::prelude::{
    AbiParam, Configurable, FunctionBuilder, FunctionBuilderContext, InstBuilder, Value, types,
};
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::{isa, settings};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use kea_hir::HirModule;
use kea_mir::{
    MirBinaryOp, MirCallee, MirEffectOpClass, MirFunction, MirInst, MirLiteral, MirModule,
    MirTerminator, MirValueId, lower_hir_module,
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

        let isa = build_isa(config)?;
        let stats = collect_pass_stats(module);
        let object = match config.mode {
            CodegenMode::Jit => compile_with_jit(module, &isa, config)?,
            CodegenMode::Aot => compile_with_object(module, &isa, config)?,
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
    isa: &Arc<dyn isa::TargetIsa>,
    _config: &BackendConfig,
) -> Result<Vec<u8>, CodegenError> {
    let builder = JITBuilder::with_isa(isa.clone(), cranelift_module::default_libcall_names());
    let mut jit_module = JITModule::new(builder);
    compile_into_module(&mut jit_module, module)?;
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
    compile_into_module(&mut object_module, module)?;
    let product = object_module.finish();
    product.emit().map_err(|detail| CodegenError::ObjectEmit {
        detail: detail.to_string(),
    })
}

fn compile_into_module<M: Module>(module: &mut M, mir: &MirModule) -> Result<(), CodegenError> {
    let mut func_ids: BTreeMap<String, FuncId> = BTreeMap::new();
    let mut signatures: BTreeMap<String, cranelift_codegen::ir::Signature> = BTreeMap::new();

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
            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);
            builder.seal_block(entry_block);

            let mut values: BTreeMap<MirValueId, Value> = BTreeMap::new();
            for (index, value) in builder.block_params(entry_block).iter().copied().enumerate() {
                values.insert(MirValueId(index as u32), value);
            }

            let block = function
                .blocks
                .iter()
                .find(|block| block.id == function.entry)
                .ok_or_else(|| CodegenError::UnsupportedMir {
                    function: function.name.clone(),
                    detail: "entry block missing".to_string(),
                })?;

            for inst in &block.instructions {
                lower_instruction(module, &mut builder, &function.name, inst, &mut values, &func_ids)?;
            }
            lower_terminator(&mut builder, &function.name, &block.terminator, &function.signature.ret, &values)?;
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
                detail: detail.to_string(),
            })?;
        module.clear_context(&mut context);
    }

    Ok(())
}

fn build_signature<M: Module>(
    module: &M,
    function: &MirFunction,
) -> Result<cranelift_codegen::ir::Signature, CodegenError> {
    let mut signature = module.make_signature();

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

fn clif_type(ty: &Type) -> Result<cranelift::prelude::Type, CodegenError> {
    match ty {
        Type::Int => Ok(types::I64),
        Type::Float => Ok(types::F64),
        Type::Bool => Ok(types::I8),
        unsupported => Err(CodegenError::UnsupportedType {
            ty: unsupported.to_string(),
        }),
    }
}

fn lower_instruction<M: Module>(
    module: &mut M,
    builder: &mut FunctionBuilder,
    function_name: &str,
    inst: &MirInst,
    values: &mut BTreeMap<MirValueId, Value>,
    func_ids: &BTreeMap<String, FuncId>,
) -> Result<(), CodegenError> {
    match inst {
        MirInst::Const { dest, literal } => {
            let value = lower_literal(builder, literal, function_name)?;
            values.insert(dest.clone(), value);
            Ok(())
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
            Ok(())
        }
        MirInst::Call {
            callee,
            args,
            result,
            ..
        } => {
            let mut lowered_args = Vec::with_capacity(args.len());
            for arg in args {
                lowered_args.push(get_value(values, function_name, arg)?);
            }

            let call_result = match callee {
                MirCallee::Local(name) => {
                    let callee_id = *func_ids.get(name).ok_or_else(|| CodegenError::UnknownFunction {
                        function: name.clone(),
                    })?;
                    let local_ref = module.declare_func_in_func(callee_id, builder.func);
                    let call = builder.ins().call(local_ref, &lowered_args);
                    builder.inst_results(call).first().copied()
                }
                MirCallee::External(name) => {
                    return Err(CodegenError::UnsupportedMir {
                        function: function_name.to_string(),
                        detail: format!("external call `{name}` is not implemented in 0d"),
                    });
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

            Ok(())
        }
        MirInst::Nop => Ok(()),
        MirInst::Retain { .. }
        | MirInst::Release { .. }
        | MirInst::Move { .. }
        | MirInst::Borrow { .. }
        | MirInst::TryClaim { .. }
        | MirInst::Freeze { .. }
        | MirInst::CowUpdate { .. }
        | MirInst::EffectOp { .. }
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

fn b1_to_i8(builder: &mut FunctionBuilder, predicate: Value) -> Value {
    builder.ins().uextend(types::I8, predicate)
}

fn lower_terminator(
    builder: &mut FunctionBuilder,
    function_name: &str,
    terminator: &MirTerminator,
    return_ty: &Type,
    values: &BTreeMap<MirValueId, Value>,
) -> Result<(), CodegenError> {
    match terminator {
        MirTerminator::Return { value } => {
            if *return_ty == Type::Unit {
                builder.ins().return_(&[]);
                return Ok(());
            }

            let value_id = value.as_ref().ok_or_else(|| CodegenError::UnsupportedMir {
                function: function_name.to_string(),
                detail: "non-unit function returned without value".to_string(),
            })?;
            let value = get_value(values, function_name, value_id)?;
            builder.ins().return_(&[value]);
            Ok(())
        }
        MirTerminator::Jump { .. }
        | MirTerminator::Branch { .. }
        | MirTerminator::Unreachable => Err(CodegenError::UnsupportedMir {
            function: function_name.to_string(),
            detail: format!("terminator `{terminator:?}` is not implemented in 0d pure lowering"),
        }),
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
                MirInst::CowUpdate { .. } => stats.alloc_count += 1,
                MirInst::Const { .. }
                | MirInst::Binary { .. }
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
    use kea_mir::{MirBlock, MirBlockId, MirFunctionSignature, MirTerminator};
    use kea_types::{FunctionType, Label};

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
}

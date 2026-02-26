//! Backend interface and Cranelift backend scaffold for Kea MIR.
//!
//! This crate defines the backend contract for 0d and provides a first
//! Cranelift-backed implementor placeholder. The API is backend-neutral:
//! backends consume MIR + ABI manifest + target config and return code
//! artifacts, diagnostics, and machine-readable pass stats.

use std::collections::BTreeMap;

use kea_hir::HirModule;
use kea_mir::{MirEffectOpClass, MirFunction, MirInst, MirModule, lower_hir_module};
use kea_types::EffectRow;

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
    #[error("backend `{backend}` does not support mode `{mode:?}`")]
    UnsupportedMode { backend: String, mode: CodegenMode },
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
        if matches!(config.mode, CodegenMode::Aot) {
            // AOT object emission lands later in 0d; this keeps the backend
            // contract explicit while the implementation is still scaffolded.
            return Err(CodegenError::UnsupportedMode {
                backend: self.name().to_string(),
                mode: config.mode,
            });
        }

        validate_abi_manifest(module, abi)?;

        Ok(BackendArtifact {
            // Placeholder object payload while MIR→Cranelift lowering is built.
            object: Vec::new(),
            stats: collect_pass_stats(module),
        })
    }
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
    use kea_mir::{MirBlock, MirBlockId, MirFunctionSignature, MirTerminator, MirValueId};
    use kea_types::{Label, Type};

    fn sample_module() -> MirModule {
        MirModule {
            functions: vec![MirFunction {
                name: "write".to_string(),
                signature: MirFunctionSignature {
                    params: vec![Type::String],
                    ret: Type::Unit,
                    effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                },
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    id: MirBlockId(0),
                    instructions: vec![
                        MirInst::Retain {
                            value: MirValueId(1),
                        },
                        MirInst::Release {
                            value: MirValueId(1),
                        },
                        MirInst::EffectOp {
                            class: MirEffectOpClass::Direct,
                            effect: "IO".to_string(),
                            operation: "stdout".to_string(),
                            args: vec![MirValueId(1)],
                            result: None,
                        },
                    ],
                    terminator: MirTerminator::Return { value: None },
                }],
            }],
        }
    }

    #[test]
    fn validate_abi_manifest_reports_missing_function() {
        let module = sample_module();
        let empty_manifest = AbiManifest {
            functions: BTreeMap::new(),
        };

        let err = validate_abi_manifest(&module, &empty_manifest).expect_err("should fail");
        assert!(matches!(err, CodegenError::MissingAbiEntry { .. }));
    }

    #[test]
    fn default_abi_manifest_marks_effect_evidence_for_effectful_functions() {
        let module = sample_module();
        let manifest = default_abi_manifest(&module);

        let sig = manifest.get("write").expect("write signature");
        assert_eq!(sig.effect_evidence, AbiEffectEvidencePlacement::TrailingParam);
    }

    #[test]
    fn cranelift_backend_returns_pass_stats() {
        let module = sample_module();
        let manifest = default_abi_manifest(&module);
        let backend = CraneliftBackend;

        let artifact = backend
            .compile_module(&module, &manifest, &BackendConfig::default())
            .expect("compilation should succeed");

        assert_eq!(artifact.stats.per_function.len(), 1);
        let stats = &artifact.stats.per_function[0];
        assert_eq!(stats.retain_count, 1);
        assert_eq!(stats.release_count, 1);
        assert_eq!(stats.effect_op_direct_count, 1);
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
                ty: Type::Function(kea_types::FunctionType::pure(vec![Type::Int], Type::Int)),
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

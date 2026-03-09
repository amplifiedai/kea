//! Backend-neutral mid-level IR (MIR) for Kea.
//!
//! This crate defines explicit control-flow + memory/effect operations that are
//! independent of any specific backend API (Cranelift, LLVM, etc.).

use std::collections::{BTreeMap, BTreeSet};

use kea_ast::{BinOp, DeclKind, ExprKind as AstExprKind, TypeAnnotation, UnaryOp};
use kea_hir::{HirDecl, HirExpr, HirExprKind, HirFunction, HirHandleClause, HirModule, HirPattern};
use kea_types::{EffectRow, FunctionType, Label, RecordType, SumType, Type};

/// Configuration for MIR lowering passes.
#[derive(Debug, Clone, Default)]
pub struct MirLoweringConfig {
    /// Enable handler inlining (devirtualize callback closures).
    /// Default: false (JIT — compilation cost dominates).
    /// Use `MirLoweringConfig::aot()` for AOT mode where compilation is amortized.
    /// Override with `KEA_NO_HANDLER_INLINE=1` (force off) or
    /// `KEA_HANDLER_INLINE=1` (force on).
    pub handler_inlining: bool,
}

impl MirLoweringConfig {
    /// AOT defaults: handler inlining on (compilation cost amortized).
    pub fn aot() -> Self {
        Self {
            handler_inlining: true,
        }
    }

    /// JIT defaults: handler inlining off (compilation cost dominates).
    pub fn jit() -> Self {
        Self {
            handler_inlining: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MirValueId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MirBlockId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub struct MirModule {
    pub functions: Vec<MirFunction>,
    pub layouts: MirLayoutCatalog,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct MirLayoutCatalog {
    pub records: Vec<MirRecordLayout>,
    pub sums: Vec<MirSumLayout>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirRecordLayout {
    pub name: String,
    pub is_unboxed: bool,
    pub fields: Vec<MirRecordFieldLayout>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirRecordFieldLayout {
    pub name: String,
    pub annotation: kea_ast::TypeAnnotation,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirSumLayout {
    pub name: String,
    pub variants: Vec<MirVariantLayout>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirVariantLayout {
    pub name: String,
    pub tag: u32,
    pub fields: Vec<MirVariantFieldLayout>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirVariantFieldLayout {
    pub name: Option<String>,
    pub annotation: kea_ast::TypeAnnotation,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirFunction {
    pub name: String,
    pub signature: MirFunctionSignature,
    pub entry: MirBlockId,
    pub blocks: Vec<MirBlock>,
    /// Whether this function was annotated with `@fip`. FIP functions use reuse
    /// tokens for all memory management; explicit Release insertion would conflict
    /// with the FIP verifier which requires zero explicit releases.
    pub is_fip: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirFunctionSignature {
    pub params: Vec<Type>,
    pub ret: Type,
    pub effects: EffectRow,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirBlock {
    pub id: MirBlockId,
    pub params: Vec<MirBlockParam>,
    pub instructions: Vec<MirInst>,
    pub terminator: MirTerminator,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirBlockParam {
    pub id: MirValueId,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MirInst {
    Const {
        dest: MirValueId,
        literal: MirLiteral,
    },
    Binary {
        dest: MirValueId,
        op: MirBinaryOp,
        left: MirValueId,
        right: MirValueId,
    },
    Unary {
        dest: MirValueId,
        op: MirUnaryOp,
        operand: MirValueId,
    },
    RecordInit {
        dest: MirValueId,
        record_type: String,
        fields: Vec<(String, MirValueId)>,
    },
    RecordInitReuse {
        dest: MirValueId,
        source: MirValueId,
        record_type: String,
        fields: Vec<(String, MirValueId)>,
    },
    ReuseToken {
        dest: MirValueId,
        source: MirValueId,
    },
    RecordInitFromToken {
        dest: MirValueId,
        token: MirValueId,
        record_type: String,
        fields: Vec<(String, MirValueId)>,
    },
    SumInit {
        dest: MirValueId,
        sum_type: String,
        variant: String,
        tag: u32,
        fields: Vec<MirValueId>,
    },
    SumInitReuse {
        dest: MirValueId,
        source: MirValueId,
        sum_type: String,
        variant: String,
        tag: u32,
        fields: Vec<MirValueId>,
    },
    SumInitFromToken {
        dest: MirValueId,
        token: MirValueId,
        sum_type: String,
        variant: String,
        tag: u32,
        fields: Vec<MirValueId>,
    },
    SumTagLoad {
        dest: MirValueId,
        sum: MirValueId,
        sum_type: String,
    },
    SumPayloadLoad {
        dest: MirValueId,
        sum: MirValueId,
        sum_type: String,
        variant: String,
        field_index: usize,
        field_ty: Type,
    },
    RecordFieldLoad {
        dest: MirValueId,
        record: MirValueId,
        record_type: String,
        field: String,
        field_ty: Type,
    },
    FunctionRef {
        dest: MirValueId,
        function: String,
    },
    ClosureInit {
        dest: MirValueId,
        entry: MirValueId,
        captures: Vec<MirValueId>,
        capture_types: Vec<Type>,
    },
    ClosureCaptureLoad {
        dest: MirValueId,
        closure: MirValueId,
        capture_index: usize,
        capture_ty: Type,
    },
    StateCellNew {
        dest: MirValueId,
        initial: MirValueId,
    },
    StateCellLoad {
        dest: MirValueId,
        cell: MirValueId,
    },
    StateCellStore {
        cell: MirValueId,
        value: MirValueId,
    },
    Retain {
        value: MirValueId,
    },
    Release {
        value: MirValueId,
    },
    Move {
        dest: MirValueId,
        src: MirValueId,
    },
    Borrow {
        dest: MirValueId,
        src: MirValueId,
    },
    TryClaim {
        dest: MirValueId,
        src: MirValueId,
    },
    Freeze {
        dest: MirValueId,
        src: MirValueId,
    },
    CowUpdate {
        dest: MirValueId,
        target: MirValueId,
        record_type: String,
        updates: Vec<MirFieldUpdate>,
        unique_path: MirBlockId,
        copy_path: MirBlockId,
    },
    EffectOp {
        class: MirEffectOpClass,
        effect: String,
        operation: String,
        args: Vec<MirValueId>,
        result: Option<MirValueId>,
    },
    HandlerEnter {
        effect: String,
    },
    HandlerExit {
        effect: String,
    },
    Resume {
        value: MirValueId,
    },
    Call {
        callee: MirCallee,
        args: Vec<MirValueId>,
        arg_types: Vec<Type>,
        result: Option<MirValueId>,
        ret_type: Type,
        callee_fail_result_abi: bool,
        capture_fail_result: bool,
        cc_manifest_id: String,
    },
    Unsupported {
        detail: String,
    },
    Nop,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirFieldUpdate {
    pub field: String,
    pub value: MirValueId,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MirCallee {
    Local(String),
    External(String),
    Value(MirValueId),
}

#[derive(Debug, Clone, PartialEq)]
pub enum MirLiteral {
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(char),
    String(String),
    Unit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirBinaryOp {
    Add,
    Sub,
    Mul,
    WrappingAdd,
    WrappingSub,
    WrappingMul,
    Div,
    Mod,
    Concat,
    Combine,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
    ShiftRightUnsigned,
    In,
    NotIn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirUnaryOp {
    Neg,
    Not,
    BitNot,
    Popcount,
    LeadingZeros,
    TrailingZeros,
    WidenSignedToInt,
    WidenUnsignedToInt,
    /// Truncate an `Int` (i64) value to a narrower fixed-width type.
    /// The stored bits are the low-order bits of the i64.
    NarrowToI8,
    NarrowToI16,
    NarrowToI32,
    NarrowToU8,
    NarrowToU16,
    NarrowToU32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirEffectOpClass {
    Direct,
    Dispatch,
    ZeroResume,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MirTerminator {
    Jump {
        target: MirBlockId,
        args: Vec<MirValueId>,
    },
    Branch {
        condition: MirValueId,
        then_block: MirBlockId,
        else_block: MirBlockId,
    },
    Return {
        value: Option<MirValueId>,
    },
    Unreachable,
}

impl MirInst {
    pub fn is_memory_op(&self) -> bool {
        matches!(
            self,
            MirInst::Retain { .. }
                | MirInst::Release { .. }
                | MirInst::Move { .. }
                | MirInst::Borrow { .. }
                | MirInst::TryClaim { .. }
                | MirInst::Freeze { .. }
                | MirInst::RecordInit { .. }
                | MirInst::RecordInitReuse { .. }
                | MirInst::ReuseToken { .. }
                | MirInst::RecordInitFromToken { .. }
                | MirInst::SumInit { .. }
                | MirInst::SumInitReuse { .. }
                | MirInst::SumInitFromToken { .. }
                | MirInst::ClosureInit { .. }
                | MirInst::SumTagLoad { .. }
                | MirInst::SumPayloadLoad { .. }
                | MirInst::RecordFieldLoad { .. }
                | MirInst::ClosureCaptureLoad { .. }
                | MirInst::StateCellNew { .. }
                | MirInst::StateCellLoad { .. }
                | MirInst::StateCellStore { .. }
                | MirInst::CowUpdate { .. }
        )
    }

    pub fn is_handler_op(&self) -> bool {
        matches!(
            self,
            MirInst::HandlerEnter { .. } | MirInst::HandlerExit { .. } | MirInst::Resume { .. }
        )
    }
}

pub fn lower_hir_module(module: &HirModule) -> MirModule {
    lower_hir_module_with_config(module, &MirLoweringConfig::default())
}

pub fn lower_hir_module_with_config(module: &HirModule, config: &MirLoweringConfig) -> MirModule {
    let import_aliases = collect_import_aliases(module);
    let mut known_functions = module
        .declarations
        .iter()
        .filter_map(|decl| match decl {
            HirDecl::Function(function) => Some(function.name.clone()),
            HirDecl::Raw(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let mut known_function_types = module
        .declarations
        .iter()
        .filter_map(|decl| match decl {
            HirDecl::Function(function) => Some((function.name.clone(), function.ty.clone())),
            HirDecl::Raw(_) => None,
        })
        .collect::<BTreeMap<_, _>>();
    let known_function_alias_targets =
        collect_namespaced_alias_targets(known_function_types.keys(), &import_aliases);
    extend_namespaced_set_with_import_aliases(&mut known_functions, &import_aliases);
    extend_namespaced_map_with_import_aliases(&mut known_function_types, &import_aliases);
    let intrinsic_symbols = collect_intrinsic_symbols(module);
    let mut effect_operations = collect_effect_operations(module);
    extend_namespaced_map_with_import_aliases(&mut effect_operations, &import_aliases);
    let mut known_function_dispatch_effects =
        collect_function_dispatch_effects(module, &effect_operations);
    extend_namespaced_map_with_import_aliases(
        &mut known_function_dispatch_effects,
        &import_aliases,
    );
    let lambda_factories = collect_lambda_factory_templates(module, &known_functions);
    let known_const_exprs = collect_const_field_exprs(module);
    let mut layouts = MirLayoutCatalog::default();
    for decl in &module.declarations {
        if let HirDecl::Raw(raw_decl) = decl {
            collect_layout_metadata(raw_decl, &mut layouts);
        }
    }
    seed_builtin_sum_layouts(&mut layouts);
    seed_anon_record_layouts(module, &mut layouts);
    let mut functions = Vec::new();
    for decl in &module.declarations {
        if let HirDecl::Function(function) = decl {
            let lowered = lower_hir_function(
                function,
                &layouts,
                &known_functions,
                &known_function_types,
                &known_function_alias_targets,
                &known_const_exprs,
                &intrinsic_symbols,
                &effect_operations,
                &known_function_dispatch_effects,
                &lambda_factories,
                false,
            );
            functions.extend(lowered);
        }
    }
    // Generate default capability wrapper functions.  These are zero-capture
    // closures whose entry calls the runtime directly.  Entry-point functions
    // (main) create ClosureInit references to these wrappers so that capability
    // cells can be threaded to callees even when no user handler is installed.
    functions.extend(generate_default_capability_wrappers(&effect_operations));
    // Remove functions that contain Unsupported instructions, and transitively
    // remove any function that calls a removed function.  This handles:
    // - Generic functions with unresolvable trait dispatch (direct Unsupported)
    // - Concrete wrappers that delegate to those generic functions (transitive)
    functions = filter_unsupported_functions_transitive(functions);

    // Handler inlining: devirtualize callback closures when structurally verified.
    // Default: on for AOT, off for JIT (compilation cost dominates in JIT).
    // Override: KEA_HANDLER_INLINE=1 forces on, KEA_NO_HANDLER_INLINE=1 forces off.
    // Set KEA_HANDLER_INLINE_STATS=1 to print rewrite counts to stderr.
    let handler_inline_enabled = if std::env::var("KEA_NO_HANDLER_INLINE").as_deref() == Ok("1") {
        false
    } else if std::env::var("KEA_HANDLER_INLINE").as_deref() == Ok("1") {
        true
    } else {
        config.handler_inlining
    };
    if handler_inline_enabled {
        let fn_index: BTreeMap<String, usize> = functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.name.clone(), i))
            .collect();
        let (mut total_get, mut total_put, mut total_pure) = (0usize, 0usize, 0usize);
        for i in 0..functions.len() {
            let (g, p, c) = inline_known_handler_callbacks(i, &mut functions, &fn_index);
            total_get += g;
            total_put += p;
            total_pure += c;
        }
        if std::env::var("KEA_HANDLER_INLINE_STATS").as_deref() == Ok("1")
            && (total_get + total_put + total_pure) > 0
        {
            eprintln!(
                "[handler-inline] state_get={total_get} state_put={total_put} pure={total_pure}"
            );
        }
    }

    for function in &mut functions {
        insert_retains_for_reused_call_args(function, &layouts);
        insert_releases_for_dead_params(function, &layouts);
        rewrite_trmc_descending_sum_chain(function);
        emit_reuse_tokens_for_trailing_release_alloc(function, &layouts);
        schedule_trailing_releases_after_last_use(function);
        elide_adjacent_retain_release_pairs(function);
        fuse_release_alloc_same_layout(function, &layouts);
        fuse_release_alloc_cross_block_jump(function, &layouts);
        emit_reuse_tokens_for_mixed_predecessor_joins(function, &layouts);
        emit_reuse_tokens_for_loop_backedge_joins(function, &layouts);
    }

    if std::env::var("KEA_DUMP_MIR").as_deref() == Ok("1") {
        for function in &functions {
            eprintln!("=== MIR: {} ===", function.name);
            for block in &function.blocks {
                let params: Vec<String> = block
                    .params
                    .iter()
                    .map(|p| format!("v{}:{:?}", p.id.0, p.ty))
                    .collect();
                eprintln!("  block b{} (params: [{}]):", block.id.0, params.join(", "));
                for (i, inst) in block.instructions.iter().enumerate() {
                    eprintln!("    {i:3}: {inst:?}");
                }
                eprintln!("    term: {:?}", block.terminator);
            }
        }
    }

    MirModule { functions, layouts }
}

/// Classify what a closure wraps, determined by structural verification of the
/// entry wrapper and its target function body.
#[derive(Debug, Clone)]
enum InlinableCallback {
    /// State.get: captures[0] is the state cell, replace Call with StateCellLoad
    StateGet { state_cell: MirValueId },
    /// State.put: captures[0] is the state cell, replace Call with StateCellStore + Unit
    StatePut { state_cell: MirValueId },
    /// Pure callback: replace Call with a Const or Move
    PureCallback {
        replacement: PureCallbackReplacement,
        num_call_args: usize,
    },
}

/// What a pure callback returns — resolved during structural verification.
#[derive(Debug, Clone)]
enum PureCallbackReplacement {
    /// Return a constant literal (e.g., `resume 42`, `resume ()`)
    Const(MirLiteral),
    /// Return a captured value, resolved from ClosureInit captures
    CaptureValue(MirValueId),
    /// Return a call argument by index (resolved at rewrite time)
    CallArg(usize),
}

/// MIR optimization pass: devirtualize handler callback closures when structurally
/// verified as safe. Phase A: state-get/state-put → direct ops. Phase B: pure
/// callbacks (constant return, capture return, arg passthrough) → Const/Move.
///
/// Only applies when handler and dispatch site are in the same function (Case 1).
/// Chain-augmented callbacks (`__chain_callback`) are explicitly skipped.
fn inline_known_handler_callbacks(
    func_idx: usize,
    functions: &mut [MirFunction],
    fn_index: &BTreeMap<String, usize>,
) -> (usize, usize, usize) {
    // Returns (state_get_inlined, state_put_inlined, pure_callback_inlined)
    let function = &functions[func_idx];
    // Phase 1: Build analysis maps by scanning all instructions
    let mut fn_ref_map: BTreeMap<MirValueId, String> = BTreeMap::new();
    let mut closure_map: BTreeMap<MirValueId, (String, Vec<MirValueId>)> = BTreeMap::new();

    for block in &function.blocks {
        for inst in &block.instructions {
            match inst {
                MirInst::FunctionRef { dest, function } => {
                    fn_ref_map.insert(dest.clone(), function.clone());
                }
                MirInst::ClosureInit {
                    dest,
                    entry,
                    captures,
                    ..
                } => {
                    if let Some(entry_name) = fn_ref_map.get(entry) {
                        closure_map.insert(dest.clone(), (entry_name.clone(), captures.clone()));
                    }
                }
                _ => {}
            }
        }
    }

    // Phase 2: Structural verification — classify each closure
    let mut inlinable: BTreeMap<MirValueId, InlinableCallback> = BTreeMap::new();

    for (closure_id, (entry_name, captures)) in &closure_map {
        // Skip chain-augmented callbacks (stacking wrappers)
        if entry_name.contains("__chain_callback") {
            continue;
        }

        // Structural verification: look up entry wrapper function
        let Some(&wrapper_idx) = fn_index.get(entry_name.as_str()) else {
            continue;
        };
        let wrapper_fn = &functions[wrapper_idx];

        // Entry wrapper must be single-block with ClosureCaptureLoad(s) → Call(Local(target))
        if wrapper_fn.blocks.len() != 1 {
            continue;
        }
        let wrapper_block = &wrapper_fn.blocks[0];

        // Find the Call instruction (last instruction) and extract the target name
        let Some(MirInst::Call {
            callee: MirCallee::Local(target_name),
            args: wrapper_call_args,
            ..
        }) = wrapper_block.instructions.last()
        else {
            continue;
        };

        // Look up the target (impl) function and verify its body shape
        let Some(&target_idx) = fn_index.get(target_name.as_str()) else {
            continue;
        };
        let target_fn = &functions[target_idx];
        if target_fn.blocks.len() != 1 {
            continue;
        }
        let target_block = &target_fn.blocks[0];

        // Phase A: State wrapper devirtualization (name pre-filter + structural verification)
        let is_state_get = entry_name.ends_with("$state_get");
        let is_state_put = entry_name.ends_with("$state_put");

        if is_state_get {
            // State-get: exactly 1 capture (the state cell), 0 call params
            if captures.len() != 1 {
                continue;
            }
            // Wrapper shape: exactly 1 ClosureCaptureLoad(index=0) + 1 Call
            if wrapper_block.instructions.len() != 2 {
                continue;
            }
            if !matches!(
                &wrapper_block.instructions[0],
                MirInst::ClosureCaptureLoad {
                    capture_index: 0,
                    ..
                }
            ) {
                continue;
            }
            // Target shape: single StateCellLoad, return value matches loaded value
            if target_block.instructions.len() != 1 {
                continue;
            }
            let MirInst::StateCellLoad { dest: loaded, .. } = &target_block.instructions[0] else {
                continue;
            };
            // Verify terminator returns the loaded value
            if !matches!(
                &target_block.terminator,
                MirTerminator::Return { value: Some(v) } if v == loaded
            ) {
                continue;
            }
            // Target must accept exactly 1 param (the cell)
            if target_fn.signature.params.len() != 1 {
                continue;
            }
            inlinable.insert(
                closure_id.clone(),
                InlinableCallback::StateGet {
                    state_cell: captures[0].clone(),
                },
            );
        } else if is_state_put {
            // State-put: exactly 1 capture (the state cell), 1 call param (the value)
            if captures.len() != 1 {
                continue;
            }
            // Wrapper shape: exactly 1 ClosureCaptureLoad(index=0) + 1 Call
            if wrapper_block.instructions.len() != 2 {
                continue;
            }
            if !matches!(
                &wrapper_block.instructions[0],
                MirInst::ClosureCaptureLoad {
                    capture_index: 0,
                    ..
                }
            ) {
                continue;
            }
            // Target shape: StateCellStore + Const(Unit), return value matches unit const
            if target_block.instructions.len() != 2 {
                continue;
            }
            if !matches!(
                &target_block.instructions[0],
                MirInst::StateCellStore { .. }
            ) {
                continue;
            }
            let MirInst::Const {
                dest: unit_dest,
                literal: MirLiteral::Unit,
            } = &target_block.instructions[1]
            else {
                continue;
            };
            // Verify terminator returns the unit const
            if !matches!(
                &target_block.terminator,
                MirTerminator::Return { value: Some(v) } if v == unit_dest
            ) {
                continue;
            }
            // Target must accept exactly 2 params (cell, value)
            if target_fn.signature.params.len() != 2 {
                continue;
            }
            inlinable.insert(
                closure_id.clone(),
                InlinableCallback::StatePut {
                    state_cell: captures[0].clone(),
                },
            );
        } else {
            // Phase B: Pure callback devirtualization
            // Verify wrapper has only ClosureCaptureLoad instructions + final Call
            let num_wrapper_captures = wrapper_block
                .instructions
                .iter()
                .filter(|i| matches!(i, MirInst::ClosureCaptureLoad { .. }))
                .count();
            // All non-Call instructions must be ClosureCaptureLoad (no bound dispatch captures)
            if num_wrapper_captures + 1 != wrapper_block.instructions.len() {
                continue;
            }
            // Verify captures are sequential indices 0..N
            let captures_sequential = wrapper_block.instructions[..num_wrapper_captures]
                .iter()
                .enumerate()
                .all(|(i, inst)| {
                    matches!(inst, MirInst::ClosureCaptureLoad { capture_index, .. } if *capture_index == i)
                });
            if !captures_sequential {
                continue;
            }
            // Derive num_call_params from wrapper call args vs captures
            let num_call_params = wrapper_call_args.len().saturating_sub(num_wrapper_captures);
            // Verify capture count matches the closure's actual captures
            if captures.len() != num_wrapper_captures {
                continue;
            }
            // Target must be single-block, 0 or 1 instructions, pure
            if target_block.instructions.len() > 1 {
                continue;
            }
            // Determine what the target returns
            let MirTerminator::Return {
                value: Some(ret_val),
            } = &target_block.terminator
            else {
                continue;
            };
            if target_block.instructions.len() == 1 {
                // Single instruction: must be Const, and return value must match its dest
                let MirInst::Const { dest, literal } = &target_block.instructions[0] else {
                    continue;
                };
                if ret_val != dest {
                    continue;
                }
                inlinable.insert(
                    closure_id.clone(),
                    InlinableCallback::PureCallback {
                        replacement: PureCallbackReplacement::Const(literal.clone()),
                        num_call_args: num_call_params,
                    },
                );
            } else {
                // Zero instructions: return value must be a function parameter
                // Target params = captures (0..num_wrapper_captures) + call params
                let param_idx = ret_val.0 as usize;
                if param_idx >= target_fn.signature.params.len() {
                    continue;
                }
                if param_idx < num_wrapper_captures {
                    // Returns a capture — resolve to the actual MirValueId from ClosureInit
                    if param_idx >= captures.len() {
                        continue;
                    }
                    inlinable.insert(
                        closure_id.clone(),
                        InlinableCallback::PureCallback {
                            replacement: PureCallbackReplacement::CaptureValue(
                                captures[param_idx].clone(),
                            ),
                            num_call_args: num_call_params,
                        },
                    );
                } else {
                    // Returns a call arg
                    let call_arg_idx = param_idx - num_wrapper_captures;
                    if call_arg_idx >= num_call_params {
                        continue;
                    }
                    inlinable.insert(
                        closure_id.clone(),
                        InlinableCallback::PureCallback {
                            replacement: PureCallbackReplacement::CallArg(call_arg_idx),
                            num_call_args: num_call_params,
                        },
                    );
                }
            }
        }
    }

    if inlinable.is_empty() {
        return (0, 0, 0);
    }
    let mut state_get_count = 0usize;
    let mut state_put_count = 0usize;
    let mut pure_count = 0usize;

    // Reborrow mutably for rewrite and DCE phases
    let function = &mut functions[func_idx];

    // Phase 3: Rewrite — collect replacements then apply
    // Each replacement: (block_idx, inst_idx, replacement instructions)
    let mut replacements: Vec<(usize, usize, Vec<MirInst>)> = Vec::new();

    for (block_idx, block) in function.blocks.iter().enumerate() {
        for (inst_idx, inst) in block.instructions.iter().enumerate() {
            if let MirInst::Call {
                callee: MirCallee::Value(callee_value),
                args,
                result,
                ..
            } = inst
                && let Some(callback_kind) = inlinable.get(callee_value)
            {
                match callback_kind {
                    InlinableCallback::StateGet { state_cell } => {
                        if !args.is_empty() {
                            continue;
                        }
                        state_get_count += 1;
                        if let Some(dest) = result {
                            replacements.push((
                                block_idx,
                                inst_idx,
                                vec![MirInst::StateCellLoad {
                                    dest: dest.clone(),
                                    cell: state_cell.clone(),
                                }],
                            ));
                        } else {
                            replacements.push((block_idx, inst_idx, vec![MirInst::Nop]));
                        }
                    }
                    InlinableCallback::StatePut { state_cell } => {
                        if args.len() != 1 {
                            continue;
                        }
                        state_put_count += 1;
                        let mut insts = vec![MirInst::StateCellStore {
                            cell: state_cell.clone(),
                            value: args[0].clone(),
                        }];
                        if let Some(dest) = result {
                            insts.push(MirInst::Const {
                                dest: dest.clone(),
                                literal: MirLiteral::Unit,
                            });
                        }
                        replacements.push((block_idx, inst_idx, insts));
                    }
                    InlinableCallback::PureCallback {
                        replacement,
                        num_call_args,
                    } => {
                        if args.len() != *num_call_args {
                            continue;
                        }
                        pure_count += 1;
                        let insts = match replacement {
                            PureCallbackReplacement::Const(literal) => {
                                if let Some(dest) = result {
                                    vec![MirInst::Const {
                                        dest: dest.clone(),
                                        literal: literal.clone(),
                                    }]
                                } else {
                                    vec![MirInst::Nop]
                                }
                            }
                            PureCallbackReplacement::CaptureValue(src) => {
                                if let Some(dest) = result {
                                    vec![MirInst::Move {
                                        dest: dest.clone(),
                                        src: src.clone(),
                                    }]
                                } else {
                                    vec![MirInst::Nop]
                                }
                            }
                            PureCallbackReplacement::CallArg(idx) => {
                                if *idx >= args.len() {
                                    continue;
                                }
                                if let Some(dest) = result {
                                    vec![MirInst::Move {
                                        dest: dest.clone(),
                                        src: args[*idx].clone(),
                                    }]
                                } else {
                                    vec![MirInst::Nop]
                                }
                            }
                        };
                        replacements.push((block_idx, inst_idx, insts));
                    }
                }
            }
        }
    }

    // Apply replacements in reverse order to preserve indices
    for (block_idx, inst_idx, new_insts) in replacements.into_iter().rev() {
        let block = &mut function.blocks[block_idx];
        block.instructions.remove(inst_idx);
        for (offset, inst) in new_insts.into_iter().enumerate() {
            block.instructions.insert(inst_idx + offset, inst);
        }
    }

    // Phase 4: Two-pass dead code elimination for orphaned FunctionRef + ClosureInit
    for _ in 0..2 {
        let mut referenced: BTreeSet<MirValueId> = BTreeSet::new();
        for block in &function.blocks {
            for inst in &block.instructions {
                // Collect all values read by this instruction
                // Use a simple inline check rather than calling inst_reads_value for each candidate
                match inst {
                    MirInst::ClosureInit {
                        entry, captures, ..
                    } => {
                        referenced.insert(entry.clone());
                        for c in captures {
                            referenced.insert(c.clone());
                        }
                    }
                    MirInst::Call {
                        callee: MirCallee::Value(v),
                        args,
                        ..
                    } => {
                        referenced.insert(v.clone());
                        for a in args {
                            referenced.insert(a.clone());
                        }
                    }
                    MirInst::Call { args, .. } => {
                        for a in args {
                            referenced.insert(a.clone());
                        }
                    }
                    MirInst::StateCellLoad { cell, .. } => {
                        referenced.insert(cell.clone());
                    }
                    MirInst::StateCellStore { cell, value } => {
                        referenced.insert(cell.clone());
                        referenced.insert(value.clone());
                    }
                    MirInst::Binary { left, right, .. } => {
                        referenced.insert(left.clone());
                        referenced.insert(right.clone());
                    }
                    MirInst::Unary { operand, .. } => {
                        referenced.insert(operand.clone());
                    }
                    MirInst::StateCellNew { initial, .. } => {
                        referenced.insert(initial.clone());
                    }
                    MirInst::ClosureCaptureLoad { closure, .. } => {
                        referenced.insert(closure.clone());
                    }
                    MirInst::RecordInit { fields, .. } => {
                        for (_, v) in fields {
                            referenced.insert(v.clone());
                        }
                    }
                    MirInst::SumInit { fields, .. } => {
                        for v in fields {
                            referenced.insert(v.clone());
                        }
                    }
                    MirInst::RecordFieldLoad { record, .. } => {
                        referenced.insert(record.clone());
                    }
                    MirInst::SumTagLoad { sum, .. } | MirInst::SumPayloadLoad { sum, .. } => {
                        referenced.insert(sum.clone());
                    }
                    MirInst::Move { src, .. }
                    | MirInst::Borrow { src, .. }
                    | MirInst::TryClaim { src, .. }
                    | MirInst::Freeze { src, .. } => {
                        referenced.insert(src.clone());
                    }
                    MirInst::Retain { value } | MirInst::Release { value } => {
                        referenced.insert(value.clone());
                    }
                    MirInst::Resume { value } => {
                        referenced.insert(value.clone());
                    }
                    MirInst::EffectOp { args, .. } => {
                        for a in args {
                            referenced.insert(a.clone());
                        }
                    }
                    MirInst::CowUpdate {
                        target, updates, ..
                    } => {
                        referenced.insert(target.clone());
                        for u in updates {
                            referenced.insert(u.value.clone());
                        }
                    }
                    MirInst::RecordInitReuse { source, fields, .. } => {
                        referenced.insert(source.clone());
                        for (_, v) in fields {
                            referenced.insert(v.clone());
                        }
                    }
                    MirInst::SumInitReuse { source, fields, .. } => {
                        referenced.insert(source.clone());
                        for v in fields {
                            referenced.insert(v.clone());
                        }
                    }
                    MirInst::RecordInitFromToken { token, fields, .. } => {
                        referenced.insert(token.clone());
                        for (_, v) in fields {
                            referenced.insert(v.clone());
                        }
                    }
                    MirInst::SumInitFromToken { token, fields, .. } => {
                        referenced.insert(token.clone());
                        for v in fields {
                            referenced.insert(v.clone());
                        }
                    }
                    MirInst::ReuseToken { source, .. } => {
                        referenced.insert(source.clone());
                    }
                    MirInst::Const { .. }
                    | MirInst::FunctionRef { .. }
                    | MirInst::HandlerEnter { .. }
                    | MirInst::HandlerExit { .. }
                    | MirInst::Unsupported { .. }
                    | MirInst::Nop => {}
                }
            }
            // Also check terminator
            match &block.terminator {
                MirTerminator::Return { value: Some(v) } => {
                    referenced.insert(v.clone());
                }
                MirTerminator::Jump { args, .. } => {
                    for a in args {
                        referenced.insert(a.clone());
                    }
                }
                MirTerminator::Branch { condition, .. } => {
                    referenced.insert(condition.clone());
                }
                MirTerminator::Return { value: None } | MirTerminator::Unreachable => {}
            }
        }

        // Kill unreferenced FunctionRef and ClosureInit instructions
        for block in &mut function.blocks {
            for inst in &mut block.instructions {
                if matches!(
                    inst,
                    MirInst::FunctionRef { .. } | MirInst::ClosureInit { .. }
                ) && let Some(dest) = inst_defined_value(inst)
                    && !referenced.contains(dest)
                {
                    *inst = MirInst::Nop;
                }
            }
        }
    }
    (state_get_count, state_put_count, pure_count)
}

fn rewrite_trmc_descending_sum_chain(function: &mut MirFunction) {
    let function_arity = function.signature.params.len();
    if function_arity == 0 {
        return;
    }

    let Some(entry_idx) = function
        .blocks
        .iter()
        .position(|block| block.id == function.entry)
    else {
        return;
    };
    let (condition_value, then_id, else_id) = match &function.blocks[entry_idx].terminator {
        MirTerminator::Branch {
            condition,
            then_block,
            else_block,
        } => (condition.clone(), then_block.clone(), else_block.clone()),
        _ => return,
    };

    let Some(then_idx) = function.blocks.iter().position(|block| block.id == then_id) else {
        return;
    };
    let Some(else_idx) = function.blocks.iter().position(|block| block.id == else_id) else {
        return;
    };

    let (then_join_target, then_value, else_join_target, else_value) = match (
        &function.blocks[then_idx].terminator,
        &function.blocks[else_idx].terminator,
    ) {
        (
            MirTerminator::Jump {
                target: then_target,
                args: then_args,
            },
            MirTerminator::Jump {
                target: else_target,
                args: else_args,
            },
        ) if then_args.len() == 1 && else_args.len() == 1 => (
            then_target.clone(),
            then_args[0].clone(),
            else_target.clone(),
            else_args[0].clone(),
        ),
        _ => return,
    };
    if then_join_target != else_join_target {
        return;
    }

    let Some(join_idx) = function
        .blocks
        .iter()
        .position(|block| block.id == then_join_target)
    else {
        return;
    };
    let join_block = &function.blocks[join_idx];
    match (
        join_block.params.as_slice(),
        &join_block.terminator,
        join_block.instructions.as_slice(),
    ) {
        (
            [MirBlockParam { id, .. }],
            MirTerminator::Return {
                value: Some(return_value),
            },
            [MirInst::Nop],
        ) if return_value == id => {}
        _ => return,
    }
    let then_is_recursive =
        block_has_recursive_self_call(&function.blocks[then_idx], &function.name);
    let else_is_recursive =
        block_has_recursive_self_call(&function.blocks[else_idx], &function.name);
    if then_is_recursive == else_is_recursive {
        return;
    }
    let (base_idx, recurse_idx, base_value, recurse_value) = if then_is_recursive {
        (else_idx, then_idx, else_value, then_value)
    } else {
        (then_idx, else_idx, then_value, else_value)
    };

    let recurse_block = &function.blocks[recurse_idx];
    let Some((
        call_idx,
        call_result,
        call_arg,
        recursive_param_idx,
        recursive_param_value,
        constructor_idx,
        constructor,
    )) = find_recursive_constructor_pattern(
        recurse_block,
        &function.name,
        &recurse_value,
        function_arity,
    )
    else {
        return;
    };
    if function.signature.params.get(recursive_param_idx) != Some(&Type::Int) {
        return;
    }
    let recurse_on_then = recurse_idx == then_idx;
    let Some(base_threshold) = extract_descending_base_threshold(
        &function.blocks[entry_idx],
        &condition_value,
        &recursive_param_value,
        recurse_on_then,
    ) else {
        return;
    };

    let pre_call = &recurse_block.instructions[..call_idx];
    if !pre_call.iter().all(|inst| match inst {
        MirInst::Const { .. } | MirInst::Unary { .. } | MirInst::Binary { .. } | MirInst::Nop => {
            true
        }
        MirInst::Call {
            callee: MirCallee::Local(name),
            ..
        } => name != &function.name,
        MirInst::Call { .. } => true,
        _ => false,
    }) {
        return;
    }
    let mut step_consts = int_const_map_from_insts(&function.blocks[entry_idx].instructions);
    step_consts.extend(int_const_map_from_insts(pre_call));
    let Some(step_amount) =
        extract_descending_step(pre_call, &call_arg, &recursive_param_value, &step_consts)
    else {
        return;
    };
    if recurse_block.instructions[constructor_idx + 1..]
        .iter()
        .any(|inst| !matches!(inst, MirInst::Nop))
    {
        return;
    }

    let base_block = &function.blocks[base_idx];
    let base_instructions = &base_block.instructions;
    if !base_instructions.iter().all(|inst| {
        matches!(
            inst,
            MirInst::Const { .. }
                | MirInst::Unary { .. }
                | MirInst::Binary { .. }
                | MirInst::SumInit { .. }
                | MirInst::Nop
        )
    }) {
        return;
    }

    let mut next_value_id = next_fresh_value_id(function);
    let loop_i = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);
    let loop_acc = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);

    let entry_id = function.entry.clone();
    let loop_id = MirBlockId(entry_id.0.saturating_add(1));
    let step_id = MirBlockId(entry_id.0.saturating_add(2));
    let done_id = MirBlockId(entry_id.0.saturating_add(3));

    let mut entry_remap = BTreeMap::new();
    entry_remap.insert(MirValueId(0), MirValueId(0));
    let mut entry_new_insts =
        clone_insts_with_remap(base_instructions, &mut entry_remap, &mut next_value_id);
    let Some(base_value_new) = remap_value(&entry_remap, &base_value) else {
        return;
    };
    let step_value = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);
    entry_new_insts.push(MirInst::Const {
        dest: step_value.clone(),
        literal: MirLiteral::Int(step_amount),
    });
    let base_start_value = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);
    let Some(loop_start_literal) = base_threshold.checked_add(1) else {
        return;
    };
    entry_new_insts.push(MirInst::Const {
        dest: base_start_value.clone(),
        literal: MirLiteral::Int(loop_start_literal),
    });
    let diff_value = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);
    entry_new_insts.push(MirInst::Binary {
        dest: diff_value.clone(),
        op: MirBinaryOp::Sub,
        left: recursive_param_value.clone(),
        right: base_start_value.clone(),
    });
    let remainder_value = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);
    entry_new_insts.push(MirInst::Binary {
        dest: remainder_value.clone(),
        op: MirBinaryOp::Mod,
        left: diff_value.clone(),
        right: step_value.clone(),
    });
    let normalized_remainder_seed = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);
    entry_new_insts.push(MirInst::Binary {
        dest: normalized_remainder_seed.clone(),
        op: MirBinaryOp::Add,
        left: remainder_value.clone(),
        right: step_value.clone(),
    });
    let normalized_remainder = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);
    entry_new_insts.push(MirInst::Binary {
        dest: normalized_remainder.clone(),
        op: MirBinaryOp::Mod,
        left: normalized_remainder_seed,
        right: step_value.clone(),
    });
    let loop_start_value = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);
    entry_new_insts.push(MirInst::Binary {
        dest: loop_start_value.clone(),
        op: MirBinaryOp::Add,
        left: base_start_value,
        right: normalized_remainder,
    });
    entry_new_insts.retain(|inst| !matches!(inst, MirInst::Nop));

    let loop_condition = MirValueId(next_value_id);
    next_value_id = next_value_id.saturating_add(1);
    let loop_new_insts = vec![MirInst::Binary {
        dest: loop_condition.clone(),
        op: MirBinaryOp::Gt,
        left: loop_i.clone(),
        right: recursive_param_value.clone(),
    }];

    let mut step_context_remap = BTreeMap::new();
    step_context_remap.insert(recursive_param_value.clone(), loop_i.clone());
    for passthrough_param in 0..function_arity {
        let param_id = MirValueId(passthrough_param as u32);
        if param_id != recursive_param_value {
            step_context_remap.insert(param_id.clone(), param_id);
        }
    }
    let mut step_context_insts =
        clone_insts_with_remap(pre_call, &mut step_context_remap, &mut next_value_id);
    step_context_insts.retain(|inst| !matches!(inst, MirInst::Nop));

    let recursive_sum = match constructor {
        RecurseConstructorPattern::Sum {
            sum_type,
            variant,
            tag,
            fields,
        } => {
            let mut new_fields = Vec::with_capacity(fields.len());
            for field in fields {
                if field == *call_result {
                    new_fields.push(loop_acc.clone());
                } else if let Some(remapped_field) = step_context_remap.get(&field) {
                    new_fields.push(remapped_field.clone());
                } else {
                    return;
                }
            }
            MirInst::SumInit {
                dest: MirValueId(next_value_id),
                sum_type: sum_type.clone(),
                variant: variant.clone(),
                tag,
                fields: new_fields,
            }
        }
    };
    let next_acc_value = match &recursive_sum {
        MirInst::SumInit { dest, .. } => dest.clone(),
        _ => return,
    };
    next_value_id = next_value_id.saturating_add(1);
    let next_i_value = MirValueId(next_value_id);
    let mut step_new_insts = step_context_insts;
    step_new_insts.push(recursive_sum);
    step_new_insts.push(MirInst::Binary {
        dest: next_i_value.clone(),
        op: MirBinaryOp::Add,
        left: loop_i.clone(),
        right: step_value.clone(),
    });

    function.blocks = vec![
        MirBlock {
            id: entry_id,
            params: vec![],
            instructions: entry_new_insts,
            terminator: MirTerminator::Jump {
                target: loop_id.clone(),
                args: vec![loop_start_value.clone(), base_value_new],
            },
        },
        MirBlock {
            id: loop_id.clone(),
            params: vec![
                MirBlockParam {
                    id: loop_i.clone(),
                    ty: Type::Int,
                },
                MirBlockParam {
                    id: loop_acc.clone(),
                    ty: function.signature.ret.clone(),
                },
            ],
            instructions: loop_new_insts,
            terminator: MirTerminator::Branch {
                condition: loop_condition,
                then_block: done_id.clone(),
                else_block: step_id.clone(),
            },
        },
        MirBlock {
            id: step_id,
            params: vec![],
            instructions: step_new_insts,
            terminator: MirTerminator::Jump {
                target: loop_id.clone(),
                args: vec![next_i_value, next_acc_value],
            },
        },
        MirBlock {
            id: done_id,
            params: vec![],
            instructions: vec![MirInst::Nop],
            terminator: MirTerminator::Return {
                value: Some(loop_acc),
            },
        },
    ];
}

fn extract_descending_base_threshold(
    entry_block: &MirBlock,
    condition_value: &MirValueId,
    param_value: &MirValueId,
    recurse_on_then: bool,
) -> Option<i64> {
    let int_consts = int_const_map_from_insts(&entry_block.instructions);

    for inst in &entry_block.instructions {
        let MirInst::Binary {
            dest,
            op,
            left,
            right,
        } = inst
        else {
            continue;
        };
        if dest != condition_value {
            continue;
        }
        let base_threshold = if recurse_on_then {
            match op {
                MirBinaryOp::Gt if left == param_value => int_consts.get(right).copied(),
                MirBinaryOp::Gte if left == param_value => int_consts
                    .get(right)
                    .copied()
                    .and_then(|v| v.checked_sub(1)),
                MirBinaryOp::Lt if right == param_value => int_consts.get(left).copied(),
                MirBinaryOp::Lte if right == param_value => {
                    int_consts.get(left).copied().and_then(|v| v.checked_sub(1))
                }
                _ => None,
            }
        } else {
            match op {
                MirBinaryOp::Lte if left == param_value => int_consts.get(right).copied(),
                MirBinaryOp::Lt if left == param_value => int_consts
                    .get(right)
                    .copied()
                    .and_then(|v| v.checked_sub(1)),
                MirBinaryOp::Gte if right == param_value => int_consts.get(left).copied(),
                MirBinaryOp::Gt if right == param_value => {
                    int_consts.get(left).copied().and_then(|v| v.checked_sub(1))
                }
                _ => None,
            }
        };
        if let Some(threshold) = base_threshold {
            return Some(threshold);
        }
    }

    None
}

fn int_const_map_from_insts(insts: &[MirInst]) -> BTreeMap<MirValueId, i64> {
    let mut int_consts = BTreeMap::new();
    for inst in insts {
        match inst {
            MirInst::Const {
                dest,
                literal: MirLiteral::Int(value),
            } => {
                int_consts.insert(dest.clone(), *value);
            }
            MirInst::Unary {
                dest,
                op: MirUnaryOp::Neg,
                operand,
            } => {
                if let Some(value) = int_consts.get(operand).copied()
                    && let Some(negated) = value.checked_neg()
                {
                    int_consts.insert(dest.clone(), negated);
                }
            }
            MirInst::Binary {
                dest,
                op,
                left,
                right,
            } => {
                let Some(left_value) = int_consts.get(left).copied() else {
                    continue;
                };
                let Some(right_value) = int_consts.get(right).copied() else {
                    continue;
                };
                let folded = match op {
                    MirBinaryOp::Add => left_value.checked_add(right_value),
                    MirBinaryOp::Sub => left_value.checked_sub(right_value),
                    MirBinaryOp::Mul => left_value.checked_mul(right_value),
                    _ => None,
                };
                if let Some(value) = folded {
                    int_consts.insert(dest.clone(), value);
                }
            }
            _ => {}
        }
    }
    int_consts
}

fn block_has_recursive_self_call(block: &MirBlock, function_name: &str) -> bool {
    block.instructions.iter().any(|inst| {
        matches!(
            inst,
            MirInst::Call {
                callee: MirCallee::Local(name),
                ..
            } if name == function_name
        )
    })
}

enum RecurseConstructorPattern {
    Sum {
        sum_type: String,
        variant: String,
        tag: u32,
        fields: Vec<MirValueId>,
    },
}

fn find_recursive_constructor_pattern<'a>(
    block: &'a MirBlock,
    function_name: &str,
    recurse_block_value: &MirValueId,
    function_arity: usize,
) -> Option<(
    usize,
    &'a MirValueId,
    MirValueId,
    usize,
    MirValueId,
    usize,
    RecurseConstructorPattern,
)> {
    for (idx, inst) in block.instructions.iter().enumerate() {
        let MirInst::Call {
            callee: MirCallee::Local(name),
            args,
            result: Some(call_result),
            ..
        } = inst
        else {
            continue;
        };
        if name != function_name || args.len() != function_arity {
            continue;
        }
        let mut recursive_param_idx = None;
        let mut passthrough_ok = true;
        for (arg_idx, arg) in args.iter().enumerate() {
            let param_id = MirValueId(arg_idx as u32);
            if *arg == param_id {
                continue;
            }
            if recursive_param_idx.is_some() {
                passthrough_ok = false;
                break;
            }
            recursive_param_idx = Some(arg_idx);
        }
        let Some(recursive_param_idx) = recursive_param_idx else {
            continue;
        };
        if !passthrough_ok {
            continue;
        }
        let recursive_param_value = MirValueId(recursive_param_idx as u32);
        let call_arg = args[recursive_param_idx].clone();
        for (next_idx, next_inst) in block.instructions.iter().enumerate().skip(idx + 1) {
            if let MirInst::SumInit {
                dest,
                sum_type,
                variant,
                tag,
                fields,
            } = next_inst
                && dest == recurse_block_value
                && fields.iter().any(|field| field == call_result)
            {
                return Some((
                    idx,
                    call_result,
                    call_arg,
                    recursive_param_idx,
                    recursive_param_value,
                    next_idx,
                    RecurseConstructorPattern::Sum {
                        sum_type: sum_type.clone(),
                        variant: variant.clone(),
                        tag: *tag,
                        fields: fields.clone(),
                    },
                ));
            }
        }
    }
    None
}

fn extract_descending_step(
    pre_call: &[MirInst],
    call_arg: &MirValueId,
    param_value: &MirValueId,
    int_consts: &BTreeMap<MirValueId, i64>,
) -> Option<i64> {
    pre_call.iter().find_map(|inst| {
        let MirInst::Binary {
            dest,
            op,
            left,
            right,
        } = inst
        else {
            return None;
        };
        if dest != call_arg {
            return None;
        }

        match op {
            MirBinaryOp::Sub if left == param_value => {
                let step = int_consts.get(right).copied()?;
                (step > 0).then_some(step)
            }
            MirBinaryOp::Add => {
                if left == param_value {
                    let delta = int_consts.get(right).copied()?;
                    delta.checked_neg().filter(|step| *step > 0)
                } else if right == param_value {
                    let delta = int_consts.get(left).copied()?;
                    delta.checked_neg().filter(|step| *step > 0)
                } else {
                    None
                }
            }
            _ => None,
        }
    })
}

fn remap_value(remap: &BTreeMap<MirValueId, MirValueId>, value: &MirValueId) -> Option<MirValueId> {
    remap.get(value).cloned().or_else(|| Some(value.clone()))
}

fn clone_insts_with_remap(
    insts: &[MirInst],
    remap: &mut BTreeMap<MirValueId, MirValueId>,
    next_value_id: &mut u32,
) -> Vec<MirInst> {
    let mut out = Vec::with_capacity(insts.len());
    for inst in insts {
        let cloned = match inst {
            MirInst::Const { dest, literal } => {
                let new_dest = MirValueId(*next_value_id);
                *next_value_id = next_value_id.saturating_add(1);
                remap.insert(dest.clone(), new_dest.clone());
                MirInst::Const {
                    dest: new_dest,
                    literal: literal.clone(),
                }
            }
            MirInst::Binary {
                dest,
                op,
                left,
                right,
            } => {
                let new_dest = MirValueId(*next_value_id);
                *next_value_id = next_value_id.saturating_add(1);
                remap.insert(dest.clone(), new_dest.clone());
                MirInst::Binary {
                    dest: new_dest,
                    op: *op,
                    left: remap_value(remap, left).unwrap_or_else(|| left.clone()),
                    right: remap_value(remap, right).unwrap_or_else(|| right.clone()),
                }
            }
            MirInst::Unary { dest, op, operand } => {
                let new_dest = MirValueId(*next_value_id);
                *next_value_id = next_value_id.saturating_add(1);
                remap.insert(dest.clone(), new_dest.clone());
                MirInst::Unary {
                    dest: new_dest,
                    op: *op,
                    operand: remap_value(remap, operand).unwrap_or_else(|| operand.clone()),
                }
            }
            MirInst::SumInit {
                dest,
                sum_type,
                variant,
                tag,
                fields,
            } => {
                let new_dest = MirValueId(*next_value_id);
                *next_value_id = next_value_id.saturating_add(1);
                remap.insert(dest.clone(), new_dest.clone());
                MirInst::SumInit {
                    dest: new_dest,
                    sum_type: sum_type.clone(),
                    variant: variant.clone(),
                    tag: *tag,
                    fields: fields
                        .iter()
                        .map(|field| remap_value(remap, field).unwrap_or_else(|| field.clone()))
                        .collect(),
                }
            }
            MirInst::Call {
                callee,
                args,
                arg_types,
                result,
                ret_type,
                callee_fail_result_abi,
                capture_fail_result,
                cc_manifest_id,
            } => {
                let new_callee = match callee {
                    MirCallee::Value(value) => {
                        MirCallee::Value(remap_value(remap, value).unwrap_or_else(|| value.clone()))
                    }
                    MirCallee::Local(name) => MirCallee::Local(name.clone()),
                    MirCallee::External(name) => MirCallee::External(name.clone()),
                };
                let new_result = result.as_ref().map(|dest| {
                    let new_dest = MirValueId(*next_value_id);
                    *next_value_id = next_value_id.saturating_add(1);
                    remap.insert(dest.clone(), new_dest.clone());
                    new_dest
                });
                MirInst::Call {
                    callee: new_callee,
                    args: args
                        .iter()
                        .map(|arg| remap_value(remap, arg).unwrap_or_else(|| arg.clone()))
                        .collect(),
                    arg_types: arg_types.clone(),
                    result: new_result,
                    ret_type: ret_type.clone(),
                    callee_fail_result_abi: *callee_fail_result_abi,
                    capture_fail_result: *capture_fail_result,
                    cc_manifest_id: cc_manifest_id.clone(),
                }
            }
            MirInst::Nop => MirInst::Nop,
            _ => return Vec::new(),
        };
        out.push(cloned);
    }
    out
}

fn collect_const_field_exprs(module: &HirModule) -> BTreeMap<String, AstExprKind> {
    let mut exprs = BTreeMap::new();
    for decl in &module.declarations {
        let HirDecl::Raw(DeclKind::RecordDef(record)) = decl else {
            continue;
        };
        for const_field in &record.const_fields {
            exprs.insert(
                format!("{}.{}", record.name.node, const_field.name.node),
                const_field.value.node.clone(),
            );
        }
    }
    exprs
}

fn schedule_trailing_releases_after_last_use(function: &mut MirFunction) {
    for block in &mut function.blocks {
        let Some(last_non_release) = block
            .instructions
            .iter()
            .rposition(|inst| !matches!(inst, MirInst::Release { .. }))
        else {
            continue;
        };
        let tail_start = last_non_release + 1;
        if tail_start >= block.instructions.len() {
            continue;
        }

        let prefix = block.instructions[..tail_start].to_vec();
        let tail_releases = block.instructions[tail_start..]
            .iter()
            .filter_map(|inst| match inst {
                MirInst::Release { value } => Some(value.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        if tail_releases.is_empty() {
            continue;
        }

        let mut insertions: BTreeMap<usize, Vec<MirInst>> = BTreeMap::new();
        for value in tail_releases {
            let release_pos =
                compute_release_insertion_pos(&value, &block.params, &prefix, &block.terminator);
            insertions
                .entry(release_pos)
                .or_default()
                .push(MirInst::Release { value });
        }

        let mut rebuilt = Vec::with_capacity(block.instructions.len());
        for pos in 0..=prefix.len() {
            if let Some(releases) = insertions.remove(&pos) {
                rebuilt.extend(releases);
            }
            if let Some(inst) = prefix.get(pos) {
                rebuilt.push(inst.clone());
            }
        }
        block.instructions = rebuilt;
    }
}

fn elide_adjacent_retain_release_pairs(function: &mut MirFunction) {
    for block in &mut function.blocks {
        let mut instructions = block.instructions.clone();
        loop {
            let mut changed = false;
            let mut idx = 0usize;
            while idx < instructions.len() {
                let Some(retained) = (match &instructions[idx] {
                    MirInst::Retain { value } => Some(value.clone()),
                    _ => None,
                }) else {
                    idx += 1;
                    continue;
                };

                let mut probe = idx + 1;
                let mut release_idx = None;
                while probe < instructions.len() {
                    let inst = &instructions[probe];
                    if let MirInst::Release { value } = inst
                        && value == &retained
                    {
                        release_idx = Some(probe);
                        break;
                    }
                    if inst_reads_value(inst, &retained)
                        || inst_defined_value(inst).is_some_and(|dest| dest == &retained)
                    {
                        break;
                    }
                    probe += 1;
                }

                if let Some(release_idx) = release_idx {
                    instructions.remove(release_idx);
                    instructions.remove(idx);
                    changed = true;
                    continue;
                }
                idx += 1;
            }
            if !changed {
                break;
            }
        }
        block.instructions = instructions;
    }
}

fn fuse_release_alloc_same_layout(function: &mut MirFunction, layouts: &MirLayoutCatalog) {
    let layout_keys = infer_heap_layout_keys(function);
    for block in &mut function.blocks {
        let mut instructions = Vec::with_capacity(block.instructions.len());
        let mut idx = 0usize;
        while idx < block.instructions.len() {
            let released_value = match &block.instructions[idx] {
                MirInst::Release { value } => value.clone(),
                _ => {
                    instructions.push(block.instructions[idx].clone());
                    idx += 1;
                    continue;
                }
            };

            let Some((probe, candidate)) =
                find_reuse_probe(block, idx, &released_value, layouts, &layout_keys)
            else {
                instructions.push(block.instructions[idx].clone());
                idx += 1;
                continue;
            };

            for inst in &block.instructions[idx + 1..probe] {
                instructions.push(inst.clone());
            }
            match candidate {
                ReuseInitCandidate::Record {
                    dest,
                    record_type,
                    fields,
                } => instructions.push(MirInst::RecordInitReuse {
                    dest,
                    source: released_value.clone(),
                    record_type,
                    fields,
                }),
                ReuseInitCandidate::Sum {
                    dest,
                    sum_type,
                    variant,
                    tag,
                    fields,
                } => instructions.push(MirInst::SumInitReuse {
                    dest,
                    source: released_value.clone(),
                    sum_type,
                    variant,
                    tag,
                    fields,
                }),
            }
            idx = probe + 1;
        }
        block.instructions = instructions;
    }
}

#[derive(Debug, Clone)]
struct CrossBlockReuseRewrite {
    release_sites: Vec<CrossBlockReleaseSite>,
    succ_block_idx: usize,
    succ_inst_idx: usize,
    source_param: MirValueId,
    candidate: ReuseInitCandidate,
}

#[derive(Debug, Clone)]
struct CrossBlockReleaseSite {
    pred_block_idx: usize,
    release_inst_idx: usize,
}

fn fuse_release_alloc_cross_block_jump(function: &mut MirFunction, layouts: &MirLayoutCatalog) {
    let layout_keys = infer_heap_layout_keys(function);
    let block_index_by_id = function
        .blocks
        .iter()
        .enumerate()
        .map(|(idx, block)| (block.id.clone(), idx))
        .collect::<BTreeMap<_, _>>();

    let mut predecessors = BTreeMap::<MirBlockId, Vec<usize>>::new();
    for (block_idx, block) in function.blocks.iter().enumerate() {
        if let MirTerminator::Jump { target, .. } = &block.terminator {
            predecessors
                .entry(target.clone())
                .or_default()
                .push(block_idx);
        }
    }

    let mut rewrites = Vec::new();
    for (target, pred_block_indices) in predecessors {
        let Some(succ_block_idx) = block_index_by_id.get(&target).copied() else {
            continue;
        };
        if pred_block_indices.is_empty() {
            continue;
        }
        if pred_block_indices.contains(&succ_block_idx) {
            continue;
        }
        let successor = &function.blocks[succ_block_idx];
        for (arg_pos, param) in successor.params.iter().enumerate() {
            let source_param = param.id.clone();
            let Some((succ_inst_idx, candidate)) =
                find_reuse_candidate_in_block(successor, &source_param, layouts, &layout_keys)
            else {
                continue;
            };

            let mut release_sites = Vec::new();
            let mut all_predecessors_match = true;
            for pred_block_idx in &pred_block_indices {
                let pred_block = &function.blocks[*pred_block_idx];
                let Some(release_inst_idx) = find_trailing_release_idx(pred_block) else {
                    all_predecessors_match = false;
                    break;
                };
                let released_value = match &pred_block.instructions[release_inst_idx] {
                    MirInst::Release { value } => value.clone(),
                    _ => {
                        all_predecessors_match = false;
                        break;
                    }
                };
                let MirTerminator::Jump { args, .. } = &pred_block.terminator else {
                    all_predecessors_match = false;
                    break;
                };
                let Some(incoming_value) = args.get(arg_pos) else {
                    all_predecessors_match = false;
                    break;
                };
                if *incoming_value != released_value {
                    all_predecessors_match = false;
                    break;
                }
                release_sites.push(CrossBlockReleaseSite {
                    pred_block_idx: *pred_block_idx,
                    release_inst_idx,
                });
            }
            if !all_predecessors_match {
                continue;
            }

            rewrites.push(CrossBlockReuseRewrite {
                release_sites,
                succ_block_idx,
                succ_inst_idx,
                source_param,
                candidate,
            });
            break;
        }
    }

    for rewrite in rewrites {
        for release_site in rewrite.release_sites {
            function.blocks[release_site.pred_block_idx]
                .instructions
                .remove(release_site.release_inst_idx);
        }
        let replacement = match rewrite.candidate {
            ReuseInitCandidate::Record {
                dest,
                record_type,
                fields,
            } => MirInst::RecordInitReuse {
                dest,
                source: rewrite.source_param,
                record_type,
                fields,
            },
            ReuseInitCandidate::Sum {
                dest,
                sum_type,
                variant,
                tag,
                fields,
            } => MirInst::SumInitReuse {
                dest,
                source: rewrite.source_param,
                sum_type,
                variant,
                tag,
                fields,
            },
        };
        function.blocks[rewrite.succ_block_idx].instructions[rewrite.succ_inst_idx] = replacement;
    }
}

#[derive(Debug, Clone)]
struct TokenFlowRewrite {
    target_block_idx: usize,
    target_inst_idx: usize,
    token_param: MirBlockParam,
    candidate: ReuseInitCandidate,
    pred_actions: Vec<TokenFlowPredAction>,
}

#[derive(Debug, Clone)]
struct TokenFlowPredAction {
    pred_block_idx: usize,
    token_value: MirValueId,
    kind: TokenFlowPredActionKind,
}

#[derive(Debug, Clone)]
enum TokenFlowPredActionKind {
    TokenizeRelease {
        release_inst_idx: usize,
        source: MirValueId,
    },
    PassNullToken,
}

fn emit_reuse_tokens_for_mixed_predecessor_joins(
    function: &mut MirFunction,
    layouts: &MirLayoutCatalog,
) {
    let layout_keys = infer_heap_layout_keys(function);
    let block_index_by_id = function
        .blocks
        .iter()
        .enumerate()
        .map(|(idx, block)| (block.id.clone(), idx))
        .collect::<BTreeMap<_, _>>();

    let mut predecessors = BTreeMap::<MirBlockId, Vec<usize>>::new();
    for (block_idx, block) in function.blocks.iter().enumerate() {
        if let MirTerminator::Jump { target, .. } = &block.terminator {
            predecessors
                .entry(target.clone())
                .or_default()
                .push(block_idx);
        }
    }

    let mut rewrites = Vec::new();
    let mut next_value_id = next_fresh_value_id(function);
    for (target, pred_block_indices) in predecessors {
        if pred_block_indices.len() < 2 {
            continue;
        }
        let Some(target_block_idx) = block_index_by_id.get(&target).copied() else {
            continue;
        };
        let target_block = &function.blocks[target_block_idx];
        for (arg_pos, param) in target_block.params.iter().enumerate() {
            let Some((target_inst_idx, candidate)) =
                find_reuse_candidate_in_block(target_block, &param.id, layouts, &layout_keys)
            else {
                continue;
            };

            let mut pred_actions = Vec::with_capacity(pred_block_indices.len());
            let mut saw_tokenized_release = false;
            let mut saw_null_token = false;
            let mut all_predecessors_compatible = true;
            for pred_block_idx in &pred_block_indices {
                let pred_block = &function.blocks[*pred_block_idx];
                let MirTerminator::Jump { args, .. } = &pred_block.terminator else {
                    all_predecessors_compatible = false;
                    break;
                };
                let Some(incoming_value) = args.get(arg_pos).cloned() else {
                    all_predecessors_compatible = false;
                    break;
                };

                let token_value = MirValueId(next_value_id);
                next_value_id = next_value_id.saturating_add(1);
                if let Some(release_inst_idx) =
                    find_release_idx_for_value(pred_block, &incoming_value)
                {
                    saw_tokenized_release = true;
                    pred_actions.push(TokenFlowPredAction {
                        pred_block_idx: *pred_block_idx,
                        token_value,
                        kind: TokenFlowPredActionKind::TokenizeRelease {
                            release_inst_idx,
                            source: incoming_value,
                        },
                    });
                    continue;
                }

                saw_null_token = true;
                pred_actions.push(TokenFlowPredAction {
                    pred_block_idx: *pred_block_idx,
                    token_value,
                    kind: TokenFlowPredActionKind::PassNullToken,
                });
            }
            if !all_predecessors_compatible || !saw_tokenized_release || !saw_null_token {
                continue;
            }

            rewrites.push(TokenFlowRewrite {
                target_block_idx,
                target_inst_idx,
                token_param: MirBlockParam {
                    id: MirValueId(next_value_id),
                    ty: Type::Dynamic,
                },
                candidate,
                pred_actions,
            });
            next_value_id = next_value_id.saturating_add(1);
            break;
        }
    }

    for rewrite in rewrites {
        for pred_action in &rewrite.pred_actions {
            let pred_block = &mut function.blocks[pred_action.pred_block_idx];
            match pred_action.kind {
                TokenFlowPredActionKind::TokenizeRelease {
                    release_inst_idx,
                    ref source,
                } => {
                    pred_block.instructions[release_inst_idx] = MirInst::ReuseToken {
                        dest: pred_action.token_value.clone(),
                        source: source.clone(),
                    };
                }
                TokenFlowPredActionKind::PassNullToken => {
                    pred_block.instructions.push(MirInst::Const {
                        dest: pred_action.token_value.clone(),
                        literal: MirLiteral::Int(0),
                    });
                }
            }
            if let MirTerminator::Jump { args, .. } = &mut pred_block.terminator {
                args.push(pred_action.token_value.clone());
            }
        }

        let target_block = &mut function.blocks[rewrite.target_block_idx];
        target_block.params.push(rewrite.token_param.clone());
        let replacement = match rewrite.candidate {
            ReuseInitCandidate::Record {
                dest,
                record_type,
                fields,
            } => MirInst::RecordInitFromToken {
                dest,
                token: rewrite.token_param.id,
                record_type,
                fields,
            },
            ReuseInitCandidate::Sum {
                dest,
                sum_type,
                variant,
                tag,
                fields,
            } => MirInst::SumInitFromToken {
                dest,
                token: rewrite.token_param.id,
                sum_type,
                variant,
                tag,
                fields,
            },
        };
        target_block.instructions[rewrite.target_inst_idx] = replacement;
    }
}

fn emit_reuse_tokens_for_loop_backedge_joins(
    function: &mut MirFunction,
    layouts: &MirLayoutCatalog,
) {
    let layout_keys = infer_heap_layout_keys(function);
    let block_index_by_id = function
        .blocks
        .iter()
        .enumerate()
        .map(|(idx, block)| (block.id.clone(), idx))
        .collect::<BTreeMap<_, _>>();

    let mut predecessors = BTreeMap::<MirBlockId, Vec<usize>>::new();
    for (block_idx, block) in function.blocks.iter().enumerate() {
        if let MirTerminator::Jump { target, .. } = &block.terminator {
            predecessors
                .entry(target.clone())
                .or_default()
                .push(block_idx);
        }
    }

    let mut rewrites = Vec::new();
    let mut next_value_id = next_fresh_value_id(function);
    for (target, pred_block_indices) in predecessors {
        let Some(target_block_idx) = block_index_by_id.get(&target).copied() else {
            continue;
        };
        if target == function.entry {
            continue;
        }
        if !pred_block_indices.contains(&target_block_idx) {
            continue;
        }

        let target_block = &function.blocks[target_block_idx];
        for (arg_pos, param) in target_block.params.iter().enumerate() {
            let Some((target_inst_idx, candidate)) =
                find_reuse_candidate_in_block(target_block, &param.id, layouts, &layout_keys)
            else {
                continue;
            };

            let mut pred_actions = Vec::with_capacity(pred_block_indices.len());
            let mut all_predecessors_tokenize = true;
            for pred_block_idx in &pred_block_indices {
                let pred_block = &function.blocks[*pred_block_idx];
                let MirTerminator::Jump { args, .. } = &pred_block.terminator else {
                    all_predecessors_tokenize = false;
                    break;
                };
                let Some(incoming_value) = args.get(arg_pos).cloned() else {
                    all_predecessors_tokenize = false;
                    break;
                };
                let Some(release_inst_idx) =
                    find_release_idx_for_value(pred_block, &incoming_value)
                else {
                    all_predecessors_tokenize = false;
                    break;
                };

                let token_value = MirValueId(next_value_id);
                next_value_id = next_value_id.saturating_add(1);
                pred_actions.push(TokenFlowPredAction {
                    pred_block_idx: *pred_block_idx,
                    token_value,
                    kind: TokenFlowPredActionKind::TokenizeRelease {
                        release_inst_idx,
                        source: incoming_value,
                    },
                });
            }
            if !all_predecessors_tokenize || pred_actions.is_empty() {
                continue;
            }

            rewrites.push(TokenFlowRewrite {
                target_block_idx,
                target_inst_idx,
                token_param: MirBlockParam {
                    id: MirValueId(next_value_id),
                    ty: Type::Dynamic,
                },
                candidate,
                pred_actions,
            });
            next_value_id = next_value_id.saturating_add(1);
            break;
        }
    }

    for rewrite in rewrites {
        for pred_action in &rewrite.pred_actions {
            let pred_block = &mut function.blocks[pred_action.pred_block_idx];
            let TokenFlowPredActionKind::TokenizeRelease {
                release_inst_idx,
                ref source,
            } = pred_action.kind
            else {
                continue;
            };
            pred_block.instructions[release_inst_idx] = MirInst::ReuseToken {
                dest: pred_action.token_value.clone(),
                source: source.clone(),
            };
            if let MirTerminator::Jump { args, .. } = &mut pred_block.terminator {
                args.push(pred_action.token_value.clone());
            }
        }

        let target_block = &mut function.blocks[rewrite.target_block_idx];
        target_block.params.push(rewrite.token_param.clone());
        let replacement = match rewrite.candidate {
            ReuseInitCandidate::Record {
                dest,
                record_type,
                fields,
            } => MirInst::RecordInitFromToken {
                dest,
                token: rewrite.token_param.id,
                record_type,
                fields,
            },
            ReuseInitCandidate::Sum {
                dest,
                sum_type,
                variant,
                tag,
                fields,
            } => MirInst::SumInitFromToken {
                dest,
                token: rewrite.token_param.id,
                sum_type,
                variant,
                tag,
                fields,
            },
        };
        target_block.instructions[rewrite.target_inst_idx] = replacement;
    }
}

fn emit_reuse_tokens_for_trailing_release_alloc(
    function: &mut MirFunction,
    layouts: &MirLayoutCatalog,
) {
    let layout_keys = infer_heap_layout_keys(function);
    let mut next_value_id = next_fresh_value_id(function);

    for block in &mut function.blocks {
        let Some(release_idx) = find_trailing_release_idx(block) else {
            continue;
        };
        let MirInst::Release {
            value: released_value,
        } = &block.instructions[release_idx]
        else {
            continue;
        };
        let released_value = released_value.clone();
        let Some(release_layout) = layout_keys.get(&released_value) else {
            continue;
        };

        let mut chosen: Option<ReuseProbe> = None;
        for idx in 0..release_idx {
            let candidate = match &block.instructions[idx] {
                MirInst::RecordInit {
                    dest,
                    record_type,
                    fields,
                } => {
                    if dest == &released_value {
                        None
                    } else {
                    let alloc_layout = format!("record:{record_type}");
                    let layout_matches = alloc_layout == *release_layout;
                    let layout_is_reusable = record_layout_is_reuse_eligible(layouts, record_type);
                    let source_mentioned_in_fields = fields
                        .iter()
                        .any(|(_, field_value)| field_value == &released_value);
                    if layout_matches && layout_is_reusable && !source_mentioned_in_fields {
                        Some(ReuseInitCandidate::Record {
                            dest: dest.clone(),
                            record_type: record_type.clone(),
                            fields: fields.clone(),
                        })
                    } else {
                        None
                    }
                    }
                }
                MirInst::SumInit {
                    dest,
                    sum_type,
                    variant,
                    tag,
                    fields,
                } => {
                    if dest == &released_value {
                        None
                    } else {
                    let alloc_layout = format!("sum:{sum_type}");
                    let layout_matches = alloc_layout == *release_layout;
                    let layout_is_reusable = sum_layout_is_reuse_eligible(layouts, sum_type);
                    let source_mentioned_in_fields =
                        fields.iter().any(|field| field == &released_value);
                    if layout_matches && layout_is_reusable && !source_mentioned_in_fields {
                        Some(ReuseInitCandidate::Sum {
                            dest: dest.clone(),
                            sum_type: sum_type.clone(),
                            variant: variant.clone(),
                            tag: *tag,
                            fields: fields.clone(),
                        })
                    } else {
                        None
                    }
                    }
                }
                _ => None,
            };
            let Some(candidate) = candidate else {
                continue;
            };

            let mut blocked = false;
            for probe in idx + 1..release_idx {
                let probe_inst = &block.instructions[probe];
                if inst_reads_value(probe_inst, &released_value)
                    || inst_defined_value(probe_inst).is_some_and(|dest| dest == &released_value)
                    || probe_inst.is_memory_op()
                {
                    blocked = true;
                    break;
                }
            }
            if blocked {
                continue;
            }
            chosen = Some((idx, candidate));
            break;
        }

        let Some((candidate_idx, candidate)) = chosen else {
            continue;
        };

        let token_value = MirValueId(next_value_id);
        next_value_id = next_value_id.saturating_add(1);

        let mut rewritten = Vec::with_capacity(block.instructions.len() + 1);
        for (idx, inst) in block.instructions.iter().enumerate() {
            if idx == release_idx {
                continue;
            }
            if idx == candidate_idx {
                rewritten.push(MirInst::ReuseToken {
                    dest: token_value.clone(),
                    source: released_value.clone(),
                });
                let tokenized_init = match &candidate {
                    ReuseInitCandidate::Record {
                        dest,
                        record_type,
                        fields,
                    } => MirInst::RecordInitFromToken {
                        dest: dest.clone(),
                        token: token_value.clone(),
                        record_type: record_type.clone(),
                        fields: fields.clone(),
                    },
                    ReuseInitCandidate::Sum {
                        dest,
                        sum_type,
                        variant,
                        tag,
                        fields,
                    } => MirInst::SumInitFromToken {
                        dest: dest.clone(),
                        token: token_value.clone(),
                        sum_type: sum_type.clone(),
                        variant: variant.clone(),
                        tag: *tag,
                        fields: fields.clone(),
                    },
                };
                rewritten.push(tokenized_init);
                continue;
            }
            rewritten.push(inst.clone());
        }
        block.instructions = rewritten;
    }
}

fn next_fresh_value_id(function: &MirFunction) -> u32 {
    let mut max_id = 0u32;
    for (idx, _) in function.signature.params.iter().enumerate() {
        max_id = max_id.max(idx as u32);
    }
    for block in &function.blocks {
        for param in &block.params {
            max_id = max_id.max(param.id.0);
        }
        for inst in &block.instructions {
            if let Some(dest) = inst_defined_value(inst) {
                max_id = max_id.max(dest.0);
            }
            for read in inst_read_values(inst) {
                max_id = max_id.max(read.0);
            }
        }
        if let MirTerminator::Jump { args, .. } = &block.terminator {
            for arg in args {
                max_id = max_id.max(arg.0);
            }
        }
        if let MirTerminator::Branch { condition, .. } = &block.terminator {
            max_id = max_id.max(condition.0);
        }
        if let MirTerminator::Return {
            value: Some(returned),
        } = &block.terminator
        {
            max_id = max_id.max(returned.0);
        }
    }
    max_id.saturating_add(1)
}

fn inst_read_values(inst: &MirInst) -> Vec<MirValueId> {
    match inst {
        MirInst::Const { .. } | MirInst::FunctionRef { .. } | MirInst::HandlerEnter { .. } => {
            Vec::new()
        }
        MirInst::Binary { left, right, .. } => vec![left.clone(), right.clone()],
        MirInst::Unary { operand, .. } => vec![operand.clone()],
        MirInst::RecordInit { fields, .. } => fields.iter().map(|(_, v)| v.clone()).collect(),
        MirInst::RecordInitReuse { source, fields, .. } => {
            let mut reads = vec![source.clone()];
            reads.extend(fields.iter().map(|(_, v)| v.clone()));
            reads
        }
        MirInst::ReuseToken { source, .. } => vec![source.clone()],
        MirInst::RecordInitFromToken { token, fields, .. } => {
            let mut reads = vec![token.clone()];
            reads.extend(fields.iter().map(|(_, v)| v.clone()));
            reads
        }
        MirInst::SumInit { fields, .. } => fields.clone(),
        MirInst::SumInitReuse { source, fields, .. } => {
            let mut reads = vec![source.clone()];
            reads.extend(fields.clone());
            reads
        }
        MirInst::SumInitFromToken { token, fields, .. } => {
            let mut reads = vec![token.clone()];
            reads.extend(fields.clone());
            reads
        }
        MirInst::SumTagLoad { sum, .. } => vec![sum.clone()],
        MirInst::SumPayloadLoad { sum, .. } => vec![sum.clone()],
        MirInst::RecordFieldLoad { record, .. } => vec![record.clone()],
        MirInst::ClosureInit {
            entry, captures, ..
        } => {
            let mut reads = vec![entry.clone()];
            reads.extend(captures.clone());
            reads
        }
        MirInst::ClosureCaptureLoad { closure, .. } => vec![closure.clone()],
        MirInst::StateCellNew { initial, .. } => vec![initial.clone()],
        MirInst::StateCellLoad { cell, .. } => vec![cell.clone()],
        MirInst::StateCellStore { cell, value } => vec![cell.clone(), value.clone()],
        MirInst::Retain { value } | MirInst::Release { value } => vec![value.clone()],
        MirInst::Move { src, .. }
        | MirInst::Borrow { src, .. }
        | MirInst::TryClaim { src, .. }
        | MirInst::Freeze { src, .. } => vec![src.clone()],
        MirInst::CowUpdate {
            target, updates, ..
        } => {
            let mut reads = vec![target.clone()];
            reads.extend(updates.iter().map(|update| update.value.clone()));
            reads
        }
        MirInst::EffectOp { args, .. } => args.clone(),
        MirInst::HandlerExit { .. } => Vec::new(),
        MirInst::Resume { value } => vec![value.clone()],
        MirInst::Call { callee, args, .. } => {
            let mut reads = args.clone();
            if let MirCallee::Value(callee_value) = callee {
                reads.push(callee_value.clone());
            }
            reads
        }
        MirInst::Unsupported { .. } | MirInst::Nop => Vec::new(),
    }
}

fn find_trailing_release_idx(block: &MirBlock) -> Option<usize> {
    for (idx, inst) in block.instructions.iter().enumerate().rev() {
        match inst {
            MirInst::Nop => continue,
            MirInst::Release { .. } => return Some(idx),
            _ => return None,
        }
    }
    None
}

/// Find the index of a `Release { value }` instruction anywhere in a block.
///
/// Unlike `find_trailing_release_idx`, this searches the entire block. Needed
/// because `schedule_trailing_releases_after_last_use` moves releases away from
/// the tail, so the backedge and mixed-predecessor reuse passes must search the
/// whole block rather than only the tail.
/// Returns true when `value` is consumed by the given Call instruction — either as a
/// regular argument or as the callee (closure). In Perceus semantics, both cases
/// transfer ownership: the caller should not retain or release the value afterward.
fn inst_value_consumed_by_call(inst: &MirInst, value: &MirValueId) -> bool {
    match inst {
        MirInst::Call { args, callee, .. } => {
            args.contains(value)
                || matches!(callee, MirCallee::Value(callee_v) if callee_v == value)
        }
        // CowUpdate always manages the lifecycle of its target: the unique path reuses the
        // allocation in place (the result IS the target, so a subsequent Release would free the
        // result), and the copy path releases the original internally during codegen. Either way
        // the target is "consumed" — no additional Release should be inserted by this pass.
        MirInst::CowUpdate { target, .. } => target == value,
        // Sum constructors move their field values into the new heap cell without retaining
        // them — the constructor takes ownership of the fields. A subsequent Release of a
        // field would decrement its RC below the count held by the new cell, causing a
        // use-after-free when the cell is later traversed.
        MirInst::SumInit { fields, .. }
        | MirInst::SumInitReuse { fields, .. }
        | MirInst::SumInitFromToken { fields, .. } => fields.iter().any(|f| f == value),
        // Record constructors (including tuples) similarly move their field values into the
        // newly allocated record without retaining them. Releasing a field after RecordInit
        // would drop the RC to 0 and free memory still referenced by the record's own field
        // slot, causing a use-after-free when the record is later accessed or dropped.
        MirInst::RecordInit { fields, .. }
        | MirInst::RecordInitReuse { fields, .. }
        | MirInst::RecordInitFromToken { fields, .. } => {
            fields.iter().any(|(_, f)| f == value)
        }
        // ClosureInit moves its captures into the closure object (no Retain). A Release of
        // a captured value after ClosureInit would free memory still referenced by the closure.
        MirInst::ClosureInit { captures, .. } => captures.iter().any(|c| c == value),
        _ => false,
    }
}

fn find_release_idx_for_value(block: &MirBlock, value: &MirValueId) -> Option<usize> {
    block.instructions.iter().position(|inst| {
        matches!(inst, MirInst::Release { value: v } if v == value)
    })
}

/// Insert `Release` instructions for heap-managed function parameters that die
/// in a block without being forwarded to a callee or returned.
///
/// Perceus reference counting requires that every heap-managed value is released
/// exactly once on each execution path. The lowering inserts releases for
/// locally-created `let`-bound values via the Block cleanup, but function
/// parameters are in `incoming_scope` and are therefore excluded from that path.
/// This pass fills the gap by inserting releases at the "death boundary" —
/// blocks where the parameter stops being live.
///
/// A block `B` is a death boundary for parameter `v_i` when:
/// Insert `Retain` instructions before call sites where a heap-managed argument
/// is live in at least one successor block (i.e., the caller uses the value again
/// after the call returns).  The corresponding `Release` is inserted in each dead
/// successor so the retained reference is freed on every path where it is not
/// consumed by a later call.
///
/// This implements the caller-side half of Perceus ownership: when a value is
/// passed to a function that takes ownership of its arguments, the caller must
/// retain the value if it continues to use it after the call returns.  Without
/// this pass, a second use of the same value after a callee-side release would
/// be a use-after-free.
fn insert_retains_for_reused_call_args(function: &mut MirFunction, _layouts: &MirLayoutCatalog) {
    let heap_value_layouts = infer_heap_layout_keys(function);
    if heap_value_layouts.is_empty() {
        return;
    }

    // Build successor / predecessor maps.
    let mut successors: BTreeMap<MirBlockId, Vec<MirBlockId>> = function
        .blocks
        .iter()
        .map(|b| (b.id.clone(), Vec::new()))
        .collect();
    for block in &function.blocks {
        match &block.terminator {
            MirTerminator::Jump { target, .. } => {
                successors.entry(block.id.clone()).or_default().push(target.clone());
            }
            MirTerminator::Branch { then_block, else_block, .. } => {
                successors.entry(block.id.clone()).or_default().push(then_block.clone());
                successors.entry(block.id.clone()).or_default().push(else_block.clone());
            }
            _ => {}
        }
    }

    // For each heap-managed value, compute the set of blocks where it is live
    // (directly uses it or can reach a block that does).
    let mut live_sets: BTreeMap<MirValueId, BTreeSet<MirBlockId>> = BTreeMap::new();
    for value_id in heap_value_layouts.keys() {
        let direct_use: BTreeSet<MirBlockId> = function
            .blocks
            .iter()
            .filter(|block| {
                block.instructions.iter().any(|inst| inst_reads_value(inst, value_id))
                    || match &block.terminator {
                        MirTerminator::Jump { args, .. } => args.contains(value_id),
                        MirTerminator::Return { value: Some(v), .. } => v == value_id,
                        MirTerminator::Branch { condition, .. } => condition == value_id,
                        _ => false,
                    }
            })
            .map(|b| b.id.clone())
            .collect();
        let mut live = direct_use;
        let mut changed = true;
        while changed {
            changed = false;
            for block in &function.blocks {
                if live.contains(&block.id) {
                    continue;
                }
                if successors
                    .get(&block.id)
                    .is_some_and(|s| s.iter().any(|sid| live.contains(sid)))
                {
                    live.insert(block.id.clone());
                    changed = true;
                }
            }
        }
        live_sets.insert(value_id.clone(), live);
    }

    // Blocks that receive a value via Jump args (ownership transferred via block param).
    let mut forwarded_to: BTreeMap<MirValueId, BTreeSet<MirBlockId>> = BTreeMap::new();
    for block in &function.blocks {
        if let MirTerminator::Jump { target, args } = &block.terminator {
            for arg in args {
                if heap_value_layouts.contains_key(arg) {
                    forwarded_to.entry(arg.clone()).or_default().insert(target.clone());
                }
            }
        }
    }

    // Collect retains and releases to insert (compute before mutating the function).
    // retain: (block_id, instruction_index_before_which_to_insert, value_id)
    // release: (block_id, value_id) — inserted at block tail
    let mut retains: Vec<(MirBlockId, usize, MirValueId)> = Vec::new();
    let mut releases: BTreeSet<(MirBlockId, MirValueId)> = BTreeSet::new();

    for block in &function.blocks {
        for (inst_idx, inst) in block.instructions.iter().enumerate() {
            // Collect all heap-managed values consumed by this instruction as
            // call arguments, callee value, or closure captures.
            let consumed: Vec<MirValueId> = match inst {
                MirInst::Call { args, callee, .. } => {
                    let mut vals: Vec<MirValueId> = args
                        .iter()
                        .filter(|a| heap_value_layouts.contains_key(*a))
                        .cloned()
                        .collect();
                    if let MirCallee::Value(callee_v) = callee
                        && heap_value_layouts.contains_key(callee_v)
                    {
                        vals.push(callee_v.clone());
                    }
                    vals
                }
                // ClosureInit moves its captures into the closure object. If a
                // captured heap value is also used later (either in subsequent
                // instructions of this block or in a live successor block), we
                // must Retain it before the ClosureInit so the later use is safe.
                MirInst::ClosureInit { captures, .. } => captures
                    .iter()
                    .filter(|c| heap_value_layouts.contains_key(*c))
                    .cloned()
                    .collect(),
                _ => continue,
            };

            // Count occurrences of each heap-managed value in the consumed list.
            // When the same value appears N times as call args, we need N-1 extra
            // Retains to provide the callee with N ownership units.
            let mut occurrence_counts: BTreeMap<MirValueId, usize> = BTreeMap::new();
            for value_id in &consumed {
                *occurrence_counts.entry(value_id.clone()).or_insert(0) += 1;
            }

            for (value_id, count) in occurrence_counts {
                let Some(live) = live_sets.get(&value_id) else {
                    continue;
                };

                // Is the value live in any successor block?
                let live_in_successor = successors
                    .get(&block.id)
                    .is_some_and(|succs| succs.iter().any(|sid| live.contains(sid)));

                // Is the value used in a later instruction of this block?
                let used_later_in_block = block.instructions[inst_idx + 1..]
                    .iter()
                    .any(|i| inst_reads_value(i, &value_id));

                // Does a later instruction in this block *consume* value_id (as a call
                // argument)?  If so, the extra retain unit we insert is absorbed by that
                // later consuming call — the current call gets one unit and the later call
                // gets the retained unit.  We must NOT also insert Release in dead
                // successors: by the time control reaches a successor the value has
                // already been consumed by the later call in this block.
                let consumed_later_in_block = block.instructions[inst_idx + 1..]
                    .iter()
                    .any(|i| inst_value_consumed_by_call(i, &value_id));

                // Number of extra ownership units needed:
                // - (count - 1) for duplicate appearances in the same call
                // - +1 if the value is also used after the call
                let extra_retains =
                    (count - 1) + usize::from(live_in_successor || used_later_in_block);

                for _ in 0..extra_retains {
                    retains.push((block.id.clone(), inst_idx, value_id.clone()));
                }

                // Only insert balancing Release in dead successors when the extra retain
                // unit is NOT already consumed by a later call in this same block.
                if (live_in_successor || used_later_in_block) && !consumed_later_in_block {
                    // The retained extra reference must be released in every dead successor
                    // (where the value is not live and not forwarded via Jump args).
                    if let Some(succs) = successors.get(&block.id) {
                        for succ_id in succs {
                            if live.contains(succ_id) {
                                continue; // will be consumed on that path
                            }
                            let is_forwarded = forwarded_to
                                .get(&value_id)
                                .is_some_and(|ft| ft.contains(succ_id));
                            if is_forwarded {
                                continue;
                            }
                            let already_has_release = function
                                .blocks
                                .iter()
                                .find(|b| &b.id == succ_id)
                                .is_some_and(|b| {
                                    b.instructions.iter().any(|i| {
                                        matches!(i, MirInst::Release { value } if value == &value_id)
                                    })
                                });
                            if !already_has_release {
                                releases.insert((succ_id.clone(), value_id.clone()));
                            }
                        }
                    }
                }
            }
        }
    }

    // Insert Retains (reverse order to preserve instruction indices).
    retains.reverse();
    for (block_id, inst_idx, value) in retains {
        if let Some(block) = function.blocks.iter_mut().find(|b| b.id == block_id) {
            block.instructions.insert(inst_idx, MirInst::Retain { value });
        }
    }

    // Insert Releases at tails of dead successor blocks.
    for (block_id, value) in releases {
        if let Some(block) = function.blocks.iter_mut().find(|b| b.id == block_id) {
            // Only insert if not already present (idempotent).
            let already = block
                .instructions
                .iter()
                .any(|i| matches!(i, MirInst::Release { value: v } if v == &value));
            if !already {
                block.instructions.push(MirInst::Release { value });
            }
        }
    }
}

/// - `B` is dead at entry (v_i not live along any path from B to a use),
/// - at least one predecessor of `B` is live at entry for v_i, and
/// - no predecessor forwards v_i explicitly as a Jump argument to B
///   (which would create a new SSA alias handled by the Block cleanup).
///
/// Releases inserted at block tails are then rescheduled to just after the
/// parameter's last use by `schedule_trailing_releases_after_last_use`, enabling
/// same-layout reuse fusion when the next `RecordInit`/`SumInit` of matching
/// layout follows.
fn insert_releases_for_dead_params(function: &mut MirFunction, layouts: &MirLayoutCatalog) {
    // FIP functions must have zero explicit releases — the FIP verifier rejects any Release
    // instruction as evidence that the function is not truly functional in-place.
    if function.is_fip {
        return;
    }
    // Identify heap-managed function parameters.
    // Use infer_heap_layout_keys rather than is_heap_managed_type so that:
    // - Function-typed params (closure objects) are excluded — releasing a closure param here
    //   would cause a double-free of its captures when the closure destructor also releases them.
    // - Unboxed record params (is_unboxed == true, e.g. all-primitive-field structs) are also
    //   excluded — they are stack-allocated; inserting Release triggers reuse analysis which
    //   converts a 0-alloc stack init into a RecordInitReuse (counted as 1 alloc in stats).
    // - Sum-typed params use Case 2 only (not Case 1). Case 1 (release at head of dead
    //   successor block) is unsafe for sum types without Perceus RC=1 uniqueness checks:
    //   releasing a parent sum at the boundary of a dead branch could free inner nodes that
    //   the caller still holds references to via a shallow Retain of the outermost pointer.
    //   Case 2 is safe when the extracted payload type is a known primitive (not Dynamic).
    let heap_layout_keys = infer_heap_layout_keys(function);
    let mut managed_record_params: Vec<MirValueId> = Vec::new();
    let mut managed_sum_params: Vec<MirValueId> = Vec::new();
    for i in 0..function.signature.params.len() {
        let param_id = MirValueId(i as u32);
        let Some(key) = heap_layout_keys.get(&param_id) else {
            continue;
        };
        if let Some(record_name) = key.strip_prefix("record:") {
            // Skip only explicitly unboxed records — those are stack-allocated and
            // never heap-managed. Records whose fields happen to be all-primitives
            // are still heap-allocated when passed as function parameters (the caller
            // boxed them), so they DO need a Release here.
            if layouts
                .records
                .iter()
                .find(|l| l.name == record_name)
                .is_some_and(|layout| layout.is_unboxed)
            {
                continue;
            }
            managed_record_params.push(param_id);
        } else if key.starts_with("sum:") {
            managed_sum_params.push(param_id);
        }
    }
    // Locally-defined sum-typed Call results are uniquely owned by this function
    // (freshly allocated return values, RC=1 at the call site). Case 1 is therefore
    // safe for them — unlike sum params — but ONLY in blocks reachable from the
    // defining block. An SSA Call result only exists on control-flow paths that
    // pass through its defining block; inserting a Release on a disjoint path
    // (e.g. the `if n<=0` base-case branch when the Call is in the `else` branch)
    // would reference an undefined value.
    let mut managed_local_sum_calls: Vec<MirValueId> = Vec::new();
    // Maps each local sum Call result to the block where it is defined, for the
    // Case 1 reachability constraint.
    let mut def_block_for_case1: BTreeMap<MirValueId, MirBlockId> = BTreeMap::new();
    for block in &function.blocks {
        for inst in &block.instructions {
            if let MirInst::Call { result: Some(dest), .. } = inst
                && heap_layout_keys
                    .get(dest)
                    .is_some_and(|k| k.starts_with("sum:"))
            {
                managed_local_sum_calls.push(dest.clone());
                def_block_for_case1.insert(dest.clone(), block.id.clone());
            }
        }
    }

    let managed_params: Vec<MirValueId> = managed_record_params
        .iter()
        .chain(managed_sum_params.iter())
        .chain(managed_local_sum_calls.iter())
        .cloned()
        .collect();

    if managed_params.is_empty() {
        return;
    }

    // Build successor and predecessor maps once, reused for each parameter.
    let mut successors: BTreeMap<MirBlockId, Vec<MirBlockId>> = function
        .blocks
        .iter()
        .map(|b| (b.id.clone(), Vec::new()))
        .collect();
    let mut predecessors: BTreeMap<MirBlockId, Vec<MirBlockId>> = function
        .blocks
        .iter()
        .map(|b| (b.id.clone(), Vec::new()))
        .collect();
    for block in &function.blocks {
        match &block.terminator {
            MirTerminator::Jump { target, .. } => {
                successors.entry(block.id.clone()).or_default().push(target.clone());
                predecessors.entry(target.clone()).or_default().push(block.id.clone());
            }
            MirTerminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                successors
                    .entry(block.id.clone())
                    .or_default()
                    .push(then_block.clone());
                successors
                    .entry(block.id.clone())
                    .or_default()
                    .push(else_block.clone());
                predecessors
                    .entry(then_block.clone())
                    .or_default()
                    .push(block.id.clone());
                predecessors
                    .entry(else_block.clone())
                    .or_default()
                    .push(block.id.clone());
            }
            _ => {}
        }
    }

    for param_id in &managed_params {
        // --- Step 1: Backward liveness --- //
        // A block is "live" if it directly uses the parameter (in instructions
        // or terminator) OR any of its successors is live.
        let direct_use: BTreeSet<MirBlockId> = function
            .blocks
            .iter()
            .filter(|block| {
                block
                    .instructions
                    .iter()
                    .any(|inst| inst_reads_value(inst, param_id))
                    || match &block.terminator {
                        MirTerminator::Jump { args, .. } => args.contains(param_id),
                        MirTerminator::Return { value: Some(v), .. } => v == param_id,
                        MirTerminator::Branch { condition, .. } => condition == param_id,
                        _ => false,
                    }
            })
            .map(|b| b.id.clone())
            .collect();

        let mut live: BTreeSet<MirBlockId> = direct_use;
        let mut changed = true;
        while changed {
            changed = false;
            for block in &function.blocks {
                if live.contains(&block.id) {
                    continue;
                }
                if successors
                    .get(&block.id)
                    .is_some_and(|s| s.iter().any(|sid| live.contains(sid)))
                {
                    live.insert(block.id.clone());
                    changed = true;
                }
            }
        }

        // --- Step 2: Blocks that receive param via an explicit Jump arg --- //
        // These blocks get param as a new SSA block-param alias; the Block
        // cleanup already handles releases for those aliases when needed.
        let param_forwarded_to: BTreeSet<MirBlockId> = function
            .blocks
            .iter()
            .filter_map(|block| {
                if let MirTerminator::Jump { target, args } = &block.terminator {
                    if args.contains(param_id) { Some(target.clone()) } else { None }
                } else {
                    None
                }
            })
            .collect();

        // --- Step 3: Compute release insertion points (before inserting anything) --- //
        //
        // For locally-defined Call results (not function params), precompute which
        // blocks are reachable from the defining block via a forward BFS. A Case 1
        // Release is only valid in a block reachable from the defining block — the
        // SSA value does not exist on control-flow paths that bypass its definition.
        let reachable_from_def: Option<BTreeSet<MirBlockId>> =
            if let Some(def_block) = def_block_for_case1.get(param_id) {
                let mut reachable = BTreeSet::new();
                let mut stack = vec![def_block.clone()];
                while let Some(bid) = stack.pop() {
                    if reachable.insert(bid.clone())
                        && let Some(succs) = successors.get(&bid)
                    {
                        for s in succs {
                            if !reachable.contains(s) {
                                stack.push(s.clone());
                            }
                        }
                    }
                }
                Some(reachable)
            } else {
                None
            };

        // Case 1 — death boundary: param is live in predecessor but dead in this block.
        // Release is inserted at the head of the first dead block on each path.
        let case1_candidates: BTreeSet<MirBlockId> = function
            .blocks
            .iter()
            .filter(|block| {
                // Must be dead at entry (param not live here or downstream).
                !live.contains(&block.id)
                // Must not already receive param via a predecessor's Jump arg.
                && !param_forwarded_to.contains(&block.id)
                // Must not already have an explicit Release for this param.
                && !block.instructions.iter().any(|inst| {
                    matches!(inst, MirInst::Release { value } if value == param_id)
                })
                // For locally-defined Call results: only in blocks reachable from the
                // defining block. The value is undefined on disjoint CFG paths.
                && reachable_from_def.as_ref().map(|r| r.contains(&block.id)).unwrap_or(true)
                // Must have ALL predecessors live at entry.
                // If any predecessor is dead, that dead predecessor has its own Case 1
                // Release for the incoming path. Inserting another Release here would
                // double-free on paths that pass through the dead predecessor.
                // Case 1 only fires at the IMMEDIATE FRONTIER of the dead region —
                // blocks where every incoming edge comes from a live block.
                // Blocks deeper in the dead region (with dead predecessors) are handled
                // by Case 2 at the tail of the last live block that reaches them.
                && predecessors
                    .get(&block.id)
                    .is_some_and(|preds| !preds.is_empty() && preds.iter().all(|pid| live.contains(pid)))
                // Must not be an unreachable block.
                && !matches!(block.terminator, MirTerminator::Unreachable)
                // Must have NO predecessor that consumed the param via an
                // ownership-transferring operation (Call or CowUpdate). When a predecessor
                // passes param to a Call, the callee takes ownership on that path and will
                // release it; inserting a Release at this join block would double-free.
                //
                // When SOME predecessors consumed and others did not, Case 1 must stay out
                // entirely — a single Release here would be wrong for the consuming paths.
                // Case 2 will then fire for each non-consuming predecessor and insert the
                // Release at that block's tail, where it is safe and path-specific.
                && predecessors
                    .get(&block.id)
                    .map(|preds| {
                        preds.iter()
                            .filter(|pid| live.contains(*pid))
                            .all(|pid| {
                                function.blocks.iter()
                                    .find(|b| &b.id == pid)
                                    .map(|pred_block| {
                                        // The last instruction that reads param in this pred.
                                        let last_read = pred_block.instructions.iter().rev()
                                            .find(|inst| inst_reads_value(inst, param_id));
                                        match last_read {
                                            Some(inst) => !inst_value_consumed_by_call(inst, param_id),
                                            // No instruction read it — check terminator (Jump args)
                                            None => !matches!(
                                                &pred_block.terminator,
                                                MirTerminator::Jump { args, .. } if args.contains(param_id)
                                            ),
                                        }
                                    })
                                    .unwrap_or(true)
                            })
                    })
                    .unwrap_or(true)
            })
            .map(|b| b.id.clone())
            .collect();

        // Case 2 — last-user inline: param IS used in a block but all successors are dead.
        // Insert Release at the block's tail. Only fires when Case 1 would NOT also insert
        // releases in the dead successors — otherwise we'd double-release on every path
        // that exits through those successors.
        //
        // A dead successor is "covered by Case 1" when it IS a Case 1 candidate.
        // If any dead successor is a Case 1 candidate, Case 1 handles that path and
        // Case 2 must not also insert inline (they're mutually exclusive per param per path).
        //
        // Case 2 fires only when all dead successors are excluded from Case 1:
        //   - they receive the param via Jump args (param_forwarded_to), or
        //   - they are Unreachable, or
        //   - they already had a Release before this pass ran.
        let case2_candidates: BTreeSet<MirBlockId> = function
            .blocks
            .iter()
            .filter(|block| {
                // Must be in live (directly reads the param).
                live.contains(&block.id)
                // All successors must be outside the live set — this block is the last user.
                && successors
                    .get(&block.id)
                    .map(|succs| succs.iter().all(|sid| !live.contains(sid)))
                    .unwrap_or(true)
                // Param must not be forwarded to a successor via Jump args.
                && !matches!(&block.terminator, MirTerminator::Jump { args, .. } if args.contains(param_id))
                // Param must not be returned to the caller — caller owns the returned value.
                && !matches!(&block.terminator, MirTerminator::Return { value: Some(v) } if v == param_id)
                // Last read of param must not be as a Call arg/callee (ownership transferred).
                // Also: if the last read was a SumPayloadLoad that extracted a managed-type
                // child (or a Dynamic child — Dynamic can hold a heap pointer in polymorphic
                // functions), releasing the sum parent would run its destructor and double-free
                // the extracted child. Skip until a Perceus uniqueness-check pass is added.
                && !block.instructions.iter().rev()
                    .find(|inst| inst_reads_value(inst, param_id))
                    .is_some_and(|inst| {
                        inst_value_consumed_by_call(inst, param_id)
                            || matches!(inst, MirInst::SumPayloadLoad { sum, field_ty, .. }
                                if sum == param_id
                                    && (is_heap_managed_type(field_ty, layouts)
                                        || *field_ty == Type::Dynamic))
                    })
                // Must not already have an explicit Release for this param.
                && !block.instructions.iter().any(|inst| {
                    matches!(inst, MirInst::Release { value } if value == param_id)
                })
                && !matches!(block.terminator, MirTerminator::Unreachable)
                // KEY: only fire if Case 1 would NOT also release in the dead successors.
                // If any dead successor is a Case 1 candidate, let Case 1 handle it.
                && successors
                    .get(&block.id)
                    .map(|succs| {
                        succs
                            .iter()
                            .filter(|sid| !live.contains(*sid))
                            .all(|sid| !case1_candidates.contains(sid))
                    })
                    .unwrap_or(true)
            })
            .map(|b| b.id.clone())
            .collect();

        // --- Step 4: Insert the releases --- //
        // Case 1 (dead-boundary release) is applied to record params AND locally-defined
        // sum Call results (uniquely owned, RC=1 — releasing at a dead boundary is safe).
        // Sum-typed *function params* skip Case 1: the caller may hold a shallow Retain
        // of the outermost pointer; releasing at the dead boundary would decrement the
        // shared RC and free inner nodes still reachable by the caller.
        // Case 2 is applied to all managed values (with the SumPayloadLoad safety guard).
        if !managed_sum_params.contains(param_id) {
            for block_id in case1_candidates {
                if let Some(block) = function.blocks.iter_mut().find(|b| b.id == block_id) {
                    block.instructions.push(MirInst::Release {
                        value: param_id.clone(),
                    });
                }
            }
        }

        for block_id in case2_candidates {
            if let Some(block) = function.blocks.iter_mut().find(|b| b.id == block_id) {
                block.instructions.push(MirInst::Release {
                    value: param_id.clone(),
                });
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum ReuseInitCandidate {
    Record {
        dest: MirValueId,
        record_type: String,
        fields: Vec<(String, MirValueId)>,
    },
    Sum {
        dest: MirValueId,
        sum_type: String,
        variant: String,
        tag: u32,
        fields: Vec<MirValueId>,
    },
}

type ReuseProbe = (usize, ReuseInitCandidate);

fn find_reuse_probe(
    block: &MirBlock,
    release_idx: usize,
    released_value: &MirValueId,
    layouts: &MirLayoutCatalog,
    layout_keys: &BTreeMap<MirValueId, String>,
) -> Option<ReuseProbe> {
    let release_layout = layout_keys.get(released_value)?;
    for probe in release_idx + 1..block.instructions.len() {
        let inst = &block.instructions[probe];
        if inst_reads_value(inst, released_value)
            || inst_defined_value(inst).is_some_and(|dest| dest == released_value)
        {
            return None;
        }
        match inst {
            MirInst::RecordInit {
                dest,
                record_type,
                fields,
            } => {
                let alloc_layout = format!("record:{record_type}");
                let layout_matches = alloc_layout == *release_layout;
                let layout_is_reusable = record_layout_is_reuse_eligible(layouts, record_type);
                let source_mentioned_in_fields = fields
                    .iter()
                    .any(|(_, field_value)| field_value == released_value);
                if layout_matches && layout_is_reusable && !source_mentioned_in_fields {
                    return Some((
                        probe,
                        ReuseInitCandidate::Record {
                            dest: dest.clone(),
                            record_type: record_type.clone(),
                            fields: fields.clone(),
                        },
                    ));
                }
                return None;
            }
            MirInst::SumInit {
                dest,
                sum_type,
                variant,
                tag,
                fields,
            } => {
                let alloc_layout = format!("sum:{sum_type}");
                let layout_matches = alloc_layout == *release_layout;
                let layout_is_reusable = sum_layout_is_reuse_eligible(layouts, sum_type);
                let source_mentioned_in_fields = fields
                    .iter()
                    .any(|field_value| field_value == released_value);
                if layout_matches && layout_is_reusable && !source_mentioned_in_fields {
                    return Some((
                        probe,
                        ReuseInitCandidate::Sum {
                            dest: dest.clone(),
                            sum_type: sum_type.clone(),
                            variant: variant.clone(),
                            tag: *tag,
                            fields: fields.clone(),
                        },
                    ));
                }
                return None;
            }
            _ if inst.is_memory_op() => return None,
            _ => {}
        }
    }
    None
}

fn find_reuse_candidate_in_block(
    block: &MirBlock,
    source_value: &MirValueId,
    layouts: &MirLayoutCatalog,
    layout_keys: &BTreeMap<MirValueId, String>,
) -> Option<ReuseProbe> {
    let source_layout = layout_keys.get(source_value)?;
    for (idx, inst) in block.instructions.iter().enumerate() {
        if inst_reads_value(inst, source_value)
            || inst_defined_value(inst).is_some_and(|dest| dest == source_value)
        {
            return None;
        }
        match inst {
            MirInst::RecordInit {
                dest,
                record_type,
                fields,
            } => {
                let alloc_layout = format!("record:{record_type}");
                let layout_matches = alloc_layout == *source_layout;
                let layout_is_reusable = record_layout_is_reuse_eligible(layouts, record_type);
                let source_mentioned_in_fields =
                    fields.iter().any(|(_, field)| field == source_value);
                if layout_matches && layout_is_reusable && !source_mentioned_in_fields {
                    return Some((
                        idx,
                        ReuseInitCandidate::Record {
                            dest: dest.clone(),
                            record_type: record_type.clone(),
                            fields: fields.clone(),
                        },
                    ));
                }
                return None;
            }
            MirInst::SumInit {
                dest,
                sum_type,
                variant,
                tag,
                fields,
            } => {
                let alloc_layout = format!("sum:{sum_type}");
                let layout_matches = alloc_layout == *source_layout;
                let layout_is_reusable = sum_layout_is_reuse_eligible(layouts, sum_type);
                let source_mentioned_in_fields = fields.iter().any(|field| field == source_value);
                if layout_matches && layout_is_reusable && !source_mentioned_in_fields {
                    return Some((
                        idx,
                        ReuseInitCandidate::Sum {
                            dest: dest.clone(),
                            sum_type: sum_type.clone(),
                            variant: variant.clone(),
                            tag: *tag,
                            fields: fields.clone(),
                        },
                    ));
                }
                return None;
            }
            _ if inst.is_memory_op() => return None,
            _ => {}
        }
    }
    None
}

fn infer_heap_layout_keys(function: &MirFunction) -> BTreeMap<MirValueId, String> {
    let mut keys = BTreeMap::new();
    for (index, param_ty) in function.signature.params.iter().enumerate() {
        if let Some(layout_key) = type_layout_key(param_ty) {
            keys.insert(MirValueId(index as u32), layout_key);
        }
    }
    for block in &function.blocks {
        for param in &block.params {
            if let Some(layout_key) = type_layout_key(&param.ty) {
                keys.insert(param.id.clone(), layout_key);
            }
        }
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
                }
                | MirInst::CowUpdate {
                    dest, record_type, ..
                } => {
                    keys.insert(dest.clone(), format!("record:{record_type}"));
                }
                MirInst::SumInit { dest, sum_type, .. } => {
                    keys.insert(dest.clone(), format!("sum:{sum_type}"));
                }
                MirInst::SumInitReuse { dest, sum_type, .. } => {
                    keys.insert(dest.clone(), format!("sum:{sum_type}"));
                }
                MirInst::SumInitFromToken { dest, sum_type, .. } => {
                    keys.insert(dest.clone(), format!("sum:{sum_type}"));
                }
                MirInst::ReuseToken { dest, source } => {
                    if let Some(layout_key) = keys.get(source).cloned() {
                        keys.insert(dest.clone(), layout_key);
                    }
                }
                MirInst::Move { dest, src }
                | MirInst::Borrow { dest, src }
                | MirInst::TryClaim { dest, src }
                | MirInst::Freeze { dest, src } => {
                    if let Some(layout_key) = keys.get(src).cloned() {
                        keys.insert(dest.clone(), layout_key);
                    }
                }
                MirInst::Call {
                    result: Some(dest),
                    ret_type,
                    ..
                } => {
                    if let Some(layout_key) = type_layout_key(ret_type) {
                        keys.insert(dest.clone(), layout_key);
                    }
                }
                _ => {}
            }
        }
    }
    // Propagate layout keys through Jump terminator args to block params (fixpoint).
    // Block params that join if/else branches may have Dynamic type in the HIR when
    // arm expressions have heterogeneous static types. Propagating the concrete key
    // from the Jump argument to the block param lets reuse analysis see the correct
    // layout on join-block params (e.g. `q` in an if/else that produces a Point on
    // both branches).
    loop {
        let mut changed = false;
        for block_idx in 0..function.blocks.len() {
            if let MirTerminator::Jump { target, args } = &function.blocks[block_idx].terminator {
                let target = target.clone();
                let args = args.clone();
                if let Some(target_block) = function.blocks.iter().find(|b| b.id == target) {
                    for (arg_value, block_param) in args.iter().zip(target_block.params.iter()) {
                        if !keys.contains_key(&block_param.id)
                            && let Some(key) = keys.get(arg_value).cloned()
                        {
                            keys.insert(block_param.id.clone(), key);
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    keys
}


fn type_layout_key(ty: &Type) -> Option<String> {
    match ty {
        Type::Record(record) => Some(format!("record:{}", record.name)),
        Type::Sum(sum) => Some(format!("sum:{}", sum.name)),
        _ => None,
    }
}

fn record_layout_is_reuse_eligible(layouts: &MirLayoutCatalog, record_type: &str) -> bool {
    let Some(layout) = layouts
        .records
        .iter()
        .find(|layout| layout.name == record_type)
    else {
        return false;
    };
    layout
        .fields
        .iter()
        .all(|field| !annotation_is_heap_managed(&field.annotation, layouts))
}

fn sum_layout_is_reuse_eligible(layouts: &MirLayoutCatalog, sum_type: &str) -> bool {
    let Some(layout) = layouts.sums.iter().find(|layout| layout.name == sum_type) else {
        return false;
    };
    if layout
        .variants
        .iter()
        .any(|variant| variant.fields.is_empty())
    {
        return false;
    }
    layout
        .variants
        .iter()
        .flat_map(|variant| &variant.fields)
        .all(|field| !annotation_is_heap_managed(&field.annotation, layouts))
}

fn annotation_is_heap_managed(annotation: &TypeAnnotation, layouts: &MirLayoutCatalog) -> bool {
    match annotation {
        TypeAnnotation::Named(name) => {
            if matches!(
                name.as_str(),
                "Int"
                    | "Bool"
                    | "Float"
                    | "Unit"
                    | "Int8"
                    | "Int16"
                    | "Int32"
                    | "Int64"
                    | "UInt8"
                    | "UInt16"
                    | "UInt32"
                    | "UInt64"
                    | "Float16"
                    | "Float32"
                    | "Float64"
            ) {
                return false;
            }
            if layouts
                .records
                .iter()
                .find(|record| record.name == *name)
                .is_some_and(|record| record.is_unboxed)
            {
                return false;
            }
            true
        }
        TypeAnnotation::Tuple(items) => items
            .iter()
            .any(|item| annotation_is_heap_managed(item, layouts)),
        _ => true,
    }
}

fn compute_release_insertion_pos(
    value: &MirValueId,
    params: &[MirBlockParam],
    prefix: &[MirInst],
    terminator: &MirTerminator,
) -> usize {
    let mut has_definition = params.iter().any(|param| &param.id == value);
    let mut def_pos = if has_definition { 0 } else { prefix.len() };
    for (idx, inst) in prefix.iter().enumerate() {
        if inst_defined_value(inst).is_some_and(|dest| dest == value) {
            has_definition = true;
            def_pos = idx + 1;
        }
    }

    let mut last_use_pos = 0usize;
    for (idx, inst) in prefix.iter().enumerate() {
        if inst_reads_value(inst, value) {
            last_use_pos = idx + 1;
        }
    }
    if terminator_reads_value(terminator, value) {
        last_use_pos = prefix.len();
    }

    if has_definition {
        last_use_pos.max(def_pos).min(prefix.len())
    } else {
        prefix.len()
    }
}

fn inst_defined_value(inst: &MirInst) -> Option<&MirValueId> {
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
        | MirInst::Freeze { dest, .. }
        | MirInst::CowUpdate { dest, .. } => Some(dest),
        MirInst::EffectOp {
            result: Some(dest), ..
        } => Some(dest),
        MirInst::Call {
            result: Some(dest), ..
        } => Some(dest),
        MirInst::StateCellStore { .. }
        | MirInst::Retain { .. }
        | MirInst::Release { .. }
        | MirInst::EffectOp { result: None, .. }
        | MirInst::HandlerEnter { .. }
        | MirInst::HandlerExit { .. }
        | MirInst::Resume { .. }
        | MirInst::Call { result: None, .. }
        | MirInst::Unsupported { .. }
        | MirInst::Nop => None,
    }
}

fn inst_reads_value(inst: &MirInst, value: &MirValueId) -> bool {
    match inst {
        MirInst::Const { .. } | MirInst::FunctionRef { .. } | MirInst::HandlerEnter { .. } => false,
        MirInst::Binary { left, right, .. } => left == value || right == value,
        MirInst::Unary { operand, .. } => operand == value,
        MirInst::RecordInit { fields, .. } => fields.iter().any(|(_, field)| field == value),
        MirInst::RecordInitReuse { source, fields, .. } => {
            source == value || fields.iter().any(|(_, field)| field == value)
        }
        MirInst::ReuseToken { source, .. } => source == value,
        MirInst::RecordInitFromToken { token, fields, .. } => {
            token == value || fields.iter().any(|(_, field)| field == value)
        }
        MirInst::SumInit { fields, .. } => fields.iter().any(|field| field == value),
        MirInst::SumInitReuse { source, fields, .. } => {
            source == value || fields.iter().any(|field| field == value)
        }
        MirInst::SumInitFromToken { token, fields, .. } => {
            token == value || fields.iter().any(|field| field == value)
        }
        MirInst::SumTagLoad { sum, .. } => sum == value,
        MirInst::SumPayloadLoad { sum, .. } => sum == value,
        MirInst::RecordFieldLoad { record, .. } => record == value,
        MirInst::ClosureInit {
            entry, captures, ..
        } => entry == value || captures.iter().any(|capture| capture == value),
        MirInst::ClosureCaptureLoad { closure, .. } => closure == value,
        MirInst::StateCellNew { initial, .. } => initial == value,
        MirInst::StateCellLoad { cell, .. } => cell == value,
        MirInst::StateCellStore {
            cell,
            value: stored,
        } => cell == value || stored == value,
        MirInst::Retain { value: retained } | MirInst::Release { value: retained } => {
            retained == value
        }
        MirInst::Move { src, .. }
        | MirInst::Borrow { src, .. }
        | MirInst::TryClaim { src, .. }
        | MirInst::Freeze { src, .. } => src == value,
        MirInst::CowUpdate {
            target, updates, ..
        } => target == value || updates.iter().any(|update| &update.value == value),
        MirInst::EffectOp { args, .. } => args.iter().any(|arg| arg == value),
        MirInst::HandlerExit { .. } => false,
        MirInst::Resume { value: resumed } => resumed == value,
        MirInst::Call { callee, args, .. } => match callee {
            MirCallee::Value(callee_value) => {
                callee_value == value || args.iter().any(|arg| arg == value)
            }
            MirCallee::Local(_) | MirCallee::External(_) => args.iter().any(|arg| arg == value),
        },
        MirInst::Unsupported { .. } | MirInst::Nop => false,
    }
}

fn terminator_reads_value(terminator: &MirTerminator, value: &MirValueId) -> bool {
    match terminator {
        MirTerminator::Jump { args, .. } => args.iter().any(|arg| arg == value),
        MirTerminator::Branch { condition, .. } => condition == value,
        MirTerminator::Return {
            value: Some(returned),
        } => returned == value,
        MirTerminator::Return { value: None } | MirTerminator::Unreachable => false,
    }
}

#[derive(Debug, Clone)]
struct LambdaFactoryTemplate {
    outer_params: Vec<String>,
    lambda_params: Vec<kea_hir::HirParam>,
    lambda_body: HirExpr,
    captures: Vec<String>,
}

struct DirectCapabilitySpec {
    effect: &'static str,
    operations: &'static [&'static str],
}

const DIRECT_CAPABILITIES: &[DirectCapabilitySpec] = &[
    DirectCapabilitySpec {
        effect: "IO",
        operations: &["stdout", "stderr", "read_file", "write_file", "exit", "file_exists", "env_var", "mkdir"],
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

fn direct_capability_operation(name: &str) -> Option<(&'static str, &'static str)> {
    for capability in DIRECT_CAPABILITIES {
        let Some(operation_name) = name.strip_prefix(capability.effect) else {
            continue;
        };
        let Some(operation_name) = operation_name.strip_prefix('.') else {
            continue;
        };
        if let Some(&operation) = capability
            .operations
            .iter()
            .find(|operation| **operation == operation_name)
        {
            return Some((capability.effect, operation));
        }
    }
    None
}

fn ptr_intrinsic_symbol(name: &str) -> Option<&'static str> {
    match name {
        "Ptr.null" | "Kea.Ptr.null" => Some("__kea_ptr_null"),
        "Ptr.is_null" | "Kea.Ptr.is_null" => Some("__kea_ptr_is_null"),
        "Ptr.read" | "Kea.Ptr.read" => Some("__kea_ptr_read_i64"),
        "Ptr.write" | "Kea.Ptr.write" => Some("__kea_ptr_write_i64"),
        "Ptr.offset" | "Kea.Ptr.offset" => Some("__kea_ptr_offset"),
        "Ptr.cast" | "Kea.Ptr.cast" => Some("__kea_ptr_cast"),
        "Ptr.alloc" | "Kea.Ptr.alloc" => Some("__kea_ptr_alloc"),
        "Ptr.free" | "Kea.Ptr.free" => Some("__kea_ptr_free"),
        _ => None,
    }
}

fn ptr_pointee_size_bytes(ty: &Type) -> i64 {
    match ty {
        Type::IntN(width, _) => match width {
            kea_types::IntWidth::I8 => 1,
            kea_types::IntWidth::I16 => 2,
            kea_types::IntWidth::I32 => 4,
            kea_types::IntWidth::I64 => 8,
        },
        Type::FloatN(width) => match width {
            kea_types::FloatWidth::F16 | kea_types::FloatWidth::F32 => 4,
            kea_types::FloatWidth::F64 => 8,
        },
        Type::Bool => 1,
        Type::Char => 4,
        Type::Unit => 1,
        Type::Int | Type::Float => 8,
        // Bootstrap aggregates and other opaque/runtime carriers flow as words.
        _ => 8,
    }
}

fn ptr_element_size_from_ptr_type(ty: &Type) -> Option<i64> {
    match ty {
        Type::Opaque { name, params } if name == "Ptr" && params.len() == 1 => {
            Some(ptr_pointee_size_bytes(&params[0]))
        }
        _ => None,
    }
}

fn ptr_intrinsic_extra_int_arg(name: &str, arg_types: &[Type], ret_type: &Type) -> Option<i64> {
    match name {
        "Ptr.offset" | "Kea.Ptr.offset" => arg_types
            .first()
            .and_then(ptr_element_size_from_ptr_type)
            .or_else(|| ptr_element_size_from_ptr_type(ret_type))
            .or(Some(8)),
        "Ptr.alloc" | "Kea.Ptr.alloc" => ptr_element_size_from_ptr_type(ret_type).or(Some(8)),
        _ => None,
    }
}

fn is_direct_capability_effect(effect: &str) -> bool {
    DIRECT_CAPABILITIES
        .iter()
        .any(|capability| capability.effect == effect)
}

fn default_capability_wrapper_name(effect: &str, operation: &str) -> String {
    format!("__kea_default_{effect}_{operation}")
}

/// Generate MIR wrapper functions for each capability operation.  Each wrapper
/// is a closure entry: it takes `(closure_ptr, ...operation_args)` and forwards
/// to `EffectOp::Direct`.  Entry-point functions create closures referencing
/// these wrappers as default capability cells.
fn generate_default_capability_wrappers(
    effect_operations: &BTreeMap<String, EffectOperationInfo>,
) -> Vec<MirFunction> {
    let mut wrappers = Vec::new();
    let mut seen = BTreeSet::new();
    for op in effect_operations.values() {
        if !is_direct_capability_effect(&op.effect) {
            continue;
        }
        let fn_name = default_capability_wrapper_name(&op.effect, &op.operation);
        if !seen.insert(fn_name.clone()) {
            continue;
        }
        // Params: closure_ptr (Dynamic) + one Dynamic per real arg
        let mut params = vec![Type::Dynamic]; // closure_ptr (unused)
        for _ in 0..op.arity {
            params.push(Type::Dynamic);
        }
        let ret = if op.returns_unit {
            Type::Unit
        } else {
            Type::Dynamic
        };
        // Real args are MirValueId(1..arity) — MirValueId(0) is closure_ptr
        let args: Vec<MirValueId> = (1..=op.arity as u32).map(MirValueId).collect();
        let result = if op.returns_unit {
            None
        } else {
            Some(MirValueId(op.arity as u32 + 1))
        };
        wrappers.push(MirFunction {
            name: fn_name,
            signature: MirFunctionSignature {
                params,
                ret: ret.clone(),
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: Vec::new(),
                instructions: vec![MirInst::EffectOp {
                    class: MirEffectOpClass::Direct,
                    effect: op.effect.clone(),
                    operation: op.operation.clone(),
                    args,
                    result: result.clone(),
                }],
                terminator: MirTerminator::Return { value: result },
            }],
        });
    }
    wrappers
}

#[derive(Debug, Clone)]
struct EffectOperationInfo {
    effect: String,
    operation: String,
    arity: usize,
    returns_unit: bool,
    returns_never: bool,
}

fn is_unit_type_annotation(annotation: &TypeAnnotation) -> bool {
    matches!(annotation, TypeAnnotation::Named(name) if name == "Unit")
}

fn is_never_type_annotation(annotation: &TypeAnnotation) -> bool {
    matches!(annotation, TypeAnnotation::Named(name) if name == "Never")
}

fn collect_effect_operations(module: &HirModule) -> BTreeMap<String, EffectOperationInfo> {
    let mut operations = BTreeMap::new();
    for decl in &module.declarations {
        let HirDecl::Raw(DeclKind::EffectDecl(effect_decl)) = decl else {
            continue;
        };
        let effect = effect_decl.name.node.clone();
        let module_path = format!("Kea.{effect}");
        for op in &effect_decl.operations {
            let operation = op.name.node.clone();
            let info = EffectOperationInfo {
                effect: effect.clone(),
                operation: operation.clone(),
                arity: op.params.len(),
                returns_unit: is_unit_type_annotation(&op.return_annotation.node),
                returns_never: is_never_type_annotation(&op.return_annotation.node),
            };
            operations.insert(format!("{effect}.{operation}"), info.clone());
            operations.insert(format!("{module_path}.{operation}"), info);
        }
    }
    operations
}

fn handler_cell_lowering_for_operation(op: &EffectOperationInfo) -> Option<HandlerCellOpLowering> {
    // Uniform InvokeCallback: all operations dispatch through callback closures.
    // This eliminates plan mismatch between handler and callee — there's only one
    // dispatch mode, so no reconstruction needed. Previous LoadCell (zero-arg) and
    // StoreArgAndReturnUnit (State.put) modes are now callbacks that close over
    // internal state cells.
    Some(HandlerCellOpLowering::InvokeCallback {
        arity: op.arity,
        returns_unit: op.returns_unit,
    })
}

fn handler_plan_for_effect(
    effect_operations: &BTreeMap<String, EffectOperationInfo>,
    effect: &str,
) -> Option<ActiveEffectHandlerPlan> {
    // Uniform InvokeCallback: all operations dispatch through callback closures.
    // handler_cell_lowering_for_operation always returns InvokeCallback, so
    // the plan is the same for all effects — capability, stateful, or reader.
    let mut operation_lowering = BTreeMap::new();
    for op in effect_operations
        .values()
        .filter(|op| op.effect == effect)
        // Never-returning ops don't use the callback/cell dispatch mechanism.
        .filter(|op| !op.returns_never)
    {
        let Some(lowering) = handler_cell_lowering_for_operation(op) else {
            continue;
        };
        operation_lowering.insert(op.operation.clone(), lowering);
    }
    if operation_lowering.is_empty() {
        None
    } else {
        Some(ActiveEffectHandlerPlan { operation_lowering })
    }
}

fn collect_function_dispatch_effects(
    module: &HirModule,
    effect_operations: &BTreeMap<String, EffectOperationInfo>,
) -> BTreeMap<String, Vec<String>> {
    let dispatchable_effects = effect_operations
        .values()
        .map(|op| op.effect.clone())
        .collect::<BTreeSet<_>>();
    let mut mapping = BTreeMap::new();
    for decl in &module.declarations {
        let HirDecl::Function(function) = decl else {
            continue;
        };
        let Type::Function(ft) = &function.ty else {
            continue;
        };
        // Entry-point functions (main) don't receive hidden dispatch params
        // because the JIT harness calls them with zero args. They create
        // default capability cells internally instead.
        let is_entry_point = function.name == "main";
        let effects = ft
            .effects
            .row
            .fields
            .iter()
            .map(|(label, _)| label.as_str().to_string())
            .filter(|effect| dispatchable_effects.contains(effect))
            .filter(|effect| effect != "Fail")
            .filter(|effect| !is_entry_point || !is_direct_capability_effect(effect))
            .collect::<Vec<_>>();
        let mut dispatch_ops = BTreeSet::new();
        for effect in effects {
            for op in effect_operations
                .values()
                .filter(|op| op.effect == effect)
                // Never-returning ops don't participate in the dispatch/callback
                // mechanism: they use the Direct path (or trap). No cell needed.
                .filter(|op| !op.returns_never)
            {
                dispatch_ops.insert(format!("{effect}.{}", op.operation));
            }
        }
        if !dispatch_ops.is_empty() {
            mapping.insert(function.name.clone(), dispatch_ops.into_iter().collect());
        }
    }
    mapping
}

fn fixed_width_type_from_name(name: &str) -> Option<Type> {
    match name {
        "Int8" => Some(Type::IntN(
            kea_types::IntWidth::I8,
            kea_types::Signedness::Signed,
        )),
        "Int16" => Some(Type::IntN(
            kea_types::IntWidth::I16,
            kea_types::Signedness::Signed,
        )),
        "Int32" => Some(Type::IntN(
            kea_types::IntWidth::I32,
            kea_types::Signedness::Signed,
        )),
        "Int64" => Some(Type::IntN(
            kea_types::IntWidth::I64,
            kea_types::Signedness::Signed,
        )),
        "UInt8" => Some(Type::IntN(
            kea_types::IntWidth::I8,
            kea_types::Signedness::Unsigned,
        )),
        "UInt16" => Some(Type::IntN(
            kea_types::IntWidth::I16,
            kea_types::Signedness::Unsigned,
        )),
        "UInt32" => Some(Type::IntN(
            kea_types::IntWidth::I32,
            kea_types::Signedness::Unsigned,
        )),
        "UInt64" => Some(Type::IntN(
            kea_types::IntWidth::I64,
            kea_types::Signedness::Unsigned,
        )),
        _ => None,
    }
}

fn try_from_target_type_from_name(name: &str) -> Option<Type> {
    let mut parts = name.split('.');
    let last = parts.next_back()?;
    if last != "try_from" {
        return None;
    }
    let target = parts.next_back()?;
    fixed_width_type_from_name(target)
}

fn is_namespaced_symbol_name(name: &str) -> bool {
    name.contains('.')
}

/// Extract a nominal type name suitable for trait dispatch lookup.
/// Returns the type name for records, sums, and primitive types.
/// Returns `None` for type variables, dynamic types, etc.
fn nominal_type_name_for_dispatch(ty: &Type) -> Option<String> {
    match ty {
        Type::Int => Some("Int".to_string()),
        Type::Bool => Some("Bool".to_string()),
        Type::String => Some("String".to_string()),
        Type::Float => Some("Float".to_string()),
        Type::Char => Some("Char".to_string()),
        Type::Sum(s) => Some(s.name.clone()),
        Type::Record(r) => Some(r.name.clone()),
        _ => None,
    }
}

/// Remove functions that contain `Unsupported` instructions, plus any function
/// that (transitively) calls one of those removed functions.
///
/// This handles two cases:
/// - Direct: generic functions with unresolvable trait dispatch produce `Unsupported`
///   instructions directly (e.g. `Encode.encode(x: a)` where `a` is a free type var).
/// - Transitive: concrete wrapper functions (e.g. `Decode.List.decode`) that call a
///   removed generic helper (e.g. `decode_list`) don't contain `Unsupported` themselves
///   but would cause a codegen "unknown function" error if kept.
fn filter_unsupported_functions_transitive(functions: Vec<MirFunction>) -> Vec<MirFunction> {
    fn has_unsupported(f: &MirFunction) -> bool {
        f.blocks
            .iter()
            .any(|b| b.instructions.iter().any(|i| matches!(i, MirInst::Unsupported { .. })))
    }

    fn local_refs(f: &MirFunction) -> impl Iterator<Item = &str> {
        f.blocks.iter().flat_map(|b| {
            b.instructions.iter().flat_map(|i| {
                let mut names: Vec<&str> = Vec::new();
                match i {
                    MirInst::Call { callee: MirCallee::Local(name), .. } => {
                        names.push(name.as_str());
                    }
                    MirInst::FunctionRef { function, .. } => {
                        names.push(function.as_str());
                    }
                    _ => {}
                }
                names.into_iter()
            })
        })
    }

    let debug = std::env::var("KEA_DEBUG_FILTER").is_ok();

    // Seed with directly-unsupported function names.
    let mut unsupported: BTreeSet<String> = functions
        .iter()
        .filter(|f| has_unsupported(f))
        .map(|f| {
            if debug { eprintln!("[filter] directly unsupported: {}", f.name); }
            f.name.clone()
        })
        .collect();

    // Fixed-point: keep adding callers of unsupported functions.
    loop {
        let before = unsupported.len();
        for f in &functions {
            if unsupported.contains(&f.name) {
                continue;
            }
            let bad_callee = local_refs(f).find(|callee| unsupported.contains(*callee));
            if let Some(callee) = bad_callee {
                if debug { eprintln!("[filter] transitively unsupported: {} (calls {})", f.name, callee); }
                unsupported.insert(f.name.clone());
            }
        }
        if unsupported.len() == before {
            break;
        }
    }

    // Never filter out `main` if it *directly* contains an Unsupported instruction.
    // Codegen will surface the detail (e.g. "requires simple variable argument patterns")
    // rather than the opaque "unknown function `main`" error.
    // Only transitively-unsupported `main` functions (those that merely call an unsupported
    // helper) are still filtered normally, to avoid spurious codegen "unknown callee" errors.
    let main_directly_unsupported = functions
        .iter()
        .any(|f| f.name == "main" && has_unsupported(f));

    functions
        .into_iter()
        .filter(|f| {
            let keep_as_main = main_directly_unsupported && f.name == "main";
            keep_as_main || !unsupported.contains(&f.name)
        })
        .collect()
}

/// Attempt to resolve a `Trait.method` call to a concrete `Trait.TypeName.method`
/// implementation by inspecting argument and return types.
///
/// Resolution order:
/// 1. First argument type: `Encode.encode(x: Point)` → `Encode.Point.encode`
/// 2. Return type (unwrapping Option/Result wrappers):
///    `Decode.decode(j: Json) -> Option Point` → `Decode.Point.decode`
///
/// This handles both encoder dispatch (first-arg) and decoder dispatch (return-type)
/// without requiring dictionary passing.
fn try_resolve_trait_dispatch_callee(
    name: &str,
    args: &[kea_hir::HirExpr],
    known_function_types: &BTreeMap<String, Type>,
    var_types: Option<&BTreeMap<String, Type>>,
) -> Option<String> {
    // Only handle `Trait.method` (exactly one dot, e.g. `Encode.encode`).
    // Skip `Trait.Type.method` forms (already fully qualified).
    let (trait_prefix, method) = name.rsplit_once('.')?;
    if trait_prefix.contains('.') {
        return None;
    }
    // Strategy 1: dispatch on the first argument's concrete type.
    // When the HirExpr type is Dynamic (common in monomorphized functions where
    // the HIR didn't propagate the concrete type into argument nodes), fall back
    // to var_types (parameter bindings) or the SumConstructor sum_type (inline
    // list/sum literals like `[1,2,3]`).
    if let Some(first_arg) = args.first() {
        let type_name = if !matches!(first_arg.ty, Type::Dynamic) {
            nominal_type_name_for_dispatch(&first_arg.ty)
        } else {
            match &first_arg.kind {
                kea_hir::HirExprKind::Var(var_name) => var_types
                    .and_then(|vt| vt.get(var_name.as_str()))
                    .and_then(nominal_type_name_for_dispatch),
                kea_hir::HirExprKind::SumConstructor { sum_type, .. } => {
                    Some(sum_type.clone())
                }
                _ => None,
            }
        };
        if let Some(type_name) = type_name {
            let candidate = format!("{trait_prefix}.{type_name}.{method}");
            if known_function_types.contains_key(&candidate) {
                return Some(candidate);
            }
        }
    }
    // Strategy 2: dispatch on the return type (used by Decode.decode which
    // takes a Json input but dispatches on the output type).
    // Accepts any type arg as candidate.
    None
}

/// Attempt to resolve a `Trait.method` call using the expected return type.
///
/// Used for decode-style dispatch: `Decode.decode(j) -> Option T` resolves to
/// `Decode.T.decode`. The call-site return type `ret_ty` is passed in.
fn try_resolve_trait_dispatch_callee_by_ret(
    name: &str,
    ret_ty: &Type,
    known_function_types: &BTreeMap<String, Type>,
) -> Option<String> {
    let (trait_prefix, method) = name.rsplit_once('.')?;
    if trait_prefix.contains('.') {
        return None;
    }
    // Unwrap Option/Result wrapper to get the inner concrete type.
    let inner_ty = unwrap_option_type(ret_ty).or(Some(ret_ty))?;
    let type_name = nominal_type_name_for_dispatch(inner_ty)?;
    let candidate = format!("{trait_prefix}.{type_name}.{method}");
    known_function_types.contains_key(&candidate).then_some(candidate)
}

/// If `ty` is `Option T`, return `T`. Otherwise return `None`.
fn unwrap_option_type(ty: &Type) -> Option<&Type> {
    let Type::Sum(sum) = ty else { return None };
    if sum.name != "Option" || sum.type_args.len() != 1 {
        return None;
    }
    Some(&sum.type_args[0])
}

fn collect_import_aliases(module: &HirModule) -> BTreeMap<String, String> {
    let mut aliases = BTreeMap::new();
    for decl in &module.declarations {
        let HirDecl::Raw(DeclKind::Import(import)) = decl else {
            continue;
        };
        let module_path = import.module.node.clone();
        let alias = import
            .alias
            .as_ref()
            .map(|alias| alias.node.clone())
            .unwrap_or_else(|| {
                module_path
                    .rsplit('.')
                    .next()
                    .unwrap_or(module_path.as_str())
                    .to_string()
            });
        aliases.insert(alias, module_path);
    }
    aliases
}

fn extend_namespaced_set_with_import_aliases(
    symbols: &mut BTreeSet<String>,
    import_aliases: &BTreeMap<String, String>,
) {
    let originals = symbols.iter().cloned().collect::<Vec<_>>();
    for (alias, module_path) in import_aliases {
        let prefix = format!("{module_path}.");
        for original in &originals {
            if let Some(rest) = original.strip_prefix(&prefix) {
                symbols.insert(format!("{alias}.{rest}"));
            }
        }
    }
}

fn extend_namespaced_map_with_import_aliases<T: Clone>(
    symbols: &mut BTreeMap<String, T>,
    import_aliases: &BTreeMap<String, String>,
) {
    let originals = symbols
        .iter()
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect::<Vec<_>>();
    for (alias, module_path) in import_aliases {
        let prefix = format!("{module_path}.");
        for (original, value) in &originals {
            if let Some(rest) = original.strip_prefix(&prefix) {
                symbols.insert(format!("{alias}.{rest}"), value.clone());
            }
        }
    }
}

fn collect_namespaced_alias_targets<'a>(
    names: impl Iterator<Item = &'a String>,
    import_aliases: &BTreeMap<String, String>,
) -> BTreeMap<String, String> {
    let mut targets = BTreeMap::new();
    let originals = names.cloned().collect::<Vec<_>>();
    for (alias, module_path) in import_aliases {
        let prefix = format!("{module_path}.");
        for original in &originals {
            if let Some(rest) = original.strip_prefix(&prefix) {
                targets.insert(format!("{alias}.{rest}"), original.clone());
            }
        }
    }
    targets
}

fn collect_intrinsic_symbols(module: &HirModule) -> BTreeMap<String, String> {
    let mut symbols = BTreeMap::new();
    for decl in &module.declarations {
        match decl {
            HirDecl::Raw(DeclKind::Function(fn_decl)) => {
                if let Some(symbol) = intrinsic_symbol_from_annotations(&fn_decl.annotations) {
                    symbols.insert(fn_decl.name.node.clone(), symbol);
                }
            }
            HirDecl::Raw(DeclKind::ExprFn(expr_decl)) => {
                if let Some(symbol) = intrinsic_symbol_from_annotations(&expr_decl.annotations) {
                    symbols.insert(expr_decl.name.node.clone(), symbol);
                }
            }
            _ => {}
        }
    }
    symbols
}

fn intrinsic_symbol_from_annotations(annotations: &[kea_ast::Annotation]) -> Option<String> {
    for annotation in annotations {
        if annotation.name.node != "intrinsic" {
            continue;
        }
        if annotation.args.len() != 1 {
            continue;
        }
        if let kea_ast::ExprKind::Lit(kea_ast::Lit::String(symbol)) = &annotation.args[0].value.node
        {
            return Some(symbol.clone());
        }
    }
    None
}

fn collect_lambda_factory_templates(
    module: &HirModule,
    known_functions: &BTreeSet<String>,
) -> BTreeMap<String, LambdaFactoryTemplate> {
    let mut templates = BTreeMap::new();
    for decl in &module.declarations {
        let HirDecl::Function(function) = decl else {
            continue;
        };
        let HirExprKind::Lambda {
            params: lambda_params,
            body: lambda_body,
        } = &function.body.kind
        else {
            continue;
        };

        let outer_params = function
            .params
            .iter()
            .filter_map(|param| param.name.clone())
            .collect::<Vec<_>>();
        if outer_params.len() != function.params.len() {
            continue;
        }
        let outer_param_set = outer_params.iter().cloned().collect::<BTreeSet<_>>();

        let mut var_refs = BTreeSet::new();
        collect_hir_var_refs(lambda_body, &mut var_refs);
        for param_name in lambda_params.iter().filter_map(|param| param.name.as_ref()) {
            var_refs.remove(param_name);
        }
        var_refs.retain(|name| !known_functions.contains(name) && !is_namespaced_symbol_name(name));
        if !var_refs.iter().all(|name| outer_param_set.contains(name)) {
            continue;
        }
        let captures = outer_params
            .iter()
            .filter(|name| var_refs.contains(*name))
            .cloned()
            .collect::<Vec<_>>();

        templates.insert(
            function.name.clone(),
            LambdaFactoryTemplate {
                outer_params,
                lambda_params: lambda_params.clone(),
                lambda_body: lambda_body.as_ref().clone(),
                captures,
            },
        );
    }
    templates
}

fn collect_hir_var_refs(expr: &HirExpr, refs: &mut BTreeSet<String>) {
    match &expr.kind {
        HirExprKind::Lit(_) => {}
        HirExprKind::Var(name) => {
            refs.insert(name.clone());
        }
        HirExprKind::Binary { left, right, .. } => {
            collect_hir_var_refs(left, refs);
            collect_hir_var_refs(right, refs);
        }
        HirExprKind::Unary { operand, .. } => collect_hir_var_refs(operand, refs),
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_hir_var_refs(condition, refs);
            collect_hir_var_refs(then_branch, refs);
            if let Some(else_expr) = else_branch {
                collect_hir_var_refs(else_expr, refs);
            }
        }
        HirExprKind::Call { func, args } => {
            collect_hir_var_refs(func, refs);
            for arg in args {
                collect_hir_var_refs(arg, refs);
            }
        }
        HirExprKind::Let { value, .. } => collect_hir_var_refs(value, refs),
        HirExprKind::Block(exprs) | HirExprKind::Tuple(exprs) => {
            for item in exprs {
                collect_hir_var_refs(item, refs);
            }
        }
        HirExprKind::Lambda { body, .. } => collect_hir_var_refs(body, refs),
        HirExprKind::RecordLit { fields, .. } => {
            for (_, field_expr) in fields {
                collect_hir_var_refs(field_expr, refs);
            }
        }
        HirExprKind::RecordUpdate { base, fields, .. } => {
            collect_hir_var_refs(base, refs);
            for (_, field_expr) in fields {
                collect_hir_var_refs(field_expr, refs);
            }
        }
        HirExprKind::FieldAccess { expr, .. } => collect_hir_var_refs(expr, refs),
        HirExprKind::SumConstructor { fields, .. } => {
            for field_expr in fields {
                collect_hir_var_refs(field_expr, refs);
            }
        }
        HirExprKind::SumPayloadAccess { expr, .. } => collect_hir_var_refs(expr, refs),
        HirExprKind::Catch { expr } => collect_hir_var_refs(expr, refs),
        HirExprKind::Handle {
            expr,
            clauses,
            then_clause,
        } => {
            collect_hir_var_refs(expr, refs);
            for clause in clauses {
                collect_hir_var_refs(&clause.body, refs);
            }
            if let Some(then_expr) = then_clause {
                collect_hir_var_refs(then_expr, refs);
            }
        }
        HirExprKind::Resume { value } => collect_hir_var_refs(value, refs),
        HirExprKind::Raw(_) => {}
    }
}

/// Result of splitting a non-tail clause body at the Resume node.
/// Pre-resume stmts + resume value become a tail-resumptive callback.
/// Post-resume code runs inline after the handle expression returns.
struct NonTailResumeSplit {
    pre_resume_stmts: Vec<HirExpr>,
    resume_value: HirExpr,
    resume_binding: String,
    post_resume_body: Vec<HirExpr>,
    /// Pre-resume let-bindings referenced in post-resume body.
    captured_bindings: Vec<String>,
    /// Clause arg names referenced in post-resume body.
    clause_arg_captures: Vec<String>,
}

/// Split a non-tail clause body at the `let x = resume val` point.
/// Returns None if the body doesn't contain a splittable resume.
/// `clause_arg_names` are the handler clause's argument names — if any are
/// referenced in the post-resume body, they're recorded in `clause_arg_captures`.
fn split_non_tail_resume(
    body: &HirExpr,
    clause_arg_names: &BTreeSet<String>,
) -> Option<NonTailResumeSplit> {
    let HirExprKind::Block(exprs) = &body.kind else {
        return None;
    };
    let resume_idx = exprs.iter().position(|e| {
        matches!(
            &e.kind,
            HirExprKind::Let {
                value,
                pattern: HirPattern::Var(_),
            } if matches!(value.kind, HirExprKind::Resume { .. })
        )
    })?;
    let resume_expr = &exprs[resume_idx];
    let HirExprKind::Let {
        pattern: HirPattern::Var(binding_name),
        value: resume_value_box,
    } = &resume_expr.kind
    else {
        return None;
    };
    let HirExprKind::Resume { value } = &resume_value_box.kind else {
        return None;
    };

    let pre_resume_stmts: Vec<HirExpr> = exprs[..resume_idx].to_vec();
    let post_resume_body: Vec<HirExpr> = exprs[resume_idx + 1..].to_vec();
    if post_resume_body.is_empty() {
        return None;
    }

    let mut pre_bound = BTreeSet::new();
    for stmt in &pre_resume_stmts {
        if let HirExprKind::Let {
            pattern: HirPattern::Var(name),
            ..
        } = &stmt.kind
        {
            pre_bound.insert(name.clone());
        }
    }
    let mut post_refs = BTreeSet::new();
    for expr in &post_resume_body {
        collect_hir_var_refs(expr, &mut post_refs);
    }
    let captured_bindings: Vec<String> = pre_bound.intersection(&post_refs).cloned().collect();
    let clause_arg_captures: Vec<String> =
        clause_arg_names.intersection(&post_refs).cloned().collect();

    Some(NonTailResumeSplit {
        pre_resume_stmts,
        resume_value: value.as_ref().clone(),
        resume_binding: binding_name.clone(),
        post_resume_body,
        captured_bindings,
        clause_arg_captures,
    })
}

/// Classification of a handler clause body for callback lowering.
enum ClauseBodyClassification {
    /// Body is `resume value` or a Block ending in `resume value`.
    /// The callback_body is the expression the callback should return,
    /// with any preceding side-effect statements included.
    TailResumptive { callback_body: HirExpr },
    /// Body uses non-tail resume: `let x = resume val; post_code`.
    NonTail(NonTailResumeSplit),
    /// Body handles a Never-returning operation — no `resume`, the body's
    /// value becomes the result of the enclosing `handle` expression.
    ZeroResume { callback_body: HirExpr },
}

/// Classify a handler clause body for callback lowering.
/// Returns None if the body is neither tail-resumptive nor a valid non-tail split.
fn classify_clause_body(
    body: &HirExpr,
    clause_arg_names: &BTreeSet<String>,
    span: kea_ast::Span,
    returns_never: bool,
) -> Option<ClauseBodyClassification> {
    // Never-returning ops can't resume — body value exits the handle expression directly.
    if returns_never {
        return Some(ClauseBodyClassification::ZeroResume {
            callback_body: body.clone(),
        });
    }
    // Direct `resume value` → tail-resumptive, callback returns value
    if let HirExprKind::Resume { value } = &body.kind {
        return Some(ClauseBodyClassification::TailResumptive {
            callback_body: value.as_ref().clone(),
        });
    }
    // Block ending in `resume value` → tail-resumptive with side effects.
    // callback_body = Block(stmts_before_resume..., value).
    // This subsumes the old Log special case and any effect with
    // side-effecting code before a tail resume.
    if let HirExprKind::Block(exprs) = &body.kind
        && let Some(last) = exprs.last()
        && let HirExprKind::Resume { value } = &last.kind
    {
        let mut stmts: Vec<HirExpr> = exprs[..exprs.len() - 1].to_vec();
        stmts.push(value.as_ref().clone());
        let body_ty = value.ty.clone();
        let callback_body = if stmts.len() == 1 {
            stmts.pop().unwrap()
        } else {
            HirExpr {
                kind: HirExprKind::Block(stmts),
                ty: body_ty,
                span,
            }
        };
        return Some(ClauseBodyClassification::TailResumptive { callback_body });
    }
    // Non-tail split: `let x = resume val; post_code`
    split_non_tail_resume(body, clause_arg_names).map(ClauseBodyClassification::NonTail)
}

fn synth_lambda_type(params: &[kea_hir::HirParam], body: &HirExpr) -> Type {
    let ret_ty = match &body.kind {
        HirExprKind::Lambda {
            params: inner_params,
            body: inner_body,
        } if !matches!(body.ty, Type::Function(_)) => synth_lambda_type(inner_params, inner_body),
        _ => body.ty.clone(),
    };
    Type::Function(FunctionType::pure(
        vec![Type::Dynamic; params.len()],
        ret_ty,
    ))
}

fn collect_hir_dispatch_effect_ops(
    expr: &HirExpr,
    effect_operations: &BTreeMap<String, EffectOperationInfo>,
    out: &mut BTreeSet<String>,
) {
    match &expr.kind {
        HirExprKind::Lit(_) | HirExprKind::Var(_) | HirExprKind::Raw(_) => {}
        HirExprKind::Binary { left, right, .. } => {
            collect_hir_dispatch_effect_ops(left, effect_operations, out);
            collect_hir_dispatch_effect_ops(right, effect_operations, out);
        }
        HirExprKind::Unary { operand, .. } => {
            collect_hir_dispatch_effect_ops(operand, effect_operations, out)
        }
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_hir_dispatch_effect_ops(condition, effect_operations, out);
            collect_hir_dispatch_effect_ops(then_branch, effect_operations, out);
            if let Some(else_expr) = else_branch {
                collect_hir_dispatch_effect_ops(else_expr, effect_operations, out);
            }
        }
        HirExprKind::Call { func, args } => {
            if let HirExprKind::Var(name) = &func.kind
                && let Some(op) = effect_operations.get(name)
                && op.effect != "Fail"
                && !is_direct_capability_effect(&op.effect)
            {
                out.insert(format!("{}.{}", op.effect, op.operation));
            }
            collect_hir_dispatch_effect_ops(func, effect_operations, out);
            for arg in args {
                collect_hir_dispatch_effect_ops(arg, effect_operations, out);
            }
        }
        HirExprKind::Let { value, .. } => {
            collect_hir_dispatch_effect_ops(value, effect_operations, out)
        }
        HirExprKind::Block(exprs) | HirExprKind::Tuple(exprs) => {
            for item in exprs {
                collect_hir_dispatch_effect_ops(item, effect_operations, out);
            }
        }
        HirExprKind::Lambda { body, .. } => {
            collect_hir_dispatch_effect_ops(body, effect_operations, out)
        }
        HirExprKind::RecordLit { fields, .. } => {
            for (_, field_expr) in fields {
                collect_hir_dispatch_effect_ops(field_expr, effect_operations, out);
            }
        }
        HirExprKind::RecordUpdate { base, fields, .. } => {
            collect_hir_dispatch_effect_ops(base, effect_operations, out);
            for (_, field_expr) in fields {
                collect_hir_dispatch_effect_ops(field_expr, effect_operations, out);
            }
        }
        HirExprKind::FieldAccess { expr, .. } | HirExprKind::SumPayloadAccess { expr, .. } => {
            collect_hir_dispatch_effect_ops(expr, effect_operations, out)
        }
        HirExprKind::SumConstructor { fields, .. } => {
            for field_expr in fields {
                collect_hir_dispatch_effect_ops(field_expr, effect_operations, out);
            }
        }
        HirExprKind::Catch { expr } => {
            collect_hir_dispatch_effect_ops(expr, effect_operations, out)
        }
        HirExprKind::Handle {
            expr,
            clauses,
            then_clause,
        } => {
            collect_hir_dispatch_effect_ops(expr, effect_operations, out);
            for clause in clauses {
                collect_hir_dispatch_effect_ops(&clause.body, effect_operations, out);
            }
            if let Some(then_expr) = then_clause {
                collect_hir_dispatch_effect_ops(then_expr, effect_operations, out);
            }
        }
        HirExprKind::Resume { value } => {
            collect_hir_dispatch_effect_ops(value, effect_operations, out)
        }
    }
}

/// Collect dispatch effect keys required by directly-called known functions.
///
/// When a lambda body calls a named function (e.g. `IO.println`), that function
/// may itself require dispatch effect cells (e.g. `IO.stdout`) as trailing params.
/// The calling lambda therefore also needs those cells available, either captured
/// into the closure or received as trailing params.
///
/// This is particularly important for handler clause callbacks whose synthesised
/// type is `EffectRow::pure()` — `dispatch_effects_for_effect_row` returns nothing
/// for them, but the body may call IO/Clock/etc. functions that need dispatch cells.
fn collect_callee_known_dispatch_effects(
    expr: &HirExpr,
    known_dispatch_effects: &BTreeMap<String, Vec<String>>,
    out: &mut BTreeSet<String>,
) {
    match &expr.kind {
        HirExprKind::Lit(_) | HirExprKind::Raw(_) => {}
        HirExprKind::Var(_) => {}
        HirExprKind::Binary { left, right, .. } => {
            collect_callee_known_dispatch_effects(left, known_dispatch_effects, out);
            collect_callee_known_dispatch_effects(right, known_dispatch_effects, out);
        }
        HirExprKind::Unary { operand, .. } => {
            collect_callee_known_dispatch_effects(operand, known_dispatch_effects, out)
        }
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_callee_known_dispatch_effects(condition, known_dispatch_effects, out);
            collect_callee_known_dispatch_effects(then_branch, known_dispatch_effects, out);
            if let Some(else_expr) = else_branch {
                collect_callee_known_dispatch_effects(else_expr, known_dispatch_effects, out);
            }
        }
        HirExprKind::Call { func, args } => {
            // Add dispatch effects of the directly-called function.
            if let HirExprKind::Var(name) = &func.kind
                && let Some(callee_effects) = known_dispatch_effects.get(name)
            {
                out.extend(callee_effects.iter().cloned());
            }
            collect_callee_known_dispatch_effects(func, known_dispatch_effects, out);
            for arg in args {
                collect_callee_known_dispatch_effects(arg, known_dispatch_effects, out);
            }
        }
        HirExprKind::Let { value, .. } => {
            collect_callee_known_dispatch_effects(value, known_dispatch_effects, out)
        }
        HirExprKind::Block(exprs) | HirExprKind::Tuple(exprs) => {
            for item in exprs {
                collect_callee_known_dispatch_effects(item, known_dispatch_effects, out);
            }
        }
        HirExprKind::Lambda { .. } => {
            // Don't recurse into nested lambdas — they have their own dispatch context.
        }
        HirExprKind::RecordLit { fields, .. } => {
            for (_, field_expr) in fields {
                collect_callee_known_dispatch_effects(field_expr, known_dispatch_effects, out);
            }
        }
        HirExprKind::RecordUpdate { base, fields, .. } => {
            collect_callee_known_dispatch_effects(base, known_dispatch_effects, out);
            for (_, field_expr) in fields {
                collect_callee_known_dispatch_effects(field_expr, known_dispatch_effects, out);
            }
        }
        HirExprKind::FieldAccess { expr, .. } | HirExprKind::SumPayloadAccess { expr, .. } => {
            collect_callee_known_dispatch_effects(expr, known_dispatch_effects, out)
        }
        HirExprKind::SumConstructor { fields, .. } => {
            for field_expr in fields {
                collect_callee_known_dispatch_effects(field_expr, known_dispatch_effects, out);
            }
        }
        HirExprKind::Catch { expr } => {
            collect_callee_known_dispatch_effects(expr, known_dispatch_effects, out)
        }
        HirExprKind::Handle {
            expr,
            clauses,
            then_clause,
        } => {
            collect_callee_known_dispatch_effects(expr, known_dispatch_effects, out);
            for clause in clauses {
                collect_callee_known_dispatch_effects(&clause.body, known_dispatch_effects, out);
            }
            if let Some(then_expr) = then_clause {
                collect_callee_known_dispatch_effects(then_expr, known_dispatch_effects, out);
            }
        }
        HirExprKind::Resume { value } => {
            collect_callee_known_dispatch_effects(value, known_dispatch_effects, out)
        }
    }
}

/// Returns `true` if `body` contains a `Fail` effect call that is not
/// protected by an inner `catch` or a nested `handle` that handles `Fail`.
///
/// Used to detect handler clause callbacks whose bodies would silently trap
/// at runtime: `Fail` operations cannot propagate upward through the pure
/// callback ABI (the callback is synthesised with `EffectRow::pure()`).
fn hir_body_has_residual_fail(
    body: &HirExpr,
    effect_ops: &BTreeMap<String, EffectOperationInfo>,
) -> bool {
    match &body.kind {
        // A call is the primary detection point.
        HirExprKind::Call { func, args } => {
            let func_calls_fail = match &func.kind {
                // Direct effect-op call: Fail.fail or any other Fail-labelled op.
                HirExprKind::Var(name) => {
                    effect_ops.get(name).is_some_and(|op| op.effect == "Fail")
                        || uses_fail_result_abi_from_type(&func.ty)
                }
                _ => uses_fail_result_abi_from_type(&func.ty),
            };
            func_calls_fail
                || hir_body_has_residual_fail(func, effect_ops)
                || args.iter().any(|a| hir_body_has_residual_fail(a, effect_ops))
        }
        // `catch` swallows Fail — do NOT recurse into it.
        HirExprKind::Catch { .. } => false,
        // Leaves with no sub-expressions.
        HirExprKind::Lit(_) | HirExprKind::Var(_) | HirExprKind::Raw(_) => false,
        // Structural / compound forms — recurse.
        HirExprKind::Binary { left, right, .. } => {
            hir_body_has_residual_fail(left, effect_ops)
                || hir_body_has_residual_fail(right, effect_ops)
        }
        HirExprKind::Unary { operand, .. } => hir_body_has_residual_fail(operand, effect_ops),
        HirExprKind::Block(exprs) | HirExprKind::Tuple(exprs) => {
            exprs.iter().any(|e| hir_body_has_residual_fail(e, effect_ops))
        }
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            hir_body_has_residual_fail(condition, effect_ops)
                || hir_body_has_residual_fail(then_branch, effect_ops)
                || else_branch
                    .as_ref()
                    .is_some_and(|e| hir_body_has_residual_fail(e, effect_ops))
        }
        HirExprKind::Let { value, .. } => hir_body_has_residual_fail(value, effect_ops),
        HirExprKind::Lambda { body, .. } => hir_body_has_residual_fail(body, effect_ops),
        HirExprKind::Resume { value } => hir_body_has_residual_fail(value, effect_ops),
        HirExprKind::RecordLit { fields, .. } => {
            fields.iter().any(|(_, e)| hir_body_has_residual_fail(e, effect_ops))
        }
        HirExprKind::RecordUpdate { base, fields, .. } => {
            hir_body_has_residual_fail(base, effect_ops)
                || fields.iter().any(|(_, e)| hir_body_has_residual_fail(e, effect_ops))
        }
        HirExprKind::FieldAccess { expr, .. } | HirExprKind::SumPayloadAccess { expr, .. } => {
            hir_body_has_residual_fail(expr, effect_ops)
        }
        HirExprKind::SumConstructor { fields, .. } => {
            fields.iter().any(|e| hir_body_has_residual_fail(e, effect_ops))
        }
        // Nested handle: if any clause handles Fail, the handled expression's
        // Fail calls are captured there — don't recurse into `expr`.  Clause
        // bodies and the then-clause are still scanned.
        HirExprKind::Handle {
            expr,
            clauses,
            then_clause,
        } => {
            let inner_handles_fail = clauses.iter().any(|c| c.effect == "Fail");
            (!inner_handles_fail && hir_body_has_residual_fail(expr, effect_ops))
                || clauses
                    .iter()
                    .filter(|c| c.effect != "Fail")
                    .any(|c| hir_body_has_residual_fail(&c.body, effect_ops))
                || then_clause
                    .as_ref()
                    .is_some_and(|t| hir_body_has_residual_fail(t, effect_ops))
        }
    }
}

fn block_tail_ref_sets(exprs: &[HirExpr]) -> Vec<BTreeSet<String>> {
    let mut suffix = vec![BTreeSet::new(); exprs.len() + 1];
    for idx in (0..exprs.len()).rev() {
        suffix[idx] = suffix[idx + 1].clone();
        let mut refs = BTreeSet::new();
        collect_hir_var_refs(&exprs[idx], &mut refs);
        suffix[idx].extend(refs);
    }
    suffix
}

fn uses_fail_result_abi_from_type(ty: &Type) -> bool {
    match ty {
        Type::Function(ft) => {
            ft.effects.row.rest.is_none()
                && !ft.effects.row.fields.is_empty()
                && ft
                    .effects
                    .row
                    .fields
                    .iter()
                    .all(|(label, _)| label.as_str() == "Fail")
                && ft.ret.as_result().is_none()
        }
        _ => false,
    }
}

fn collect_layout_metadata(raw_decl: &DeclKind, layouts: &mut MirLayoutCatalog) {
    match raw_decl {
        DeclKind::RecordDef(record) => layouts.records.push(MirRecordLayout {
            name: record.name.node.clone(),
            is_unboxed: record
                .annotations
                .iter()
                .any(|annotation| annotation.name.node == "unboxed"),
            fields: record
                .fields
                .iter()
                .map(|(field, annotation)| MirRecordFieldLayout {
                    name: field.node.clone(),
                    annotation: annotation.clone(),
                })
                .collect(),
        }),
        DeclKind::TypeDef(sum) => layouts.sums.push(MirSumLayout {
            name: sum.name.node.clone(),
            variants: sum
                .variants
                .iter()
                .enumerate()
                .map(|(tag, variant)| MirVariantLayout {
                    name: variant.name.node.clone(),
                    tag: tag as u32,
                    fields: variant
                        .fields
                        .iter()
                        .map(|field| MirVariantFieldLayout {
                            name: field.name.as_ref().map(|name| name.node.clone()),
                            annotation: field.ty.node.clone(),
                        })
                        .collect(),
                })
                .collect(),
        }),
        _ => {}
    }
}

fn seed_builtin_sum_layouts(layouts: &mut MirLayoutCatalog) {
    let has_option = layouts.sums.iter().any(|sum| sum.name == "Option");
    if !has_option {
        // Tag order matches option.kea source: None=tag0 (first), Some=tag1 (second).
        layouts.sums.push(MirSumLayout {
            name: "Option".to_string(),
            variants: vec![
                MirVariantLayout {
                    name: "None".to_string(),
                    tag: 0,
                    fields: vec![],
                },
                MirVariantLayout {
                    name: "Some".to_string(),
                    tag: 1,
                    fields: vec![MirVariantFieldLayout {
                        name: None,
                        annotation: kea_ast::TypeAnnotation::Named("Dynamic".to_string()),
                    }],
                },
            ],
        });
    }

    let has_result = layouts.sums.iter().any(|sum| sum.name == "Result");
    if !has_result {
        layouts.sums.push(MirSumLayout {
            name: "Result".to_string(),
            variants: vec![
                MirVariantLayout {
                    name: "Ok".to_string(),
                    tag: 0,
                    fields: vec![MirVariantFieldLayout {
                        name: None,
                        annotation: kea_ast::TypeAnnotation::Named("Dynamic".to_string()),
                    }],
                },
                MirVariantLayout {
                    name: "Err".to_string(),
                    tag: 1,
                    fields: vec![MirVariantFieldLayout {
                        name: None,
                        annotation: kea_ast::TypeAnnotation::Named("Dynamic".to_string()),
                    }],
                },
            ],
        });
    }
}

fn seed_anon_record_layouts(module: &HirModule, layouts: &mut MirLayoutCatalog) {
    let mut known = layouts
        .records
        .iter()
        .map(|record| record.name.clone())
        .collect::<BTreeSet<_>>();
    for decl in &module.declarations {
        let HirDecl::Function(function) = decl else {
            continue;
        };
        collect_anon_record_layouts_from_expr(&function.body, layouts, &mut known);
    }
}

fn collect_anon_record_layouts_from_expr(
    expr: &HirExpr,
    layouts: &mut MirLayoutCatalog,
    known: &mut BTreeSet<String>,
) {
    match &expr.kind {
        HirExprKind::Lit(_) | HirExprKind::Var(_) => {}
        HirExprKind::RecordLit { fields, .. } => {
            for (_, field_expr) in fields {
                collect_anon_record_layouts_from_expr(field_expr, layouts, known);
            }
        }
        HirExprKind::RecordUpdate { base, fields, .. } => {
            collect_anon_record_layouts_from_expr(base, layouts, known);
            for (_, field_expr) in fields {
                collect_anon_record_layouts_from_expr(field_expr, layouts, known);
            }
        }
        HirExprKind::SumConstructor { fields, .. } => {
            for field_expr in fields {
                collect_anon_record_layouts_from_expr(field_expr, layouts, known);
            }
        }
        HirExprKind::Tuple(fields) => {
            for field_expr in fields {
                collect_anon_record_layouts_from_expr(field_expr, layouts, known);
            }
            let layout_name = tuple_layout_name(fields.len());
            if known.insert(layout_name.clone()) {
                layouts.records.push(MirRecordLayout {
                    name: layout_name,
                    is_unboxed: false,
                    fields: (0..fields.len())
                        .map(|index| MirRecordFieldLayout {
                            name: index.to_string(),
                            annotation: TypeAnnotation::Named("Dynamic".to_string()),
                        })
                        .collect(),
                });
            }
        }
        HirExprKind::SumPayloadAccess { expr, .. }
        | HirExprKind::FieldAccess { expr, .. }
        | HirExprKind::Catch { expr } => {
            collect_anon_record_layouts_from_expr(expr, layouts, known);
        }
        HirExprKind::Handle {
            expr,
            clauses,
            then_clause,
        } => {
            collect_anon_record_layouts_from_expr(expr, layouts, known);
            for clause in clauses {
                collect_anon_record_layouts_from_expr(&clause.body, layouts, known);
            }
            if let Some(then_expr) = then_clause {
                collect_anon_record_layouts_from_expr(then_expr, layouts, known);
            }
        }
        HirExprKind::Resume { value } => {
            collect_anon_record_layouts_from_expr(value, layouts, known);
        }
        HirExprKind::Binary { left, right, .. } => {
            collect_anon_record_layouts_from_expr(left, layouts, known);
            collect_anon_record_layouts_from_expr(right, layouts, known);
        }
        HirExprKind::Unary { operand, .. } => {
            collect_anon_record_layouts_from_expr(operand, layouts, known);
        }
        HirExprKind::Call { func, args } => {
            collect_anon_record_layouts_from_expr(func, layouts, known);
            for arg in args {
                collect_anon_record_layouts_from_expr(arg, layouts, known);
            }
        }
        HirExprKind::Lambda { body, .. } => {
            collect_anon_record_layouts_from_expr(body, layouts, known);
        }
        HirExprKind::Let { value, .. } => {
            collect_anon_record_layouts_from_expr(value, layouts, known);
        }
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_anon_record_layouts_from_expr(condition, layouts, known);
            collect_anon_record_layouts_from_expr(then_branch, layouts, known);
            if let Some(else_expr) = else_branch {
                collect_anon_record_layouts_from_expr(else_expr, layouts, known);
            }
        }
        HirExprKind::Block(exprs) => {
            for inner in exprs {
                collect_anon_record_layouts_from_expr(inner, layouts, known);
            }
        }
        HirExprKind::Raw(raw_expr) => {
            if let AstExprKind::AnonRecord { fields, spread } = raw_expr
                && spread.is_none()
            {
                let field_names = fields
                    .iter()
                    .map(|(name, _)| name.node.clone())
                    .collect::<BTreeSet<_>>();
                let layout_name = anon_record_layout_name(&field_names);
                if known.insert(layout_name.clone()) {
                    layouts.records.push(MirRecordLayout {
                        name: layout_name,
            is_unboxed: false,
                        fields: field_names
                            .into_iter()
                            .map(|field_name| MirRecordFieldLayout {
                                name: field_name,
                                annotation: TypeAnnotation::Named("Dynamic".to_string()),
                            })
                            .collect(),
                    });
                }
            }
        }
    }
}

fn anon_record_layout_name(fields: &BTreeSet<String>) -> String {
    if fields.is_empty() {
        "__AnonRecord$empty".to_string()
    } else {
        format!(
            "__AnonRecord${}",
            fields.iter().cloned().collect::<Vec<_>>().join("$")
        )
    }
}

fn tuple_layout_name(arity: usize) -> String {
    format!("__Tuple${arity}")
}

#[allow(clippy::too_many_arguments)]
fn lower_hir_function(
    function: &HirFunction,
    layouts: &MirLayoutCatalog,
    known_functions: &BTreeSet<String>,
    known_function_types: &BTreeMap<String, Type>,
    known_function_alias_targets: &BTreeMap<String, String>,
    known_const_exprs: &BTreeMap<String, AstExprKind>,
    intrinsic_symbols: &BTreeMap<String, String>,
    effect_operations: &BTreeMap<String, EffectOperationInfo>,
    known_function_dispatch_effects: &BTreeMap<String, Vec<String>>,
    lambda_factories: &BTreeMap<String, LambdaFactoryTemplate>,
    fail_tls_wrap: bool,
) -> Vec<MirFunction> {
    let (declared_params, ret) = match &function.ty {
        Type::Function(ft) => (ft.params.clone(), ft.ret.as_ref().clone()),
        _ => (
            function.params.iter().map(|_| Type::Dynamic).collect(),
            Type::Dynamic,
        ),
    };
    let hidden_dispatch_effects = known_function_dispatch_effects
        .get(&function.name)
        .cloned()
        .unwrap_or_default();
    let mut params = declared_params.clone();
    for _ in &hidden_dispatch_effects {
        params.push(Type::Dynamic);
    }

    let mut ctx = FunctionLoweringCtx::new(
        &function.name,
        declared_params.len(),
        &hidden_dispatch_effects,
        layouts,
        known_functions,
        known_function_types,
        known_function_alias_targets,
        known_const_exprs,
        intrinsic_symbols,
        effect_operations,
        known_function_dispatch_effects,
        lambda_factories,
    );
    for (index, param) in function.params.iter().enumerate() {
        if let Some(name) = &param.name {
            ctx.vars.insert(name.clone(), MirValueId(index as u32));
            if let Some(param_ty) = declared_params.get(index) {
                ctx.var_types.insert(name.clone(), param_ty.clone());
                match param_ty {
                    Type::Record(record_ty) => {
                        ctx.var_record_types
                            .insert(name.clone(), record_ty.name.clone());
                    }
                    Type::AnonRecord(row) => {
                        if let Some(record_type) = ctx.infer_unique_record_type_for_row(row) {
                            ctx.var_record_types.insert(name.clone(), record_type);
                        }
                    }
                    Type::Tuple(items) => {
                        ctx.var_record_types
                            .insert(name.clone(), tuple_layout_name(items.len()));
                        ctx.tuple_value_types
                            .insert(MirValueId(index as u32), items.clone());
                    }
                    _ => {}
                }
            }
        }
        if let Some(param_ty) = declared_params.get(index)
            && let Some(sum_type) = ctx.infer_sum_type_from_type(param_ty)
        {
            ctx.sum_value_types
                .insert(MirValueId(index as u32), sum_type);
        }
    }
    // Entry-point functions create default capability cells (closures wrapping
    // the runtime functions) so that capability dispatch cells can be threaded
    // to callees even when no user handler is installed.
    //
    // We iterate all direct capability specs (not just those in main's concrete
    // effect row) because capability effects can propagate through row variables
    // and still be needed inside lambdas created in main's body.  The wrapper
    // functions are always generated, so creating cells for unused capabilities
    // is harmless.
    if function.name == "main" {
        for capability in DIRECT_CAPABILITIES {
            let effect = capability.effect;
            for op in effect_operations
                .values()
                .filter(|op| op.effect == effect)
                // Never-returning ops use the Direct path; no default cell needed.
                .filter(|op| !op.returns_never)
            {
                let wrapper_name = default_capability_wrapper_name(effect, &op.operation);
                let fn_ref = ctx.new_value();
                ctx.emit_inst(MirInst::FunctionRef {
                    dest: fn_ref.clone(),
                    function: wrapper_name,
                });
                let closure = ctx.new_value();
                ctx.emit_inst(MirInst::ClosureInit {
                    dest: closure.clone(),
                    entry: fn_ref,
                    captures: vec![],
                    capture_types: vec![],
                });
                ctx.active_effect_cells
                    .insert((effect.to_string(), op.operation.clone()), closure);
            }
            if let Some(plan) = handler_plan_for_effect(effect_operations, effect) {
                ctx.active_effect_handlers
                    .entry(effect.to_string())
                    .or_insert(plan);
            }
        }
    }

    let return_value = if fail_tls_wrap {
        // TLS-wrapping path: lower body through lower_catch_body_as_local_call so
        // that any residual Fail is captured, then branch on the Result and either
        // return the Ok value normally or store the Err payload in the TLS slot and
        // return a zero sentinel.  The sentinel is safe because the dispatch site
        // discards the callback return value whenever TLS is set.
        ctx.emit_fail_tls_wrapped_body(&function.body, &ret)
    } else if let HirExprKind::Lambda { params, body } = &function.body.kind {
        ctx.lower_lambda_to_closure_value(
            &function.body,
            params,
            body,
            if matches!(ret, Type::Function(_)) {
                Some(&ret)
            } else {
                None
            },
            false,
            false,
        )
    } else {
        ctx.lower_expr(&function.body)
    };
    let lifted_functions = ctx.lifted_functions.clone();
    // HIR body types are erased to Dynamic when no type annotation is available.
    // If the body lowered to None (Unit call) but the declared return type is
    // Dynamic, promote ret to Unit so that codegen emits the correct void return.
    let ret = if ret == Type::Dynamic && return_value.is_none() {
        Type::Unit
    } else {
        ret
    };
    let blocks = ctx.finish(return_value, &ret);

    let mut functions = vec![MirFunction {
        name: function.name.clone(),
        signature: MirFunctionSignature {
            params,
            ret,
            effects: function.effects.clone(),
        },
        entry: MirBlockId(0),
        blocks,
        is_fip: function.is_fip,
    }];
    functions.extend(lifted_functions);
    functions
}

#[derive(Debug, Clone)]
struct PendingBlock {
    id: MirBlockId,
    params: Vec<MirBlockParam>,
    instructions: Vec<MirInst>,
    terminator: Option<MirTerminator>,
}

struct FunctionLoweringCtx {
    function_name: String,
    layouts: MirLayoutCatalog,
    blocks: Vec<PendingBlock>,
    current_block: MirBlockId,
    vars: BTreeMap<String, MirValueId>,
    var_types: BTreeMap<String, Type>,
    local_lambdas: BTreeMap<String, LocalLambda>,
    known_functions: BTreeSet<String>,
    known_function_types: BTreeMap<String, Type>,
    known_function_alias_targets: BTreeMap<String, String>,
    known_const_exprs: BTreeMap<String, AstExprKind>,
    intrinsic_symbols: BTreeMap<String, String>,
    effect_operations: BTreeMap<String, EffectOperationInfo>,
    known_function_dispatch_effects: BTreeMap<String, Vec<String>>,
    active_effect_cells: BTreeMap<(String, String), MirValueId>,
    active_effect_handlers: BTreeMap<String, ActiveEffectHandlerPlan>,
    lambda_factories: BTreeMap<String, LambdaFactoryTemplate>,
    var_record_types: BTreeMap<String, String>,
    record_value_types: BTreeMap<MirValueId, String>,
    /// Maps a MirValueId to the element types of a tuple it holds.
    /// Used to recover correct field types when `RecordFieldLoad` is applied to
    /// a tuple whose static HIR type annotation was erased to Dynamic.
    tuple_value_types: BTreeMap<MirValueId, Vec<Type>>,
    sum_value_types: BTreeMap<MirValueId, String>,
    sum_ctor_candidates: BTreeMap<String, Vec<SumCtorCandidate>>,
    lifted_functions: Vec<MirFunction>,
    named_function_closure_entries: BTreeMap<String, String>,
    block_tail_refs_stack: Vec<BTreeSet<String>>,
    block_incoming_bindings_stack: Vec<BTreeSet<String>>,
    next_lifted_lambda_id: u32,
    next_closure_entry_id: u32,
    next_value_id: u32,
    const_lowering_stack: Vec<String>,
    const_owner_stack: Vec<String>,
    stacking_chains: BTreeMap<(String, String), StackingChain>,
    /// SumPayloadLoad result values whose extracted field type is heap-managed.
    /// Block cleanup skips releasing these to avoid double-freeing with the parent cell's
    /// destructor: SumPayloadLoad gives a borrowed reference into the parent cell; an
    /// independent Release can race with the parent's own destructor traversal.
    /// The insert_releases_for_dead_params pass already guards against releasing the parent
    /// (via the SumPayloadLoad-with-managed-field check), so neither the parent nor the
    /// extracted child is released — a conservative "safe but leaky" mode until full
    /// Perceus RC=1 uniqueness analysis is implemented.
    sum_payload_load_dests: BTreeSet<MirValueId>,
    /// Exit block for zero-resume handler clauses (Never-returning ops whose handler clause
    /// intercepts the abort and returns a value from the handle expression).
    /// Set by `lower_handle_expr` when any clause handles a Never-returning op.
    /// Dispatch code jumps here after invoking a zero-resume callback.
    active_zero_resume_exit: Option<(MirBlockId, MirValueId)>,
}

#[derive(Debug, Clone)]
struct SumCtorCandidate {
    sum_type: String,
    tag: u32,
    arity: usize,
}

#[derive(Debug, Clone)]
struct LocalLambda {
    params: Vec<kea_hir::HirParam>,
    body: HirExpr,
    captures: Vec<CapturedBinding>,
}

#[derive(Debug, Clone)]
struct CapturedBinding {
    name: String,
    value: MirValueId,
    ty: Type,
    record_type: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HandlerCellOpLowering {
    InvokeCallback { arity: usize, returns_unit: bool },
}

#[derive(Debug, Clone, Default)]
struct ActiveEffectHandlerPlan {
    operation_lowering: BTreeMap<String, HandlerCellOpLowering>,
}

/// Tracks a callback stacking chain for a non-tail handler clause.
/// The chain cell holds a composed closure that applies post-resume transforms
/// in LIFO order. Built up per-invocation inside the callback, unwound after
/// the handle expression returns.
#[derive(Debug, Clone)]
struct StackingChain {
    chain_cell: MirValueId,
}

#[derive(Debug, Clone)]
struct VarScope {
    vars: BTreeMap<String, MirValueId>,
    var_types: BTreeMap<String, Type>,
    local_lambdas: BTreeMap<String, LocalLambda>,
    var_record_types: BTreeMap<String, String>,
    active_effect_cells: BTreeMap<(String, String), MirValueId>,
    active_effect_handlers: BTreeMap<String, ActiveEffectHandlerPlan>,
}

impl FunctionLoweringCtx {
    #[allow(clippy::too_many_arguments)]
    fn new(
        function_name: &str,
        param_count: usize,
        hidden_dispatch_effects: &[String],
        layouts: &MirLayoutCatalog,
        known_functions: &BTreeSet<String>,
        known_function_types: &BTreeMap<String, Type>,
        known_function_alias_targets: &BTreeMap<String, String>,
        known_const_exprs: &BTreeMap<String, AstExprKind>,
        intrinsic_symbols: &BTreeMap<String, String>,
        effect_operations: &BTreeMap<String, EffectOperationInfo>,
        known_function_dispatch_effects: &BTreeMap<String, Vec<String>>,
        lambda_factories: &BTreeMap<String, LambdaFactoryTemplate>,
    ) -> Self {
        let mut sum_ctor_candidates: BTreeMap<String, Vec<SumCtorCandidate>> = BTreeMap::new();
        for sum in &layouts.sums {
            for variant in &sum.variants {
                sum_ctor_candidates
                    .entry(variant.name.clone())
                    .or_default()
                    .push(SumCtorCandidate {
                        sum_type: sum.name.clone(),
                        tag: variant.tag,
                        arity: variant.fields.len(),
                    });
            }
        }

        let mut active_effect_cells = BTreeMap::new();
        let mut active_effect_handlers = BTreeMap::new();
        for (idx, dispatch_op_key) in hidden_dispatch_effects.iter().enumerate() {
            let shared_cell = MirValueId((param_count + idx) as u32);
            let Some((effect, operation)) = dispatch_op_key.split_once('.') else {
                continue;
            };
            active_effect_cells.insert((effect.to_string(), operation.to_string()), shared_cell);
            if let Some(plan) = handler_plan_for_effect(effect_operations, effect) {
                active_effect_handlers
                    .entry(effect.to_string())
                    .or_insert(plan);
            }
        }

        Self {
            function_name: function_name.to_string(),
            layouts: layouts.clone(),
            blocks: vec![PendingBlock {
                id: MirBlockId(0),
                params: Vec::new(),
                instructions: Vec::new(),
                terminator: None,
            }],
            current_block: MirBlockId(0),
            vars: BTreeMap::new(),
            var_types: BTreeMap::new(),
            local_lambdas: BTreeMap::new(),
            known_functions: known_functions.clone(),
            known_function_types: known_function_types.clone(),
            known_function_alias_targets: known_function_alias_targets.clone(),
            known_const_exprs: known_const_exprs.clone(),
            intrinsic_symbols: intrinsic_symbols.clone(),
            effect_operations: effect_operations.clone(),
            known_function_dispatch_effects: known_function_dispatch_effects.clone(),
            active_effect_cells,
            active_effect_handlers,
            lambda_factories: lambda_factories.clone(),
            var_record_types: BTreeMap::new(),
            record_value_types: BTreeMap::new(),
            tuple_value_types: BTreeMap::new(),
            sum_value_types: BTreeMap::new(),
            sum_ctor_candidates,
            lifted_functions: Vec::new(),
            named_function_closure_entries: BTreeMap::new(),
            block_tail_refs_stack: Vec::new(),
            block_incoming_bindings_stack: Vec::new(),
            next_lifted_lambda_id: 0,
            next_closure_entry_id: 0,
            next_value_id: (param_count + hidden_dispatch_effects.len()) as u32,
            const_lowering_stack: Vec::new(),
            const_owner_stack: Vec::new(),
            stacking_chains: BTreeMap::new(),
            sum_payload_load_dests: BTreeSet::new(),
            active_zero_resume_exit: None,
        }
    }

    fn name_maybe_referenced_later_in_block(&self, name: &str) -> bool {
        self.block_tail_refs_stack
            .last()
            .is_some_and(|refs| refs.contains(name))
    }

    fn name_captured_from_outer_block_scope(&self, name: &str) -> bool {
        self.block_incoming_bindings_stack
            .last()
            .is_none_or(|names| names.contains(name))
    }

    fn canonical_known_function_name(&self, name: &str) -> String {
        self.known_function_alias_targets
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    fn drop_local_binding_metadata(&mut self, name: &str) {
        self.vars.remove(name);
        self.var_types.remove(name);
        self.var_record_types.remove(name);
        self.local_lambdas.remove(name);
    }

    fn allocate_generated_closure_entry_name(&mut self, stem: &str) -> String {
        let id = self.next_closure_entry_id;
        self.next_closure_entry_id = self.next_closure_entry_id.saturating_add(1);
        format!("{}::closure_entry${id}${}", self.function_name, stem)
    }

    fn register_generated_function(&mut self, function: MirFunction) {
        let signature_ty = Type::Function(FunctionType {
            params: function.signature.params.clone(),
            ret: Box::new(function.signature.ret.clone()),
            effects: function.signature.effects.clone(),
        });
        self.known_functions.insert(function.name.clone());
        self.known_function_types
            .insert(function.name.clone(), signature_ty);
        self.lifted_functions.push(function);
    }

    /// Create an identity closure `|x| x` for use as the initial chain value
    /// in callback stacking. Returns a closure MirValueId.
    fn create_identity_closure(&mut self, _value_type: &Type) -> Option<MirValueId> {
        let entry_name = self.allocate_generated_closure_entry_name("chain_identity");
        // Entry function: (env: Dynamic, x: Dynamic) -> Dynamic
        // env = param 0 (unused, always I64 closure ptr), x = param 1 — just return x.
        // Uses Dynamic because chain values flow through opaque cell stores/loads.
        let identity_fn = MirFunction {
            name: entry_name.clone(),
            signature: MirFunctionSignature {
                params: vec![Type::Dynamic, Type::Dynamic],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: Vec::new(),
                instructions: vec![],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(1)),
                },
            }],
        };
        self.register_generated_function(identity_fn);
        self.emit_closure_value(entry_name, vec![])
    }

    /// Build a post-resume chain function for callback stacking.
    ///
    /// Creates a synthetic function with params `[prev_chain, resume_binding, extra_captures...]`
    /// whose body is: `prev_chain(post_resume_transform(resume_binding))`.
    /// `extra_capture_names` are clause args or other values needed by the post-resume body.
    /// Returns the closure entry wrapper name for use with `emit_closure_value`.
    fn build_post_resume_chain_function(
        &mut self,
        effect: &str,
        operation: &str,
        split: &NonTailResumeSplit,
        extra_capture_names: &[String],
        _clause_return_type: &Type,
        span: kea_ast::Span,
    ) -> Option<String> {
        // Param order must match closure wrapper: captures first, then call params.
        // Wrapper passes: [capture_0=prev_chain, capture_1..N=extras, call_param_0=result]
        let mut params = vec![kea_hir::HirParam {
            name: Some("__prev_chain".to_string()),
            span,
        }];
        for name in extra_capture_names {
            params.push(kea_hir::HirParam {
                name: Some(name.clone()),
                span,
            });
        }
        params.push(kea_hir::HirParam {
            name: Some(split.resume_binding.clone()),
            span,
        });

        // Body: post_resume_body exprs, with last wrapped in Call(prev_chain, [expr])
        let mut body_exprs: Vec<HirExpr> = split.post_resume_body.clone();
        let last_expr = body_exprs.pop().unwrap_or_else(|| HirExpr {
            kind: HirExprKind::Var(split.resume_binding.clone()),
            ty: Type::Dynamic,
            span,
        });
        body_exprs.push(HirExpr {
            kind: HirExprKind::Call {
                func: Box::new(HirExpr {
                    kind: HirExprKind::Var("__prev_chain".to_string()),
                    ty: Type::Dynamic,
                    span,
                }),
                args: vec![last_expr],
            },
            ty: Type::Dynamic,
            span,
        });

        let body = HirExpr {
            kind: HirExprKind::Block(body_exprs),
            ty: Type::Dynamic,
            span,
        };

        let param_types: Vec<Type> = params.iter().map(|_| Type::Dynamic).collect();
        let fn_name = format!(
            "{}::__post_resume_{effect}_{operation}${}",
            self.function_name, self.next_lifted_lambda_id
        );
        self.next_lifted_lambda_id = self.next_lifted_lambda_id.saturating_add(1);

        let synthetic_fn = HirFunction {
            name: fn_name.clone(),
            params: params.clone(),
            body,
            ty: Type::Function(FunctionType {
                params: param_types,
                ret: Box::new(Type::Dynamic),
                effects: EffectRow::pure(),
            }),
            effects: EffectRow::pure(),
            span,
            is_fip: false,
        };

        let lowered_functions = lower_hir_function(
            &synthetic_fn,
            &self.layouts,
            &self.known_functions,
            &self.known_function_types,
            &self.known_function_alias_targets,
            &self.known_const_exprs,
            &self.intrinsic_symbols,
            &self.effect_operations,
            &self.known_function_dispatch_effects,
            &self.lambda_factories,
            false,
        );
        for f in lowered_functions {
            self.register_generated_function(f);
        }

        // Closure entry: captures = [prev_chain, extra_0, ...], call param = [result]
        let n_extra = extra_capture_names.len();
        let capture_types: Vec<Type> = std::iter::repeat_n(Type::Dynamic, 1 + n_extra).collect();
        let entry_name = self.allocate_generated_closure_entry_name("post_resume");
        let wrapper = self.build_closure_entry_wrapper(
            entry_name.clone(),
            fn_name,
            capture_types,       // captures: prev_chain + extras
            vec![Type::Dynamic], // call param: result (Dynamic — chain value flows through opaque cells)
            Vec::new(),
            Vec::new(),
            Type::Dynamic,
            EffectRow::pure(),
            false,
        );
        self.register_generated_function(wrapper);
        Some(entry_name)
    }

    /// Build a MIR callback wrapper that augments an inner callback with chain
    /// building for callback stacking. The wrapper:
    /// Wrap an inner callback with chain augmentation for non-tail resume.
    ///
    /// Allocate state cells for pre-resume bindings that are captured by
    /// the post-resume body. The callback stores into these cells; after the
    /// callback returns, chain augmentation loads the values and passes them
    /// as captures to the chain closure.
    fn allocate_pre_resume_capture_cells(
        &mut self,
        split: &NonTailResumeSplit,
        _span: kea_ast::Span,
    ) -> Vec<MirValueId> {
        let mut cells = Vec::new();
        for (i, binding) in split.captured_bindings.iter().enumerate() {
            let cell = self.new_value();
            let unit_initial = self.new_value();
            self.emit_inst(MirInst::Const {
                dest: unit_initial.clone(),
                literal: MirLiteral::Int(0),
            });
            self.emit_inst(MirInst::StateCellNew {
                dest: cell.clone(),
                initial: unit_initial,
            });
            let cell_name = format!("__capture_cell_{i}_{binding}");
            self.vars.insert(cell_name.clone(), cell.clone());
            self.var_types.insert(cell_name, Type::Dynamic);
            cells.push(cell);
        }
        cells
    }

    /// Build a handler clause callback closure. Handles stateful get/put as
    /// special cases, then falls through to the general path which synthesizes
    /// a lambda from the clause args and classified callback body.
    ///
    /// Returns (callback_value, arity, returns_unit).
    #[allow(clippy::too_many_arguments)]
    fn build_clause_callback(
        &mut self,
        clause: &kea_hir::HirHandleClause,
        target_effect: &str,
        internal_state_cell: Option<&MirValueId>,
        classification: &ClauseBodyClassification,
        _pre_resume_capture_cells: &[MirValueId],
    ) -> Option<(MirValueId, usize, bool)> {
        // Stateful get/put shortcuts: only safe for simple tail-resumptive bodies
        // (direct `resume value`, not blocks with side effects before resume).
        // Bodies with side effects before resume must use the general callback path
        // to avoid silently dropping those side effects.
        if let Some(state_cell) = internal_state_cell {
            let is_simple_tail = matches!(
                classification,
                ClauseBodyClassification::TailResumptive { callback_body }
                    if !matches!(callback_body.kind, HirExprKind::Block(_))
            );
            // Zero-arg operation in stateful effect → state-get callback
            if clause.args.is_empty() && is_simple_tail {
                let callback = self.build_state_get_callback(state_cell.clone())?;
                return Some((callback, 0, false));
            }
            // State-put: 1-arg clause resuming with Unit in stateful effect
            if clause.args.len() == 1 && is_simple_tail {
                let resumes_unit = match classification {
                    ClauseBodyClassification::TailResumptive { callback_body } => {
                        matches!(callback_body.kind, HirExprKind::Lit(kea_ast::Lit::Unit))
                    }
                    ClauseBodyClassification::NonTail(split) => {
                        matches!(split.resume_value.kind, HirExprKind::Lit(kea_ast::Lit::Unit))
                    }
                    // Never-returning ops can't be state-put; fall through to general path.
                    ClauseBodyClassification::ZeroResume { .. } => false,
                };
                if resumes_unit {
                    let callback = self.build_state_put_callback(state_cell.clone())?;
                    return Some((callback, 1, true));
                }
            }
            // Other operations or complex bodies: fall through to general path
        }

        // General path: build callback from classification
        let callback_body = match classification {
            ClauseBodyClassification::TailResumptive { callback_body }
            | ClauseBodyClassification::ZeroResume { callback_body } => callback_body.clone(),
            ClauseBodyClassification::NonTail(split) => {
                let mut block_exprs = split.pre_resume_stmts.clone();
                // Inject capture_store calls for captured bindings
                for (i, binding) in split.captured_bindings.iter().enumerate() {
                    let cell_name = format!("__capture_cell_{i}_{binding}");
                    block_exprs.push(HirExpr {
                        kind: HirExprKind::Call {
                            func: Box::new(HirExpr {
                                kind: HirExprKind::Var(
                                    "__kea_internal_capture_store".to_string(),
                                ),
                                ty: Type::Dynamic,
                                span: clause.span,
                            }),
                            args: vec![
                                HirExpr {
                                    kind: HirExprKind::Var(cell_name),
                                    ty: Type::Dynamic,
                                    span: clause.span,
                                },
                                HirExpr {
                                    kind: HirExprKind::Var(binding.clone()),
                                    ty: self.var_types.get(binding).cloned().unwrap_or(Type::Dynamic),
                                    span: clause.span,
                                },
                            ],
                        },
                        ty: Type::Unit,
                        span: clause.span,
                    });
                }
                block_exprs.push(split.resume_value.clone());
                let body_ty = block_exprs.last().map_or(Type::Dynamic, |e| e.ty.clone());
                if block_exprs.len() == 1 {
                    block_exprs.pop().unwrap()
                } else {
                    HirExpr {
                        kind: HirExprKind::Block(block_exprs),
                        ty: body_ty,
                        span: clause.span,
                    }
                }
            }
        };

        // Build callback params from clause args
        let mut callback_params = Vec::with_capacity(clause.args.len());
        for arg_pattern in &clause.args {
            let HirPattern::Var(arg_name) = arg_pattern else {
                self.emit_inst(MirInst::Unsupported {
                    detail: format!(
                        "handler clause `{target_effect}.{}` requires simple variable \
                         argument patterns for callback lowering",
                        clause.operation,
                    ),
                });
                return None;
            };
            callback_params.push(kea_hir::HirParam {
                name: Some(arg_name.clone()),
                span: clause.span,
            });
        }

        // Determine callback return type
        let callback_return_ty = match &callback_body.kind {
            HirExprKind::Lambda { params, body }
                if !matches!(callback_body.ty, Type::Function(_)) =>
            {
                synth_lambda_type(params, body)
            }
            _ => callback_body.ty.clone(),
        };

        // Synthesize and lower callback lambda — use concrete arg types from
        // type checker when available (threaded through HirHandleClause.arg_types).
        let callback_ty = Type::Function(FunctionType::with_effects(
            clause.arg_types.clone(),
            callback_return_ty.clone(),
            EffectRow::pure(),
        ));
        let callback_lambda = HirExpr {
            kind: HirExprKind::Lambda {
                params: callback_params.clone(),
                body: Box::new(callback_body.clone()),
            },
            ty: callback_ty.clone(),
            span: clause.span,
        };
        let needs_tls_wrap = matches!(
            classification,
            ClauseBodyClassification::TailResumptive { .. }
                | ClauseBodyClassification::NonTail(_)
        ) && hir_body_has_residual_fail(&callback_body, &self.effect_operations);
        let Some(callback_value) = self.lower_lambda_to_closure_value(
            &callback_lambda,
            &callback_params,
            &callback_body,
            Some(&callback_ty),
            true,
            needs_tls_wrap,
        ) else {
            self.emit_inst(MirInst::Unsupported {
                detail: format!(
                    "failed to lower handler callback body for `{target_effect}.{}`",
                    clause.operation
                ),
            });
            return None;
        };

        let arity = callback_params.len();
        let returns_unit = callback_return_ty == Type::Unit;
        Some((callback_value, arity, returns_unit))
    }

    /// This is the unified entry point for all non-tail handler clause wrapping.
    /// It builds the post-resume chain function, creates the identity closure and
    /// chain cell, registers in stacking_chains, and calls build_chain_augmented_callback.
    #[allow(clippy::too_many_arguments)]
    fn wrap_with_chain_augmentation(
        &mut self,
        inner_callback: MirValueId,
        target_effect: &str,
        operation: &str,
        split: &NonTailResumeSplit,
        clause_args: &[kea_hir::HirPattern],
        clause_arg_types: &[Type],
        clause_return_type: &Type,
        pre_resume_capture_cells: &[MirValueId],
        span: kea_ast::Span,
    ) -> Option<MirValueId> {
        // Combine clause arg captures + binding captures for the chain function
        let mut all_extra_captures: Vec<String> = split.clause_arg_captures.clone();
        all_extra_captures.extend(split.captured_bindings.clone());

        let post_resume_entry = self.build_post_resume_chain_function(
            target_effect,
            operation,
            split,
            &all_extra_captures,
            clause_return_type,
            span,
        )?;

        let identity = self.create_identity_closure(clause_return_type)?;
        let chain_cell = self.new_value();
        self.emit_inst(MirInst::StateCellNew {
            dest: chain_cell.clone(),
            initial: identity,
        });
        self.stacking_chains.insert(
            (target_effect.to_string(), operation.to_string()),
            StackingChain {
                chain_cell: chain_cell.clone(),
            },
        );

        // Map clause arg capture names to their indices in the callback params
        let clause_arg_names: Vec<String> = clause_args
            .iter()
            .filter_map(|p| {
                if let kea_hir::HirPattern::Var(n) = p {
                    Some(n.clone())
                } else {
                    None
                }
            })
            .collect();
        let capture_indices: Vec<usize> = split
            .clause_arg_captures
            .iter()
            .filter_map(|name| clause_arg_names.iter().position(|n| n == name))
            .collect();

        let arity = clause_args.len();
        self.build_chain_augmented_callback(
            inner_callback,
            chain_cell,
            &post_resume_entry,
            arity,
            clause_arg_types,
            clause_return_type,
            &capture_indices,
            pre_resume_capture_cells,
        )
    }

    /// 1. Calls the inner callback to get the resume value
    /// 2. Loads the previous chain from chain_cell
    /// 3. Creates a new chain closure wrapping prev with the post-resume transform
    /// 4. Stores the new chain in chain_cell
    /// 5. Returns the resume value
    ///
    /// Returns a closure MirValueId for the augmented callback.
    #[allow(clippy::too_many_arguments)]
    fn build_chain_augmented_callback(
        &mut self,
        inner_callback: MirValueId,
        chain_cell: MirValueId,
        post_resume_entry: &str,
        arity: usize,
        clause_arg_types: &[Type],
        _clause_return_type: &Type,
        clause_arg_capture_indices: &[usize],
        binding_capture_cells: &[MirValueId],
    ) -> Option<MirValueId> {
        // Build a MIR function manually:
        // Params: [env, arg0, arg1, ..., argN-1]
        // Captures in env: [inner_callback, chain_cell, binding_cell_0, ...]
        let wrapper_fn_name = format!(
            "{}::__chain_callback${}",
            self.function_name, self.next_lifted_lambda_id
        );
        self.next_lifted_lambda_id = self.next_lifted_lambda_id.saturating_add(1);

        let mut instructions = Vec::new();
        let env_param = MirValueId(0); // closure env
        // call params are MirValueId(1) through MirValueId(arity)
        let mut next_id = 1 + arity as u32;

        // Unpack captures from env: [inner_callback, chain_cell, binding_cells...]
        let cap_inner = MirValueId(next_id);
        next_id += 1;
        instructions.push(MirInst::ClosureCaptureLoad {
            dest: cap_inner.clone(),
            closure: env_param.clone(),
            capture_index: 0,
            capture_ty: Type::Dynamic,
        });
        let cap_chain_cell = MirValueId(next_id);
        next_id += 1;
        instructions.push(MirInst::ClosureCaptureLoad {
            dest: cap_chain_cell.clone(),
            closure: env_param.clone(),
            capture_index: 1,
            capture_ty: Type::Dynamic,
        });
        let mut cap_binding_cells = Vec::new();
        for i in 0..binding_capture_cells.len() {
            let cap_cell = MirValueId(next_id);
            next_id += 1;
            instructions.push(MirInst::ClosureCaptureLoad {
                dest: cap_cell.clone(),
                closure: env_param.clone(),
                capture_index: 2 + i,
                capture_ty: Type::Dynamic,
            });
            cap_binding_cells.push(cap_cell);
        }

        // Call inner_callback(arg0, ..., argN-1) -> resume_value
        let inner_args: Vec<MirValueId> = (1..=arity as u32).map(MirValueId).collect();
        let resume_value = MirValueId(next_id);
        next_id += 1;
        // The inner callback returns the resume value. Use Dynamic for the call's
        // ret_type because even Unit resume values need to flow through the chain
        // as concrete I64 values (the chain stores/loads them as opaque data).
        instructions.push(MirInst::Call {
            callee: MirCallee::Value(cap_inner),
            args: inner_args,
            arg_types: clause_arg_types.to_vec(),
            result: Some(resume_value.clone()),
            ret_type: Type::Dynamic,
            callee_fail_result_abi: false,
            capture_fail_result: false,
            cc_manifest_id: "default".to_string(),
        });

        // After inner callback: load captured binding VALUES from cells.
        // The inner callback stored values via __kea_internal_capture_store.
        // We load the values (not cells) so each chain closure gets its own snapshot.
        let mut loaded_binding_values = Vec::new();
        for cap_cell in &cap_binding_cells {
            let loaded = MirValueId(next_id);
            next_id += 1;
            instructions.push(MirInst::StateCellLoad {
                dest: loaded.clone(),
                cell: cap_cell.clone(),
            });
            loaded_binding_values.push(loaded);
        }

        // Load prev chain from chain_cell
        let prev_chain = MirValueId(next_id);
        next_id += 1;
        instructions.push(MirInst::StateCellLoad {
            dest: prev_chain.clone(),
            cell: cap_chain_cell.clone(),
        });

        // Create new chain closure: captures = [prev_chain, clause_arg_captures..., binding_values...]
        let post_resume_entry_ref = MirValueId(next_id);
        next_id += 1;
        instructions.push(MirInst::FunctionRef {
            dest: post_resume_entry_ref.clone(),
            function: post_resume_entry.to_string(),
        });
        let mut chain_captures = vec![prev_chain];
        let mut chain_capture_types = vec![Type::Dynamic]; // prev_chain is a closure ptr
        for &idx in clause_arg_capture_indices {
            // Clause args are MirValueId(1..=arity) in the wrapper function
            chain_captures.push(MirValueId(1 + idx as u32));
            chain_capture_types.push(
                clause_arg_types.get(idx).cloned().unwrap_or(Type::Dynamic),
            );
        }
        for val in &loaded_binding_values {
            chain_captures.push(val.clone());
            // Binding values loaded from cells — use Dynamic since we don't have
            // their types threaded through (cell stores erase type info).
            chain_capture_types.push(Type::Dynamic);
        }
        let new_chain = MirValueId(next_id);
        next_id += 1;
        instructions.push(MirInst::ClosureInit {
            dest: new_chain.clone(),
            entry: post_resume_entry_ref,
            captures: chain_captures,
            capture_types: chain_capture_types,
        });

        // Store new chain in chain_cell
        instructions.push(MirInst::StateCellStore {
            cell: cap_chain_cell,
            value: new_chain,
        });

        let _ = next_id; // suppress unused warning

        // Build the wrapper MIR function
        let wrapper_fn = MirFunction {
            name: wrapper_fn_name.clone(),
            signature: MirFunctionSignature {
                params: std::iter::once(Type::Dynamic) // env (closure ptr, always I64)
                    .chain(clause_arg_types.iter().cloned()) // args with concrete types
                    .collect(),
                // Use Dynamic for ret because the chain passes resume values
                // through opaque stores/loads even when the value is Unit.
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: Vec::new(),
                instructions,
                terminator: MirTerminator::Return {
                    value: Some(resume_value),
                },
            }],
        };
        self.register_generated_function(wrapper_fn);

        // Create closure: captures = [inner_callback, chain_cell, binding_cells...]
        let mut outer_captures = vec![(inner_callback, Type::Dynamic), (chain_cell, Type::Dynamic)];
        for cell in binding_capture_cells {
            outer_captures.push((cell.clone(), Type::Dynamic));
        }
        self.emit_closure_value(wrapper_fn_name, outer_captures)
    }

    /// Build an impl function for state-get: `__state_get_impl(cell) -> Dynamic`.
    /// Plain function with explicit params — no closure env interaction.
    fn build_state_get_impl_function(&mut self) -> String {
        let impl_name = format!(
            "{}::__state_get_impl${}",
            self.function_name, self.next_lifted_lambda_id
        );
        self.next_lifted_lambda_id = self.next_lifted_lambda_id.saturating_add(1);

        // Params: [cell]
        // Body: StateCellLoad(cell) → value; return value
        let cell_param = MirValueId(0);
        let loaded_value = MirValueId(1);
        let get_impl = MirFunction {
            name: impl_name.clone(),
            signature: MirFunctionSignature {
                params: vec![Type::Dynamic],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: Vec::new(),
                instructions: vec![MirInst::StateCellLoad {
                    dest: loaded_value.clone(),
                    cell: cell_param,
                }],
                terminator: MirTerminator::Return {
                    value: Some(loaded_value),
                },
            }],
        };
        self.register_generated_function(get_impl);
        impl_name
    }

    /// Build an impl function for state-put: `__state_put_impl(cell, value) -> Dynamic`.
    /// Plain function with explicit params — no closure env interaction.
    fn build_state_put_impl_function(&mut self) -> String {
        let impl_name = format!(
            "{}::__state_put_impl${}",
            self.function_name, self.next_lifted_lambda_id
        );
        self.next_lifted_lambda_id = self.next_lifted_lambda_id.saturating_add(1);

        // Params: [cell, value]
        // Body: StateCellStore(cell, value); Const(Unit); return Unit
        let cell_param = MirValueId(0);
        let value_param = MirValueId(1);
        let unit_val = MirValueId(2);
        let put_impl = MirFunction {
            name: impl_name.clone(),
            signature: MirFunctionSignature {
                params: vec![Type::Dynamic, Type::Dynamic],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: Vec::new(),
                instructions: vec![
                    MirInst::StateCellStore {
                        cell: cell_param,
                        value: value_param,
                    },
                    MirInst::Const {
                        dest: unit_val.clone(),
                        literal: MirLiteral::Unit,
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(unit_val),
                },
            }],
        };
        self.register_generated_function(put_impl);
        impl_name
    }

    /// Build a state-get callback via the proven closure pipeline.
    /// impl function → entry wrapper (build_closure_entry_wrapper) → closure value.
    /// Captures = [internal_cell]. Returns closure MirValueId.
    fn build_state_get_callback(&mut self, internal_cell: MirValueId) -> Option<MirValueId> {
        let impl_name = self.build_state_get_impl_function();
        let entry_name = self.allocate_generated_closure_entry_name("state_get");
        let wrapper = self.build_closure_entry_wrapper(
            entry_name.clone(),
            impl_name,
            vec![Type::Dynamic], // captures: [cell]
            vec![],              // call params: none (zero-arg get)
            vec![],              // no dispatch effects
            vec![],              // no bound dispatch captures
            Type::Dynamic,
            EffectRow::pure(),
            false,
        );
        self.register_generated_function(wrapper);
        self.emit_closure_value(entry_name, vec![(internal_cell, Type::Dynamic)])
    }

    /// Build a state-put callback via the proven closure pipeline.
    /// impl function → entry wrapper (build_closure_entry_wrapper) → closure value.
    /// Captures = [internal_cell]. Returns closure MirValueId.
    fn build_state_put_callback(&mut self, internal_cell: MirValueId) -> Option<MirValueId> {
        let impl_name = self.build_state_put_impl_function();
        let entry_name = self.allocate_generated_closure_entry_name("state_put");
        let wrapper = self.build_closure_entry_wrapper(
            entry_name.clone(),
            impl_name,
            vec![Type::Dynamic], // captures: [cell]
            vec![Type::Dynamic], // call params: [value] (one-arg put)
            vec![],              // no dispatch effects
            vec![],              // no bound dispatch captures
            Type::Dynamic,
            EffectRow::pure(),
            false,
        );
        self.register_generated_function(wrapper);
        self.emit_closure_value(entry_name, vec![(internal_cell, Type::Dynamic)])
    }

    #[allow(clippy::too_many_arguments)]
    fn build_closure_entry_wrapper(
        &self,
        entry_name: String,
        target_name: String,
        capture_types: Vec<Type>,
        call_param_types: Vec<Type>,
        dispatch_effects: Vec<String>,
        bound_dispatch_capture_types: Vec<Type>,
        return_type: Type,
        effects: EffectRow,
        callee_fail_result_abi: bool,
    ) -> MirFunction {
        let mut instructions = Vec::new();
        let mut next_value_id = 1 + call_param_types.len() as u32 + dispatch_effects.len() as u32;
        let closure_value = MirValueId(0);

        let mut call_args = Vec::new();
        let mut call_arg_types = Vec::new();
        let mut bound_dispatch_args = Vec::new();

        for (idx, capture_ty) in capture_types.iter().enumerate() {
            let dest = MirValueId(next_value_id);
            next_value_id = next_value_id.saturating_add(1);
            instructions.push(MirInst::ClosureCaptureLoad {
                dest: dest.clone(),
                closure: closure_value.clone(),
                capture_index: idx,
                capture_ty: capture_ty.clone(),
            });
            call_args.push(dest);
            call_arg_types.push(capture_ty.clone());
        }
        for (idx, capture_ty) in bound_dispatch_capture_types.iter().enumerate() {
            let dest = MirValueId(next_value_id);
            next_value_id = next_value_id.saturating_add(1);
            instructions.push(MirInst::ClosureCaptureLoad {
                dest: dest.clone(),
                closure: closure_value.clone(),
                capture_index: capture_types.len() + idx,
                capture_ty: capture_ty.clone(),
            });
            bound_dispatch_args.push(dest);
        }

        for (idx, param_ty) in call_param_types.iter().enumerate() {
            call_args.push(MirValueId(1 + idx as u32));
            call_arg_types.push(param_ty.clone());
        }
        for dispatch_idx in 0..dispatch_effects.len() {
            call_args.push(MirValueId(
                1 + call_param_types.len() as u32 + dispatch_idx as u32,
            ));
            call_arg_types.push(Type::Dynamic);
        }
        for dispatch_value in bound_dispatch_args {
            call_args.push(dispatch_value);
            call_arg_types.push(Type::Dynamic);
        }

        let call_result = if return_type == Type::Unit {
            None
        } else {
            Some(MirValueId(next_value_id))
        };
        instructions.push(MirInst::Call {
            callee: MirCallee::Local(target_name),
            args: call_args,
            arg_types: call_arg_types,
            result: call_result.clone(),
            ret_type: return_type.clone(),
            callee_fail_result_abi,
            capture_fail_result: false,
            cc_manifest_id: "default".to_string(),
        });

        let wrapper_signature = MirFunctionSignature {
            params: std::iter::once(Type::Dynamic)
                .chain(call_param_types)
                .chain((0..dispatch_effects.len()).map(|_| Type::Dynamic))
                .collect(),
            ret: return_type,
            effects,
        };

        MirFunction {
            name: entry_name,
            signature: wrapper_signature,
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: Vec::new(),
                instructions,
                terminator: MirTerminator::Return { value: call_result },
            }],
        }
    }

    fn emit_closure_value(
        &mut self,
        entry_function: String,
        captures: Vec<(MirValueId, Type)>,
    ) -> Option<MirValueId> {
        let entry_value = self.new_value();
        self.emit_inst(MirInst::FunctionRef {
            dest: entry_value.clone(),
            function: entry_function,
        });
        let dest = self.new_value();
        let capture_values = captures.iter().map(|(value, _)| value.clone()).collect();
        let capture_types = captures.into_iter().map(|(_, ty)| ty).collect();
        self.emit_inst(MirInst::ClosureInit {
            dest: dest.clone(),
            entry: entry_value,
            captures: capture_values,
            capture_types,
        });
        Some(dest)
    }

    fn lower_named_function_to_closure_value(&mut self, name: &str) -> Option<MirValueId> {
        let canonical_name = self.canonical_known_function_name(name);
        let function_ty = self
            .known_function_types
            .get(&canonical_name)
            .or_else(|| self.known_function_types.get(name))?
            .clone();

        let Type::Function(ft) = function_ty else {
            let dest = self.new_value();
            self.emit_inst(MirInst::FunctionRef {
                dest: dest.clone(),
                function: canonical_name,
            });
            return Some(dest);
        };

        let entry_name = if let Some(existing) = self.named_function_closure_entries.get(&canonical_name)
        {
            existing.clone()
        } else {
            let entry_name = self.allocate_generated_closure_entry_name("named");
            let callee_fail_result_abi =
                uses_fail_result_abi_from_type(&Type::Function(ft.clone()));
            let dispatch_effects = self
                .known_function_dispatch_effects
                .get(&canonical_name)
                .or_else(|| self.known_function_dispatch_effects.get(name))
                .cloned()
                .unwrap_or_else(|| self.dispatch_effects_for_effect_row(&ft.effects));
            let wrapper = self.build_closure_entry_wrapper(
                entry_name.clone(),
                canonical_name.clone(),
                Vec::new(),
                ft.params.clone(),
                dispatch_effects,
                Vec::new(),
                ft.ret.as_ref().clone(),
                ft.effects.clone(),
                callee_fail_result_abi,
            );
            self.register_generated_function(wrapper);
            self.named_function_closure_entries
                .insert(canonical_name, entry_name.clone());
            entry_name
        };

        self.emit_closure_value(entry_name, Vec::new())
    }

    /// Lift a `catch` body to a local function and call it directly with
    /// `capture_fail_result: true`. This avoids the thin-closure indirect-call
    /// path that produces incorrect results on x86_64.
    fn lower_catch_body_as_local_call(&mut self, caught: &HirExpr) -> Option<MirValueId> {
        let fail_effects = EffectRow::closed(vec![(Label::new("Fail"), Type::Dynamic)]);
        // Collect captures: variables referenced in the caught expression
        // that are defined in the parent scope.
        let mut var_refs = BTreeSet::new();
        collect_hir_var_refs(caught, &mut var_refs);
        let captures: Vec<(String, Type, MirValueId)> = var_refs
            .into_iter()
            .filter(|name| self.vars.contains_key(name))
            .map(|name| {
                let ty = self.var_types.get(&name).cloned().unwrap_or(Type::Dynamic);
                let value = self
                    .vars
                    .get(&name)
                    .cloned()
                    .expect("capture values must exist in lowering scope");
                (name, ty, value)
            })
            .collect();

        let catch_fn_name = format!(
            "{}::catch${}",
            self.function_name, self.next_lifted_lambda_id
        );
        self.next_lifted_lambda_id = self.next_lifted_lambda_id.saturating_add(1);

        let lifted_params: Vec<kea_hir::HirParam> = captures
            .iter()
            .map(|(name, _, _)| kea_hir::HirParam {
                name: Some(name.clone()),
                span: caught.span,
            })
            .collect();
        let lifted_fn_ty = FunctionType::with_effects(
            captures.iter().map(|(_, ty, _)| ty.clone()).collect(),
            caught.ty.clone(),
            fail_effects.clone(),
        );
        let lifted = HirFunction {
            name: catch_fn_name.clone(),
            params: lifted_params,
            body: caught.clone(),
            ty: Type::Function(lifted_fn_ty),
            effects: fail_effects,
            span: caught.span,
            is_fip: false,
        };

        let mut known = self.known_functions.clone();
        known.insert(catch_fn_name.clone());
        let mut known_types = self.known_function_types.clone();
        known_types.insert(catch_fn_name.clone(), lifted.ty.clone());

        // Collect dispatch effects from the caught body.
        let mut dispatch_set = BTreeSet::new();
        collect_hir_dispatch_effect_ops(caught, &self.effect_operations, &mut dispatch_set);
        let dispatch_effects: Vec<String> = dispatch_set.into_iter().collect();
        let mut known_dispatch_effects = self.known_function_dispatch_effects.clone();
        if !dispatch_effects.is_empty() {
            known_dispatch_effects.insert(catch_fn_name.clone(), dispatch_effects.clone());
        }

        let lowered_functions = lower_hir_function(
            &lifted,
            &self.layouts,
            &known,
            &known_types,
            &self.known_function_alias_targets,
            &self.known_const_exprs,
            &self.intrinsic_symbols,
            &self.effect_operations,
            &known_dispatch_effects,
            &self.lambda_factories,
            false,
        );
        for lowered in lowered_functions {
            self.register_generated_function(lowered);
        }

        // Emit a direct local call with capture_fail_result: true.
        let mut call_args = Vec::new();
        let mut call_arg_types = Vec::new();
        for (_, ty, value) in &captures {
            call_args.push(value.clone());
            call_arg_types.push(ty.clone());
        }

        let call_result = self.new_value();
        self.emit_inst(MirInst::Call {
            callee: MirCallee::Local(catch_fn_name),
            args: call_args,
            arg_types: call_arg_types,
            result: Some(call_result.clone()),
            ret_type: caught.ty.clone(),
            callee_fail_result_abi: true,
            capture_fail_result: true,
            cc_manifest_id: "default".to_string(),
        });

        Some(call_result)
    }

    /// Emit a call to one of the TLS fail-propagation intrinsics.
    /// Returns the result MirValueId for get/take (which return a pointer),
    /// or None for set (which is void).
    fn emit_fail_tls_call(
        &mut self,
        name: &str,
        args: Vec<MirValueId>,
    ) -> Option<MirValueId> {
        let has_return = name != "__kea_set_fail_payload";
        let result = if has_return {
            Some(self.new_value())
        } else {
            None
        };
        self.emit_inst(MirInst::Call {
            callee: MirCallee::External(name.to_string()),
            args,
            arg_types: vec![Type::Dynamic; if has_return { 0 } else { 1 }],
            result: result.clone(),
            ret_type: if has_return { Type::Dynamic } else { Type::Unit },
            callee_fail_result_abi: false,
            capture_fail_result: false,
            cc_manifest_id: "default".to_string(),
        });
        result
    }

    /// Lower a callback body through `lower_catch_body_as_local_call`, then
    /// branch on the Result:
    ///
    /// - Ok(v)  → return v normally (fast path, no TLS access)
    /// - Err(p) → check-before-set into TLS slot (first-Fail-wins), return
    ///   a zero sentinel so the dispatch site can continue running
    ///
    /// Used by `lower_hir_function` when `fail_tls_wrap` is set for handler
    /// clause callbacks that contain residual `Fail`-effectful calls.
    fn emit_fail_tls_wrapped_body(
        &mut self,
        body: &HirExpr,
        ret_ty: &Type,
    ) -> Option<MirValueId> {
        // Lift the body to a fail_result_abi sub-function and call it.
        let catch_result = self.lower_catch_body_as_local_call(body)?;

        // Load the discriminant tag: 0 = Ok, non-zero = Err.
        let tag = self.new_value();
        self.emit_inst(MirInst::SumTagLoad {
            dest: tag.clone(),
            sum: catch_result.clone(),
            sum_type: "Result".to_string(),
        });

        // Branch: if tag == 0 (Ok) → ok_block; if tag != 0 (Err) → err_block.
        // MirTerminator::Branch sends control to then_block when condition != 0.
        // We want then=err, else=ok.
        let ok_block = self.new_block();
        let err_block = self.new_block();

        // Join block carries the final callback return value.
        let join_param = self.new_value();
        let join_block = self.new_block_with_params(vec![MirBlockParam {
            id: join_param.clone(),
            ty: ret_ty.clone(),
        }]);

        self.set_terminator(MirTerminator::Branch {
            condition: tag,
            then_block: err_block.clone(),
            else_block: ok_block.clone(),
        });

        // Ok branch: extract the inner value and jump to join.
        self.switch_to(ok_block);
        let ok_value = self.new_value();
        self.emit_inst(MirInst::SumPayloadLoad {
            dest: ok_value.clone(),
            sum: catch_result.clone(),
            sum_type: "Result".to_string(),
            variant: "Ok".to_string(),
            field_index: 0,
            field_ty: ret_ty.clone(),
        });
        self.ensure_jump_to(join_block.clone(), vec![ok_value]);

        // Err branch: extract fail payload, check-before-set into TLS, return sentinel.
        self.switch_to(err_block);
        let err_payload = self.new_value();
        self.emit_inst(MirInst::SumPayloadLoad {
            dest: err_payload.clone(),
            sum: catch_result.clone(),
            sum_type: "Result".to_string(),
            variant: "Err".to_string(),
            field_index: 0,
            field_ty: Type::Dynamic,
        });

        // existing = __kea_get_fail_payload()
        // Branch on existing: if non-null (slot already set), skip — first Fail wins.
        let existing = self
            .emit_fail_tls_call("__kea_get_fail_payload", vec![])
            .expect("__kea_get_fail_payload returns a value");
        let set_block = self.new_block();
        let skip_block = self.new_block();
        let after_tls = self.new_block();
        // Branch: existing != 0 → skip_block (already set); existing == 0 → set_block.
        self.set_terminator(MirTerminator::Branch {
            condition: existing,
            then_block: skip_block.clone(),
            else_block: set_block.clone(),
        });

        // set_block: store err_payload into TLS slot.
        self.switch_to(set_block);
        self.emit_fail_tls_call("__kea_set_fail_payload", vec![err_payload]);
        self.ensure_jump_to(after_tls.clone(), vec![]);

        // skip_block: TLS already holds an earlier payload; drop this one.
        self.switch_to(skip_block);
        self.ensure_jump_to(after_tls.clone(), vec![]);

        // after_tls: return a zero sentinel so the dispatch site can continue.
        self.switch_to(after_tls);
        let sentinel = self.new_value();
        if *ret_ty == Type::Unit {
            self.emit_inst(MirInst::Const {
                dest: sentinel.clone(),
                literal: MirLiteral::Unit,
            });
        } else {
            self.emit_inst(MirInst::Const {
                dest: sentinel.clone(),
                literal: MirLiteral::Int(0),
            });
        }
        self.ensure_jump_to(join_block.clone(), vec![sentinel]);

        // The join block is the exit point; its param is the value returned by
        // lower_hir_function as the function's return value.
        self.switch_to(join_block);
        Some(join_param)
    }

    /// After a `catch` body returns, check whether a handler-clause callback
    /// stored a Fail payload in the TLS slot.
    ///
    /// - If the body returned Ok AND TLS is set → override with Err(tls_payload).
    /// - If the body returned Err → clear TLS (to prevent outer-catch contamination)
    ///   and keep the body's Err.
    /// - If TLS is null → pass the result through unchanged.
    ///
    /// Always calls `__kea_take_fail_payload` (which atomically clears the slot)
    /// so the slot never leaks to a containing `catch` scope.
    fn emit_catch_tls_check(&mut self, result: MirValueId, caught_ty: &Type) -> MirValueId {
        // Load the Result tag (0 = Ok, non-zero = Err).
        let tag = self.new_value();
        self.emit_inst(MirInst::SumTagLoad {
            dest: tag.clone(),
            sum: result.clone(),
            sum_type: "Result".to_string(),
        });

        let ok_block = self.new_block();
        let err_block = self.new_block();
        let join_param = self.new_value();
        let join_block = self.new_block_with_params(vec![MirBlockParam {
            id: join_param.clone(),
            ty: Type::Sum(kea_types::SumType {
                name: "Result".to_string(),
                type_args: Vec::new(),
            }),
        }]);

        // Branch: tag != 0 → err_block; tag == 0 → ok_block.
        self.set_terminator(MirTerminator::Branch {
            condition: tag,
            then_block: err_block.clone(),
            else_block: ok_block.clone(),
        });

        // Ok path: take TLS; if non-null, override result with Err(tls_payload).
        self.switch_to(ok_block);
        let tls_payload = self
            .emit_fail_tls_call("__kea_take_fail_payload", vec![])
            .expect("__kea_take_fail_payload returns a value");

        let override_block = self.new_block();
        let keep_block = self.new_block();
        // Branch: tls_payload != 0 → override_block; == 0 → keep_block.
        self.set_terminator(MirTerminator::Branch {
            condition: tls_payload.clone(),
            then_block: override_block.clone(),
            else_block: keep_block.clone(),
        });

        // override_block: construct Err(tls_payload) and jump to join.
        self.switch_to(override_block);
        let new_err = self.new_value();
        self.emit_inst(MirInst::SumInit {
            dest: new_err.clone(),
            sum_type: "Result".to_string(),
            variant: "Err".to_string(),
            tag: 1,
            fields: vec![tls_payload],
        });
        self.sum_value_types
            .insert(new_err.clone(), "Result".to_string());
        self.ensure_jump_to(join_block.clone(), vec![new_err]);

        // keep_block: TLS was null; pass the Ok result through unchanged.
        self.switch_to(keep_block);
        self.ensure_jump_to(join_block.clone(), vec![result.clone()]);

        // Err path: take TLS to clear the slot, then keep the body's Err result.
        self.switch_to(err_block);
        let _ = self.emit_fail_tls_call("__kea_take_fail_payload", vec![]);
        self.ensure_jump_to(join_block.clone(), vec![result.clone()]);

        // Join: the final Result value.
        self.switch_to(join_block);
        let _ = caught_ty; // used implicitly via result type tracking
        join_param
    }

    fn lower_lambda_to_closure_value(
        &mut self,
        expr: &HirExpr,
        params: &[kea_hir::HirParam],
        body: &HirExpr,
        expected_ty: Option<&Type>,
        bind_dispatch_effects: bool,
        fail_tls_wrap: bool,
    ) -> Option<MirValueId> {
        let resolved_fn_ty = match (&expr.ty, expected_ty) {
            (Type::Function(ft), _) => Some(ft.clone()),
            (_, Some(Type::Function(ft))) => Some(ft.clone()),
            _ => None,
        }?;
        let param_names = params
            .iter()
            .filter_map(|param| param.name.as_ref())
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut var_refs = BTreeSet::new();
        collect_hir_var_refs(body, &mut var_refs);
        let captures = var_refs
            .into_iter()
            .filter(|name| !param_names.contains(name))
            .filter(|name| self.vars.contains_key(name))
            .map(|name| {
                let capture_ty = self.var_types.get(&name).cloned().unwrap_or(Type::Dynamic);
                let capture_value = self
                    .vars
                    .get(&name)
                    .cloned()
                    .expect("capture values must exist in lowering scope");
                (name, capture_ty, capture_value)
            })
            .collect::<Vec<_>>();
        let lambda_name = format!(
            "{}::lambda${}",
            self.function_name, self.next_lifted_lambda_id
        );
        self.next_lifted_lambda_id = self.next_lifted_lambda_id.saturating_add(1);
        let lifted_params = captures
            .iter()
            .map(|(name, _, _)| kea_hir::HirParam {
                name: Some(name.clone()),
                span: expr.span,
            })
            .chain(params.iter().cloned())
            .collect::<Vec<_>>();
        let lifted_fn_ty = FunctionType::with_effects(
            captures
                .iter()
                .map(|(_, ty, _)| ty.clone())
                .chain(resolved_fn_ty.params.iter().cloned())
                .collect(),
            resolved_fn_ty.ret.as_ref().clone(),
            resolved_fn_ty.effects.clone(),
        );
        let lifted = HirFunction {
            name: lambda_name.clone(),
            params: lifted_params,
            body: body.clone(),
            ty: Type::Function(lifted_fn_ty),
            effects: resolved_fn_ty.effects.clone(),
            span: expr.span,
            is_fip: false,
        };
        let mut known = self.known_functions.clone();
        known.insert(lambda_name.clone());
        let mut known_types = self.known_function_types.clone();
        known_types.insert(lambda_name.clone(), lifted.ty.clone());
        let mut lambda_dispatch_set = self
            .dispatch_effects_for_effect_row(&resolved_fn_ty.effects)
            .into_iter()
            .collect::<BTreeSet<_>>();
        collect_hir_dispatch_effect_ops(body, &self.effect_operations, &mut lambda_dispatch_set);
        // Also collect dispatch effects required by directly-called known functions.
        // This is necessary when the lambda type is pure (e.g. handler clause callbacks)
        // but the body calls functions like IO.println that require dispatch cells.
        // Without this, the closure doesn't capture the needed effect cells and crashes.
        collect_callee_known_dispatch_effects(
            body,
            &self.known_function_dispatch_effects,
            &mut lambda_dispatch_set,
        );
        let lambda_dispatch_effects = lambda_dispatch_set.into_iter().collect::<Vec<_>>();

        // Determine which dispatch effects to capture from active cells vs. thread as trailing
        // params. Effects with an active cell at the creation site are captured into the closure
        // so they don't appear as trailing params in the entry wrapper. This is critical for
        // effect-polymorphic callers: when a caller calls `f: fn() -[Test, e]> Unit`, it only
        // passes dispatch cells for the *concrete* effects in the type (Test.check) — it cannot
        // pass cells for effects buried in the row variable `e` (e.g., IO). By capturing IO at
        // creation time, the entry wrapper only needs trailing params for effects the caller
        // actually knows about.
        //
        // The lifted lambda body is compiled with dispatch effects ordered [trailing, bound] so
        // that param indices from the entry wrapper call match the lifted function's expectations.
        let mut wrapper_dispatch_effects: Vec<String> = Vec::new();
        let mut bound_dispatch_effects_keys: Vec<String> = Vec::new();
        let mut bound_dispatch_captures: Vec<(MirValueId, Type)> = Vec::new();
        for dispatch_op_key in &lambda_dispatch_effects {
            let Some((dispatch_effect, dispatch_operation)) = dispatch_op_key.split_once('.')
            else {
                self.emit_inst(MirInst::Unsupported {
                    detail: format!("invalid dispatch operation key `{dispatch_op_key}`"),
                });
                return None;
            };
            if let Some(dispatch_cell) =
                self.lookup_effect_cell(dispatch_effect, dispatch_operation)
            {
                // Active cell available — capture it so it doesn't become a trailing param.
                bound_dispatch_captures.push((dispatch_cell, Type::Dynamic));
                bound_dispatch_effects_keys.push(dispatch_op_key.clone());
            } else if bind_dispatch_effects {
                // Caller requires all cells to be bound (expression-position lambda).
                self.emit_inst(MirInst::Unsupported {
                    detail: format!(
                        "missing active handler cell for operation `{dispatch_op_key}` while binding lambda dispatch"
                    ),
                });
                return None;
            } else {
                // No active cell — becomes a trailing dispatch param, provided by the caller.
                wrapper_dispatch_effects.push(dispatch_op_key.clone());
            }
        }

        // The lifted lambda body sees dispatch effects in [trailing, bound] order.
        // Trailing params come from the entry wrapper signature; bound params come after.
        let lifted_lambda_dispatch_effects: Vec<String> = wrapper_dispatch_effects
            .iter()
            .chain(bound_dispatch_effects_keys.iter())
            .cloned()
            .collect();

        let mut known_dispatch_effects = self.known_function_dispatch_effects.clone();
        if !lifted_lambda_dispatch_effects.is_empty() {
            known_dispatch_effects
                .insert(lambda_name.clone(), lifted_lambda_dispatch_effects.clone());
        }
        let lowered_functions = lower_hir_function(
            &lifted,
            &self.layouts,
            &known,
            &known_types,
            &self.known_function_alias_targets,
            &self.known_const_exprs,
            &self.intrinsic_symbols,
            &self.effect_operations,
            &known_dispatch_effects,
            &self.lambda_factories,
            fail_tls_wrap,
        );
        // Use the actual return type from the lowered lambda body rather than
        // resolved_fn_ty.ret. HIR types are erased to Dynamic when no annotation
        // is available; lower_hir_function promotes Dynamic→Unit when the body
        // produces no value, so the lowered signature has the correct ret.
        let actual_ret = lowered_functions
            .first()
            .map(|f| f.signature.ret.clone())
            .unwrap_or_else(|| resolved_fn_ty.ret.as_ref().clone());
        for lowered in lowered_functions {
            self.register_generated_function(lowered);
        }

        let entry_name = self.allocate_generated_closure_entry_name("lambda");
        let callee_fail_result_abi = uses_fail_result_abi_from_type(&lifted.ty);
        let wrapper = self.build_closure_entry_wrapper(
            entry_name.clone(),
            lambda_name,
            captures.iter().map(|(_, ty, _)| ty.clone()).collect(),
            resolved_fn_ty.params.clone(),
            wrapper_dispatch_effects,
            bound_dispatch_captures
                .iter()
                .map(|(_, ty)| ty.clone())
                .collect(),
            actual_ret,
            resolved_fn_ty.effects.clone(),
            callee_fail_result_abi,
        );
        self.register_generated_function(wrapper);

        let mut all_captures = captures
            .into_iter()
            .map(|(_, ty, value)| (value, ty))
            .collect::<Vec<_>>();
        all_captures.extend(bound_dispatch_captures);
        self.emit_closure_value(entry_name, all_captures)
    }

    fn finish(mut self, return_value: Option<MirValueId>, ret_ty: &Type) -> Vec<MirBlock> {
        if self.current_block().terminator.is_none() {
            let value = if *ret_ty == Type::Unit {
                None
            } else {
                return_value
            };
            self.set_terminator(MirTerminator::Return { value });
        }

        self.blocks
            .into_iter()
            .map(|mut block| {
                if block.instructions.is_empty() {
                    block.instructions.push(MirInst::Nop);
                }
                MirBlock {
                    id: block.id,
                    params: block.params,
                    instructions: block.instructions,
                    terminator: block.terminator.unwrap_or(MirTerminator::Unreachable),
                }
            })
            .collect()
    }

    fn new_value(&mut self) -> MirValueId {
        let value = MirValueId(self.next_value_id);
        self.next_value_id += 1;
        value
    }

    fn new_block(&mut self) -> MirBlockId {
        self.new_block_with_params(Vec::new())
    }

    fn new_block_with_params(&mut self, params: Vec<MirBlockParam>) -> MirBlockId {
        let block_id = MirBlockId(self.blocks.len() as u32);
        self.blocks.push(PendingBlock {
            id: block_id.clone(),
            params,
            instructions: Vec::new(),
            terminator: None,
        });
        block_id
    }

    fn switch_to(&mut self, block_id: MirBlockId) {
        self.current_block = block_id;
    }

    fn current_block_index(&self) -> usize {
        self.current_block.0 as usize
    }

    fn current_block(&self) -> &PendingBlock {
        &self.blocks[self.current_block_index()]
    }

    fn current_block_mut(&mut self) -> &mut PendingBlock {
        let index = self.current_block_index();
        &mut self.blocks[index]
    }

    fn emit_inst(&mut self, inst: MirInst) {
        self.current_block_mut().instructions.push(inst);
    }

    /// Returns true if `value_id` is a parameter of the current block or is
    /// defined by an instruction in the current block. Used by the Block
    /// cleanup to guard Release insertion for Dynamic-typed join params so we
    /// don't emit Release for SSA values from dominating blocks that were not
    /// re-passed as explicit block arguments.
    /// Returns true if the last read of `value_id` in the current block's instructions
    /// was as a direct argument or the callee of a `Call` instruction (i.e., ownership
    /// was transferred — Perceus calls consume both args and the callee closure). In
    /// that case the Block cleanup should NOT emit a Release for the value; the callee
    /// mechanism is now responsible for the refcount.
    fn value_was_consumed_by_call(&self, value_id: &MirValueId) -> bool {
        for inst in self.current_block().instructions.iter().rev() {
            if inst_reads_value(inst, value_id) {
                return inst_value_consumed_by_call(inst, value_id);
            }
        }
        false
    }

    fn value_is_live_in_current_block(&self, value_id: &MirValueId) -> bool {
        let block = self.current_block();
        if block.params.iter().any(|p| &p.id == value_id) {
            return true;
        }
        block.instructions.iter().any(|inst| match inst {
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
            | MirInst::Freeze { dest, .. }
            | MirInst::CowUpdate { dest, .. } => dest == value_id,
            MirInst::EffectOp {
                result: Some(dest), ..
            }
            | MirInst::Call {
                result: Some(dest), ..
            } => dest == value_id,
            _ => false,
        })
    }

    fn set_terminator(&mut self, terminator: MirTerminator) {
        self.current_block_mut().terminator = Some(terminator);
    }

    fn snapshot_var_scope(&self) -> VarScope {
        VarScope {
            vars: self.vars.clone(),
            var_types: self.var_types.clone(),
            local_lambdas: self.local_lambdas.clone(),
            var_record_types: self.var_record_types.clone(),
            active_effect_cells: self.active_effect_cells.clone(),
            active_effect_handlers: self.active_effect_handlers.clone(),
        }
    }

    fn restore_var_scope(&mut self, scope: &VarScope) {
        self.vars = scope.vars.clone();
        self.var_types = scope.var_types.clone();
        self.local_lambdas = scope.local_lambdas.clone();
        self.var_record_types = scope.var_record_types.clone();
        self.active_effect_cells = scope.active_effect_cells.clone();
        self.active_effect_handlers = scope.active_effect_handlers.clone();
    }

    fn ensure_jump_to(&mut self, target: MirBlockId, args: Vec<MirValueId>) {
        if self.current_block().terminator.is_none() {
            self.set_terminator(MirTerminator::Jump { target, args });
        }
    }

    fn lookup_effect_cell(&self, effect: &str, operation: &str) -> Option<MirValueId> {
        self.active_effect_cells
            .get(&(effect.to_string(), operation.to_string()))
            .cloned()
    }

    fn lower_expr(&mut self, expr: &HirExpr) -> Option<MirValueId> {
        match &expr.kind {
            HirExprKind::Lit(lit) => {
                let dest = self.new_value();
                self.emit_inst(MirInst::Const {
                    dest: dest.clone(),
                    literal: lower_literal(lit),
                });
                Some(dest)
            }
            HirExprKind::Var(name) => {
                if let Some(value) = self.vars.get(name) {
                    return Some(value.clone());
                }
                if self.known_functions.contains(name) {
                    return self.lower_named_function_to_closure_value(name);
                }
                if let Some(const_expr) = self.known_const_exprs.get(name).cloned() {
                    return self.lower_named_const_expr(name, &const_expr);
                }
                None
            }
            HirExprKind::Binary { op, left, right } => {
                if expr.ty == Type::Bool && matches!(op, BinOp::And | BinOp::Or) {
                    return self.lower_short_circuit_binary(*op, left, right);
                }
                if matches!(op, BinOp::Eq | BinOp::Neq) {
                    let left_eq_ty = self.resolve_equality_operand_type(left);
                    let right_eq_ty = self.resolve_equality_operand_type(right);
                    if same_nominal_equality_type(&left_eq_ty, &right_eq_ty)
                        && !is_primitive_equality_type(&left_eq_ty)
                        && is_concrete_nominal_equality_type(&left_eq_ty)
                        && let Some(value) = self.lower_eq_via_trait_call(*op, left, right)
                    {
                        return Some(value);
                    }
                }
                let left_value = self.lower_expr(left)?;
                let right_value = self.lower_expr(right)?;
                let left_value = self.lower_maybe_sum_tag_operand(*op, left, left_value, right);
                let right_value = self.lower_maybe_sum_tag_operand(*op, right, right_value, left);
                // Auto-widen narrow ints when mixed with `Int` (i64) in arithmetic.
                // `Int8 + 0` and similar expressions are valid because integer
                // literals default to `Int`; widen the narrow side to match.
                let (left_value, right_value) = self.maybe_widen_mixed_int_operands(
                    &left.ty, left_value, &right.ty, right_value,
                );
                let dest = self.new_value();
                self.emit_inst(MirInst::Binary {
                    dest: dest.clone(),
                    op: lower_binop(*op),
                    left: left_value,
                    right: right_value,
                });
                Some(dest)
            }
            HirExprKind::Unary { op, operand } => {
                let operand_value = self.lower_expr(operand)?;
                let dest = self.new_value();
                self.emit_inst(MirInst::Unary {
                    dest: dest.clone(),
                    op: lower_unaryop(*op),
                    operand: operand_value,
                });
                Some(dest)
            }
            HirExprKind::RecordLit {
                record_type,
                fields,
            } => {
                let mut lowered_fields = Vec::with_capacity(fields.len());
                for (field_name, field_expr) in fields {
                    let field_value = self.lower_expr(field_expr)?;
                    lowered_fields.push((field_name.clone(), field_value));
                }
                let dest = self.new_value();
                self.emit_inst(MirInst::RecordInit {
                    dest: dest.clone(),
                    record_type: record_type.clone(),
                    fields: lowered_fields,
                });
                self.record_value_types
                    .insert(dest.clone(), record_type.clone());
                Some(dest)
            }
            HirExprKind::RecordUpdate {
                record_type,
                base,
                fields,
            } => {
                let mut flattened_updates = Vec::new();
                let flattened_base =
                    Self::collect_record_update_chain(base, record_type, &mut flattened_updates);
                for (field_name, field_expr) in fields {
                    flattened_updates.push((field_name.clone(), field_expr));
                }

                let target = self.lower_expr(flattened_base)?;
                let mut retain_target = true;
                if let HirExprKind::Var(source_name) = &flattened_base.kind
                    && self.vars.contains_key(source_name)
                    && is_heap_managed_type(&flattened_base.ty, &self.layouts)
                {
                    let source_used_later = self.name_maybe_referenced_later_in_block(source_name);
                    let source_from_outer_scope =
                        self.name_captured_from_outer_block_scope(source_name);
                    let source_read_in_update_fields =
                        flattened_updates.iter().any(|(_, field_expr)| {
                            let mut refs = BTreeSet::new();
                            collect_hir_var_refs(field_expr, &mut refs);
                            refs.contains(source_name)
                        });
                    if !source_used_later
                        && !source_from_outer_scope
                        && !source_read_in_update_fields
                    {
                        self.drop_local_binding_metadata(source_name);
                        retain_target = false;
                    }
                }
                if retain_target {
                    self.emit_inst(MirInst::Retain {
                        value: target.clone(),
                    });
                }
                let claimed = self.new_value();
                self.emit_inst(MirInst::TryClaim {
                    dest: claimed.clone(),
                    src: target.clone(),
                });
                let frozen = self.new_value();
                self.emit_inst(MirInst::Freeze {
                    dest: frozen.clone(),
                    src: claimed,
                });

                let mut updates: Vec<MirFieldUpdate> = Vec::with_capacity(flattened_updates.len());
                for (field_name, field_expr) in flattened_updates {
                    let value = self.lower_expr(field_expr)?;
                    if let Some(existing) =
                        updates.iter_mut().find(|update| update.field == field_name)
                    {
                        existing.value = value;
                    } else {
                        updates.push(MirFieldUpdate {
                            field: field_name,
                            value,
                        });
                    }
                }

                let resolved_record_type = if record_type.is_empty() {
                    match &flattened_base.ty {
                        Type::Record(record_ty) => Some(record_ty.name.clone()),
                        Type::AnonRecord(row) => self.infer_unique_record_type_for_row(row),
                        _ => match &flattened_base.kind {
                            HirExprKind::Var(name) => self.var_record_types.get(name).cloned(),
                            HirExprKind::Call { func, .. } => {
                                self.infer_record_type_from_call(func)
                            }
                            _ => self.record_value_types.get(&target).cloned(),
                        },
                    }?
                } else {
                    record_type.clone()
                };

                let dest = self.new_value();
                let block_id = self.current_block.clone();
                self.emit_inst(MirInst::CowUpdate {
                    dest: dest.clone(),
                    target: frozen,
                    record_type: resolved_record_type.clone(),
                    updates,
                    unique_path: block_id.clone(),
                    copy_path: block_id,
                });
                // No Release here: the copy path in CowUpdate codegen emits
                // the release of the original target; the unique path reuses
                // the target in place, so releasing it would free the result.
                self.record_value_types
                    .insert(dest.clone(), resolved_record_type);
                Some(dest)
            }
            HirExprKind::SumConstructor {
                sum_type,
                variant,
                tag,
                fields,
            } => {
                let mut lowered_fields = Vec::with_capacity(fields.len());
                for field_expr in fields {
                    lowered_fields.push(self.lower_expr(field_expr)?);
                }
                let tag = u32::try_from(*tag).ok()?;
                let dest = self.new_value();
                self.emit_inst(MirInst::SumInit {
                    dest: dest.clone(),
                    sum_type: sum_type.clone(),
                    variant: variant.clone(),
                    tag,
                    fields: lowered_fields,
                });
                self.sum_value_types.insert(dest.clone(), sum_type.clone());
                Some(dest)
            }
            HirExprKind::FieldAccess { expr: base, field } => {
                let record = self.lower_expr(base)?;
                let record_type = match &base.ty {
                    Type::Record(record_ty) => Some(record_ty.name.clone()),
                    Type::AnonRecord(row) => self.infer_unique_record_type_for_row(row),
                    Type::Tuple(items) => Some(tuple_layout_name(items.len())),
                    _ => match &base.kind {
                        HirExprKind::Var(name) => self.var_record_types.get(name).cloned(),
                        HirExprKind::Call { func, .. } => self.infer_record_type_from_call(func),
                        _ => self.record_value_types.get(&record).cloned(),
                    },
                }?;
                // For tuple field accesses, recover the actual element type from
                // the tuple's type information rather than relying on expr.ty, which
                // may be Type::Dynamic when type inference did not propagate through
                // the field projection.  Without the correct type, RecordFieldLoad
                // in codegen cannot emit the necessary Retain for heap-managed fields,
                // leading to use-after-free when the same field is accessed twice.
                //
                // Priority order for resolving the element type:
                //  1. `base.ty` is `Type::Tuple(items)` — directly available.
                //  2. `tuple_value_types[record]` — populated when the tuple was
                //     produced by a call whose return type was a concrete Tuple (even
                //     when the HIR Var expression that binds the result carries Dynamic).
                let field_ty = if let Type::Tuple(items) = &base.ty {
                    field
                        .parse::<usize>()
                        .ok()
                        .and_then(|idx| items.get(idx))
                        .cloned()
                        .unwrap_or_else(|| expr.ty.clone())
                } else if let Some(items) = self.tuple_value_types.get(&record) {
                    field
                        .parse::<usize>()
                        .ok()
                        .and_then(|idx| items.get(idx))
                        .cloned()
                        .unwrap_or_else(|| expr.ty.clone())
                } else {
                    expr.ty.clone()
                };
                let dest = self.new_value();
                self.emit_inst(MirInst::RecordFieldLoad {
                    dest: dest.clone(),
                    record,
                    record_type,
                    field: field.clone(),
                    field_ty,
                });
                Some(dest)
            }
            HirExprKind::SumPayloadAccess {
                expr: base,
                sum_type,
                variant,
                field_index,
            } => {
                let sum = self.lower_expr(base)?;
                // When the HIR payload type is Dynamic, attempt to recover the
                // concrete element type from the scrutinee's sum type args.  For a
                // generic sum type `Foo A B` (e.g. `List a`), the k-th field of a
                // constructor is often `type_args[k]`.  This lets us propagate
                // `(Int, Int)` when matching `Cons(pair, rest)` on
                // `List (Int, Int)` so that `pair.0` can be resolved.
                let field_ty = if expr.ty == Type::Dynamic {
                    if let Type::Sum(sum_ty) = &base.ty
                        && sum_ty.name == *sum_type
                        && let Some(concrete) = sum_ty.type_args.get(*field_index)
                    {
                        concrete.clone()
                    } else {
                        Type::Dynamic
                    }
                } else {
                    expr.ty.clone()
                };
                let dest = self.new_value();
                self.emit_inst(MirInst::SumPayloadLoad {
                    dest: dest.clone(),
                    sum,
                    sum_type: sum_type.clone(),
                    variant: variant.clone(),
                    field_index: *field_index,
                    field_ty: field_ty.clone(),
                });
                // When the concrete field type is a tuple, register the element
                // types so that MIR can resolve `pair.0` field accesses even when
                // the HIR let-binding propagates a Dynamic value type.
                if let Type::Tuple(items) = &field_ty {
                    self.tuple_value_types.insert(dest.clone(), items.clone());
                }
                if let Some(inner_sum_type) = self.infer_sum_type_from_type(&field_ty) {
                    self.sum_value_types.insert(dest.clone(), inner_sum_type);
                }
                // Track SumPayloadLoad results with managed-type fields: Block cleanup
                // must NOT release these independently (see sum_payload_load_dests doc).
                if is_heap_managed_type(&field_ty, &self.layouts) {
                    self.sum_payload_load_dests.insert(dest.clone());
                }
                Some(dest)
            }
            HirExprKind::Call { func, args } => self.lower_call_expr(expr, func, args, false),
            HirExprKind::Catch { expr: caught } => {
                let result = if let HirExprKind::Call { func, args } = &caught.kind
                    && let HirExprKind::Var(name) = &func.kind
                    && name == "Fail.fail"
                {
                    // Direct `catch fail x` — statically known to always produce Err(x).
                    // Emit Err(arg) directly instead of routing through the call path,
                    // which can't resolve Fail.fail as a callable symbol.
                    let mut fields = Vec::new();
                    for arg in args {
                        if let Some(v) = self.lower_expr(arg) {
                            fields.push(v);
                        }
                    }
                    let dest = self.new_value();
                    self.emit_inst(MirInst::SumInit {
                        dest: dest.clone(),
                        sum_type: "Result".to_string(),
                        variant: "Err".to_string(),
                        tag: 1,
                        fields,
                    });
                    dest
                } else if let HirExprKind::Call { func, args } = &caught.kind {
                    self.lower_call_expr(caught, func, args, true)?
                } else {
                    self.lower_catch_body_as_local_call(caught)?
                };

                // TLS fail-propagation check: after the caught body returns, inspect
                // the TLS slot set by any handler-clause callbacks that Fail-ed.
                // If the body returned Ok but a callback Fail-ed, override the result
                // with Err(tls_payload) so the outer code sees the failure.
                // If the body returned Err (direct failure), just clear TLS and keep
                // the body's Err.  Always take (not just get) to prevent leakage.
                let final_result = self.emit_catch_tls_check(result.clone(), &caught.ty);

                self.sum_value_types
                    .insert(final_result.clone(), "Result".to_string());
                Some(final_result)
            }
            HirExprKind::Handle {
                expr: handled,
                clauses,
                then_clause,
            } => self.lower_handle_expr(expr, handled, clauses, then_clause.as_deref()),
            HirExprKind::Resume { value } => self.lower_expr(value),
            HirExprKind::Let { pattern, value } => {
                if let (HirPattern::Var(name), HirExprKind::Lambda { params, body }) =
                    (pattern, &value.kind)
                {
                    self.local_lambdas.insert(
                        name.clone(),
                        LocalLambda {
                            params: params.clone(),
                            body: body.as_ref().clone(),
                            captures: Vec::new(),
                        },
                    );
                }
                let value_id = self.lower_expr(value)?;
                if let (HirPattern::Var(target_name), HirExprKind::Var(source_name)) =
                    (pattern, &value.kind)
                    && self.vars.contains_key(source_name)
                    && is_heap_managed_type(&value.ty, &self.layouts)
                {
                    let source_used_later = self.name_maybe_referenced_later_in_block(source_name);
                    let source_from_outer_scope =
                        self.name_captured_from_outer_block_scope(source_name);
                    if source_used_later || source_from_outer_scope {
                        self.emit_inst(MirInst::Retain {
                            value: value_id.clone(),
                        });
                    } else if target_name != source_name {
                        // Linear local alias: transfer ownership from source binding
                        // to target binding and avoid retain/release churn.
                        self.drop_local_binding_metadata(source_name);
                    }
                }
                self.bind_pattern(pattern, value_id.clone(), &value.ty);
                Some(value_id)
            }
            HirExprKind::Block(exprs) => {
                let incoming_scope = self.snapshot_var_scope();
                let mut last = None;
                let tail_refs = block_tail_ref_sets(exprs);
                self.block_incoming_bindings_stack
                    .push(incoming_scope.vars.keys().cloned().collect());
                for (index, expr) in exprs.iter().enumerate() {
                    self.block_tail_refs_stack
                        .push(tail_refs[index + 1].clone());
                    last = self.lower_expr(expr);
                    self.block_tail_refs_stack.pop();
                    if self.current_block().terminator.is_some() {
                        break;
                    }
                }
                self.block_incoming_bindings_stack.pop();
                if self.current_block().terminator.is_none() {
                    let mut releases = Vec::new();
                    for (name, value_id) in &self.vars {
                        let is_shadowed_or_new = incoming_scope
                            .vars
                            .get(name)
                            .is_none_or(|incoming_value| incoming_value != value_id);
                        if !is_shadowed_or_new {
                            continue;
                        }
                        let is_heap_managed = {
                            let by_static_type = self
                                .var_types
                                .get(name)
                                .is_some_and(|ty| is_heap_managed_type(ty, &self.layouts));
                            // If the static type is Dynamic (common for if/case join params),
                            // also check the runtime record/sum type maps to determine whether
                            // the value is heap-managed. Only do this when the value is live
                            // in the current block (is a param or defined here), to avoid
                            // emitting Release for SSA values from earlier blocks that are no
                            // longer in scope at this join point.
                            let by_tracked_record_type = !by_static_type
                                && self.record_value_types.get(value_id).is_some_and(|rname| {
                                    !self
                                        .layouts
                                        .records
                                        .iter()
                                        .any(|l| l.name == *rname && l.is_unboxed)
                                })
                                && self.value_is_live_in_current_block(value_id);
                            let by_tracked_sum_type = !by_static_type
                                && self.sum_value_types.contains_key(value_id)
                                && self.value_is_live_in_current_block(value_id);
                            by_static_type || by_tracked_record_type || by_tracked_sum_type
                        };
                        if !is_heap_managed {
                            continue;
                        }
                        if last.as_ref().is_some_and(|result_id| result_id == value_id) {
                            continue;
                        }
                        // If the value's last use was as a direct Call argument, ownership
                        // was transferred to the callee — don't release from the caller side.
                        if self.value_was_consumed_by_call(value_id) {
                            continue;
                        }
                        // SumPayloadLoad results of managed types are borrowed references
                        // into the parent cell. Releasing them here can double-free with
                        // the parent's destructor on paths where the parent is also dropped.
                        // The insert_releases_for_dead_params pass guards against releasing
                        // the parent after SumPayloadLoad extraction, so we accept a
                        // conservative "no release" (safe but leaky) until Perceus analysis
                        // is implemented.
                        if self.sum_payload_load_dests.contains(value_id) {
                            continue;
                        }
                        releases.push(value_id.clone());
                    }
                    for value_id in releases {
                        self.emit_inst(MirInst::Release { value: value_id });
                    }
                }
                self.restore_var_scope(&incoming_scope);
                last
            }
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => self.lower_if(expr, condition, then_branch, else_branch.as_deref()),
            HirExprKind::Lambda { params, body } => {
                let synthesized_ty = if matches!(expr.ty, Type::Function(_)) {
                    None
                } else {
                    Some(synth_lambda_type(params, body))
                };
                // Bind dispatch effects into the closure environment so that
                // effect operations inside the lambda body work when the closure
                // is called indirectly. The calling convention for closure variables
                // (var_types = Dynamic) passes no dispatch trailing args, so the
                // entry wrapper must have no dispatch params — cells are captured.
                self.lower_lambda_to_closure_value(
                    expr,
                    params,
                    body,
                    synthesized_ty.as_ref(),
                    true,
                    false,
                )
            }
            HirExprKind::Tuple(items) => {
                let mut lowered_fields = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    let field_value = self.lower_expr(item)?;
                    lowered_fields.push((index.to_string(), field_value));
                }
                let dest = self.new_value();
                let record_type = tuple_layout_name(items.len());
                self.emit_inst(MirInst::RecordInit {
                    dest: dest.clone(),
                    record_type: record_type.clone(),
                    fields: lowered_fields,
                });
                self.record_value_types.insert(dest.clone(), record_type);
                Some(dest)
            }
            HirExprKind::Raw(_) => match &expr.kind {
                HirExprKind::Raw(raw_expr) => self.lower_raw_ast_expr(raw_expr),
                _ => None,
            },
        }
    }

    fn lower_handle_expr(
        &mut self,
        handle_expr: &HirExpr,
        handled: &HirExpr,
        clauses: &[HirHandleClause],
        then_clause: Option<&HirExpr>,
    ) -> Option<MirValueId> {
        let target_effect = clauses.first()?.effect.clone();
        if clauses.iter().any(|clause| clause.effect != target_effect) {
            self.emit_inst(MirInst::Unsupported {
                detail: format!(
                    "handler lowering currently requires clauses from a single effect, got mixed clauses for `{target_effect}`"
                ),
            });
            return None;
        }
        let mut plan = ActiveEffectHandlerPlan::default();
        let mut operation_callback_values: BTreeMap<String, MirValueId> = BTreeMap::new();

        // Pre-scan: detect if this effect is stateful (has both a getter and setter).
        // A stateful effect has a zero-arg operation (getter) AND a 1-arg Unit-returning
        // operation (setter), e.g. State with get/put. This replaces the old Log-specific
        // exclusion with a structural check.
        let is_stateful = !is_direct_capability_effect(&target_effect) && {
            let ops: Vec<_> = self
                .effect_operations
                .values()
                .filter(|op| op.effect == target_effect)
                .collect();
            ops.iter().any(|op| op.arity == 0)
                && ops.iter().any(|op| op.arity == 1 && op.returns_unit)
        };

        // For stateful effects, create the internal state cell.
        // The initial value comes from the first zero-arg clause's resume value.
        let internal_state_cell = if is_stateful {
            // Find initial value from a zero-arg clause (State.get-like).
            let initial_expr = clauses
                .iter()
                .filter(|c| c.effect == target_effect && c.args.is_empty())
                .find_map(|c| match &c.body.kind {
                    HirExprKind::Resume { value } => Some(value.as_ref().clone()),
                    _ => split_non_tail_resume(&c.body, &BTreeSet::new())
                        .map(|s| s.resume_value.clone()),
                });
            let initial = if let Some(expr) = &initial_expr {
                self.lower_expr(expr)?
            } else {
                let unit = self.new_value();
                self.emit_inst(MirInst::Const {
                    dest: unit.clone(),
                    literal: MirLiteral::Unit,
                });
                unit
            };
            let cell = self.new_value();
            self.emit_inst(MirInst::StateCellNew {
                dest: cell.clone(),
                initial,
            });
            Some(cell)
        } else {
            None
        };

        for clause in clauses
            .iter()
            .filter(|clause| clause.effect == target_effect)
        {
            if plan.operation_lowering.contains_key(&clause.operation) {
                self.emit_inst(MirInst::Unsupported {
                    detail: format!(
                        "duplicate handler clause for `{target_effect}.{}` is not supported",
                        clause.operation
                    ),
                });
                return None;
            }

            let clause_arg_names: BTreeSet<String> = clause
                .args
                .iter()
                .filter_map(|p| {
                    if let HirPattern::Var(n) = p {
                        Some(n.clone())
                    } else {
                        None
                    }
                })
                .collect();

            let op_returns_never = self
                .effect_operations
                .get(&format!("{target_effect}.{}", clause.operation))
                .is_some_and(|op| op.returns_never);
            let classification =
                match classify_clause_body(
                    &clause.body,
                    &clause_arg_names,
                    clause.span,
                    op_returns_never,
                ) {
                    Some(c) => c,
                    None => {
                        self.emit_inst(MirInst::Unsupported {
                            detail: format!(
                                "handler clause `{target_effect}.{}` must be tail-resumptive \
                                 (`resume ...`) or use `let x = resume val; ...` form",
                                clause.operation,
                            ),
                        });
                        return None;
                    }
                };

            let pre_resume_capture_cells = match &classification {
                ClauseBodyClassification::NonTail(split) => {
                    self.allocate_pre_resume_capture_cells(split, clause.span)
                }
                _ => vec![],
            };

            let (inner_cb, arity, returns_unit) = self.build_clause_callback(
                clause,
                &target_effect,
                internal_state_cell.as_ref(),
                &classification,
                &pre_resume_capture_cells,
            )?;

            let final_callback = match &classification {
                ClauseBodyClassification::NonTail(split) => self
                    .wrap_with_chain_augmentation(
                        inner_cb,
                        &target_effect,
                        &clause.operation,
                        split,
                        &clause.args,
                        &clause.arg_types,
                        &clause.return_type,
                        &pre_resume_capture_cells,
                        clause.span,
                    )?,
                _ => inner_cb,
            };

            plan.operation_lowering.insert(
                clause.operation.clone(),
                HandlerCellOpLowering::InvokeCallback {
                    arity,
                    returns_unit,
                },
            );
            operation_callback_values.insert(clause.operation.clone(), final_callback);
        }
        if plan.operation_lowering.is_empty() {
            self.emit_inst(MirInst::Unsupported {
                detail: format!(
                    "handler lowering received no clauses for effect `{target_effect}`"
                ),
            });
            return None;
        }

        // Uniform InvokeCallback: all operations are callback closures.
        // The callback value IS the cell value stored in active_effect_cells.
        let mut operation_cells: Vec<(String, MirValueId)> = Vec::new();
        let mut release_cells: BTreeSet<MirValueId> = BTreeSet::new();
        for operation in plan.operation_lowering.keys() {
            let Some(callback) = operation_callback_values.get(operation) else {
                self.emit_inst(MirInst::Unsupported {
                    detail: format!(
                        "missing callback for handled operation `{target_effect}.{operation}`"
                    ),
                });
                return None;
            };
            release_cells.insert(callback.clone());
            operation_cells.push((operation.clone(), callback.clone()));
        }
        // Note: the internal state cell (if stateful) is NOT released here.
        // It is captured by the get/put callback closures, and its lifetime
        // is managed through those closures. Releasing it separately would
        // cause the optimizer to free it before the handler body executes
        // (schedule_trailing_releases_after_last_use sees the ClosureInit as
        // the last direct use, not the indirect use via the closure call).
        // Zero-resume setup: if any clause handles a Never-returning op, create an
        // exit block with a result param. Both the normal-completion path and each
        // zero-resume dispatch will jump to this block.
        let zero_resume_exit: Option<(MirBlockId, MirValueId)> = {
            let has_zero_resume = clauses.iter().any(|c| {
                self.effect_operations
                    .get(&format!("{target_effect}.{}", c.operation))
                    .is_some_and(|op| op.returns_never)
            });
            if has_zero_resume {
                let result_param = self.new_value();
                let exit_block = self.new_block_with_params(vec![MirBlockParam {
                    id: result_param.clone(),
                    ty: handle_expr.ty.clone(),
                }]);
                Some((exit_block, result_param))
            } else {
                None
            }
        };
        let prev_zero_resume_exit = self.active_zero_resume_exit.clone();
        self.active_zero_resume_exit = zero_resume_exit.clone();

        // For Direct capability effects (IO, Clock, etc.), if the handler only
        // covers some ops (e.g. just IO.exit), install default capability wrapper
        // cells for the uncovered non-Never ops so callee dispatch still works.
        let covered_ops: BTreeSet<String> =
            operation_cells.iter().map(|(op, _)| op.clone()).collect();
        let mut default_cells: Vec<(String, MirValueId)> = Vec::new();
        if is_direct_capability_effect(&target_effect) {
            let uncovered_ops: Vec<EffectOperationInfo> = self
                .effect_operations
                .values()
                .filter(|op| op.effect == target_effect && !op.returns_never)
                .filter(|op| !covered_ops.contains(&op.operation))
                .cloned()
                .collect();
            for op in uncovered_ops {
                if self
                    .active_effect_cells
                    .contains_key(&(target_effect.clone(), op.operation.clone()))
                {
                    // Already registered (e.g. from outer handle or main default).
                    continue;
                }
                let wrapper_name =
                    default_capability_wrapper_name(&target_effect, &op.operation);
                let fn_ref = self.new_value();
                self.emit_inst(MirInst::FunctionRef {
                    dest: fn_ref.clone(),
                    function: wrapper_name,
                });
                let closure = self.new_value();
                self.emit_inst(MirInst::ClosureInit {
                    dest: closure.clone(),
                    entry: fn_ref,
                    captures: vec![],
                    capture_types: vec![],
                });
                default_cells.push((op.operation.clone(), closure));
            }
        }

        self.emit_inst(MirInst::HandlerEnter {
            effect: target_effect.clone(),
        });
        let incoming_scope = self.snapshot_var_scope();
        for (operation, cell) in &operation_cells {
            self.active_effect_cells
                .insert((target_effect.clone(), operation.clone()), cell.clone());
        }
        for (operation, cell) in &default_cells {
            self.active_effect_cells
                .insert((target_effect.clone(), operation.clone()), cell.clone());
        }
        self.active_effect_handlers
            .insert(target_effect.clone(), plan.clone());
        let result = self.lower_expr(handled);
        self.restore_var_scope(&incoming_scope);
        for (operation, cell) in &operation_cells {
            self.active_effect_cells
                .insert((target_effect.clone(), operation.clone()), cell.clone());
        }
        for (operation, cell) in &default_cells {
            self.active_effect_cells
                .insert((target_effect.clone(), operation.clone()), cell.clone());
        }
        self.active_effect_handlers
            .insert(target_effect.clone(), plan);

        // Normal-completion: if zero-resume clauses exist, jump to exit block.
        let mut lowered_result = if let Some((exit_block, result_param)) = &zero_resume_exit {
            if self.current_block().terminator.is_none() {
                let body_val = result.clone().or_else(|| {
                    if handled.ty == Type::Unit {
                        let u = self.new_value();
                        self.emit_inst(MirInst::Const {
                            dest: u.clone(),
                            literal: MirLiteral::Unit,
                        });
                        Some(u)
                    } else {
                        None
                    }
                });
                if let Some(v) = body_val {
                    self.ensure_jump_to(exit_block.clone(), vec![v]);
                }
            }
            self.switch_to(exit_block.clone());
            Some(result_param.clone())
        } else {
            result.clone()
        };
        self.active_zero_resume_exit = prev_zero_resume_exit;

        // Callback stacking: unwind the chain after handle returns.
        // The chain closure was built up per-invocation inside the callback.
        // Calling chain(body_result) applies all post-resume transforms in LIFO order.
        if self.current_block().terminator.is_none() {
            let stacking_chain = self
                .stacking_chains
                .iter()
                .find(|((eff, _op), _)| eff == &target_effect)
                .map(|(_, chain)| chain.clone());
            if let Some(chain) = stacking_chain {
                let handled_value = if let Some(value) = lowered_result.clone() {
                    value
                } else if handled.ty == Type::Unit {
                    let unit = self.new_value();
                    self.emit_inst(MirInst::Const {
                        dest: unit.clone(),
                        literal: MirLiteral::Unit,
                    });
                    unit
                } else {
                    self.emit_inst(MirInst::Unsupported {
                        detail: "callback stacking: handle expression expected a value, \
                                 but handled body produced none"
                            .to_string(),
                    });
                    return None;
                };
                let chain_fn = self.new_value();
                self.emit_inst(MirInst::StateCellLoad {
                    dest: chain_fn.clone(),
                    cell: chain.chain_cell,
                });
                let final_result = self.new_value();
                self.emit_inst(MirInst::Call {
                    callee: MirCallee::Value(chain_fn),
                    args: vec![handled_value],
                    arg_types: vec![Type::Dynamic],
                    result: Some(final_result.clone()),
                    ret_type: Type::Dynamic,
                    callee_fail_result_abi: false,
                    capture_fail_result: false,
                    cc_manifest_id: "default".to_string(),
                });
                lowered_result = Some(final_result);
            }
        }

        if let Some(then_expr) = then_clause {
            if self.current_block().terminator.is_none() {
                let handled_value = if let Some(value) = lowered_result.clone() {
                    value
                } else if handled.ty == Type::Unit {
                    let unit = self.new_value();
                    self.emit_inst(MirInst::Const {
                        dest: unit.clone(),
                        literal: MirLiteral::Unit,
                    });
                    unit
                } else {
                    self.emit_inst(MirInst::Unsupported {
                        detail: "handle expression then-clause expected a value, but handled body produced none".to_string(),
                    });
                    return None;
                };

                if let HirExprKind::Lambda { params, body } = &then_expr.kind {
                    if params.len() != 1 {
                        self.emit_inst(MirInst::Unsupported {
                            detail: "handle then-clause lambda must accept exactly one parameter"
                                .to_string(),
                        });
                        return None;
                    }
                    let incoming_scope = self.snapshot_var_scope();
                    if let Some(param_name) = &params[0].name {
                        self.vars.insert(param_name.clone(), handled_value);
                        self.var_types
                            .insert(param_name.clone(), handled.ty.clone());
                    }
                    lowered_result = self.lower_expr(body);
                    self.restore_var_scope(&incoming_scope);
                } else {
                    let callee = self.lower_expr(then_expr)?;
                    let call_result = if handle_expr.ty == Type::Unit {
                        None
                    } else {
                        Some(self.new_value())
                    };
                    self.emit_inst(MirInst::Call {
                        callee: MirCallee::Value(callee),
                        args: vec![handled_value],
                        arg_types: vec![handled.ty.clone()],
                        result: call_result.clone(),
                        ret_type: handle_expr.ty.clone(),
                        callee_fail_result_abi: false,
                        capture_fail_result: false,
                        cc_manifest_id: "default".to_string(),
                    });
                    if let (Some(dest), Type::Sum(sum_ty)) = (&call_result, &handle_expr.ty) {
                        self.sum_value_types
                            .insert(dest.clone(), sum_ty.name.clone());
                    }
                    lowered_result = call_result;
                }
            } else {
                lowered_result = None;
            }
        }

        self.restore_var_scope(&incoming_scope);
        self.emit_inst(MirInst::HandlerExit {
            effect: target_effect,
        });
        for cell in release_cells {
            self.emit_inst(MirInst::Release { value: cell });
        }
        lowered_result
    }

    fn lower_call_expr(
        &mut self,
        expr: &HirExpr,
        func: &HirExpr,
        args: &[HirExpr],
        capture_fail_result: bool,
    ) -> Option<MirValueId> {
        let mut materialized_local_lambda_callee = None;
        if let HirExprKind::Call {
            func: factory_func,
            args: factory_args,
        } = &func.kind
            && let HirExprKind::Var(factory_name) = &factory_func.kind
            && let Some(template) = self.lambda_factories.get(factory_name).cloned()
            && !capture_fail_result
            && template.outer_params.len() == factory_args.len()
            && template.lambda_params.len() == args.len()
        {
            let incoming_scope = self.snapshot_var_scope();
            for capture_name in &template.captures {
                let capture_index = template
                    .outer_params
                    .iter()
                    .position(|param| param == capture_name)?;
                let capture_arg = factory_args.get(capture_index)?;
                let capture_value = self.lower_expr(capture_arg)?;
                self.vars
                    .insert(capture_name.clone(), capture_value.clone());
                self.var_types
                    .insert(capture_name.clone(), capture_arg.ty.clone());
                if let Type::Record(record_ty) = &capture_arg.ty {
                    self.var_record_types
                        .insert(capture_name.clone(), record_ty.name.clone());
                }
                if let Type::AnonRecord(row) = &capture_arg.ty
                    && let Some(record_type) = self.infer_unique_record_type_for_row(row)
                {
                    self.var_record_types
                        .insert(capture_name.clone(), record_type);
                }
            }
            for (param, arg_expr) in template.lambda_params.iter().zip(args) {
                let Some(param_name) = &param.name else {
                    continue;
                };
                let arg_value = self.lower_expr(arg_expr)?;
                self.vars.insert(param_name.clone(), arg_value.clone());
                self.var_types
                    .insert(param_name.clone(), arg_expr.ty.clone());
                if let Type::Record(record_ty) = &arg_expr.ty {
                    self.var_record_types
                        .insert(param_name.clone(), record_ty.name.clone());
                }
            }
            let result = if let HirExprKind::Lambda { params, body } = &template.lambda_body.kind {
                let expected_ty = if matches!(expr.ty, Type::Function(_)) {
                    expr.ty.clone()
                } else if matches!(template.lambda_body.ty, Type::Function(_)) {
                    template.lambda_body.ty.clone()
                } else {
                    synth_lambda_type(params, body)
                };
                self.lower_lambda_to_closure_value(
                    &template.lambda_body,
                    params,
                    body,
                    Some(&expected_ty),
                    false,
                    false,
                )
            } else {
                self.lower_expr(&template.lambda_body)
            };
            self.restore_var_scope(&incoming_scope);
            return result;
        }
        if let HirExprKind::Lambda { params, body } = &func.kind
            && !capture_fail_result
        {
            if params.len() != args.len() {
                return None;
            }
            let incoming_scope = self.snapshot_var_scope();
            for (param, arg_expr) in params.iter().zip(args) {
                let Some(param_name) = &param.name else {
                    continue;
                };
                let arg_value = self.lower_expr(arg_expr)?;
                self.vars.insert(param_name.clone(), arg_value.clone());
                self.var_types
                    .insert(param_name.clone(), arg_expr.ty.clone());
                if let Type::Record(record_ty) = &arg_expr.ty {
                    self.var_record_types
                        .insert(param_name.clone(), record_ty.name.clone());
                }
            }
            let result = if let HirExprKind::Lambda {
                params: inner_params,
                body: inner_body,
            } = &body.kind
            {
                let expected_ty = if matches!(expr.ty, Type::Function(_)) {
                    expr.ty.clone()
                } else if matches!(body.ty, Type::Function(_)) {
                    body.ty.clone()
                } else {
                    synth_lambda_type(inner_params, inner_body)
                };
                self.lower_lambda_to_closure_value(
                    body,
                    inner_params,
                    inner_body,
                    Some(&expected_ty),
                    false,
                    false,
                )
            } else {
                self.lower_expr(body)
            };
            self.restore_var_scope(&incoming_scope);
            return result;
        }
        if let HirExprKind::Var(name) = &func.kind
            && !self.vars.contains_key(name)
            && let Some(local_lambda) = self.local_lambdas.get(name).cloned()
        {
            let incoming_scope = self.snapshot_var_scope();
            for capture in &local_lambda.captures {
                self.vars
                    .insert(capture.name.clone(), capture.value.clone());
                self.var_types
                    .insert(capture.name.clone(), capture.ty.clone());
                if let Some(record_type) = &capture.record_type {
                    self.var_record_types
                        .insert(capture.name.clone(), record_type.clone());
                }
            }
            let synthesized_ty = if matches!(func.ty, Type::Function(_)) {
                func.ty.clone()
            } else {
                let synthesized_ret = if expr.ty == Type::Dynamic {
                    match &local_lambda.body.kind {
                        HirExprKind::Lambda { params, body }
                            if !matches!(local_lambda.body.ty, Type::Function(_)) =>
                        {
                            synth_lambda_type(params, body)
                        }
                        _ => local_lambda.body.ty.clone(),
                    }
                } else {
                    expr.ty.clone()
                };
                Type::Function(FunctionType::pure(
                    args.iter().map(|arg| arg.ty.clone()).collect(),
                    synthesized_ret,
                ))
            };
            let synthesized_expr = HirExpr {
                kind: HirExprKind::Lambda {
                    params: local_lambda.params.clone(),
                    body: Box::new(local_lambda.body.clone()),
                },
                ty: synthesized_ty,
                span: func.span,
            };
            let closure_value = self.lower_lambda_to_closure_value(
                &synthesized_expr,
                &local_lambda.params,
                &local_lambda.body,
                Some(&synthesized_expr.ty),
                false,
                false,
            )?;
            self.restore_var_scope(&incoming_scope);
            materialized_local_lambda_callee = Some(closure_value);
        }
        if let HirExprKind::Var(name) = &func.kind
            && !capture_fail_result
        {
            let lowered_op = match name.as_str() {
                "bit_and" if args.len() == 2 => Some((Some(MirBinaryOp::BitAnd), None)),
                "bit_or" if args.len() == 2 => Some((Some(MirBinaryOp::BitOr), None)),
                "bit_xor" if args.len() == 2 => Some((Some(MirBinaryOp::BitXor), None)),
                "shift_left" if args.len() == 2 => Some((Some(MirBinaryOp::ShiftLeft), None)),
                "shift_right" if args.len() == 2 => Some((Some(MirBinaryOp::ShiftRight), None)),
                "shift_right_unsigned" if args.len() == 2 => {
                    Some((Some(MirBinaryOp::ShiftRightUnsigned), None))
                }
                "wrapping_add" if args.len() == 2 => Some((Some(MirBinaryOp::WrappingAdd), None)),
                "wrapping_sub" if args.len() == 2 => Some((Some(MirBinaryOp::WrappingSub), None)),
                "wrapping_mul" if args.len() == 2 => Some((Some(MirBinaryOp::WrappingMul), None)),
                "bit_not" if args.len() == 1 => Some((None, Some(MirUnaryOp::BitNot))),
                "popcount" if args.len() == 1 => Some((None, Some(MirUnaryOp::Popcount))),
                "leading_zeros" if args.len() == 1 => Some((None, Some(MirUnaryOp::LeadingZeros))),
                "trailing_zeros" if args.len() == 1 => {
                    Some((None, Some(MirUnaryOp::TrailingZeros)))
                }
                _ => None,
            };

            if let Some((binary_op, unary_op)) = lowered_op {
                if let Some(op) = binary_op {
                    let lhs = self.lower_expr(&args[0])?;
                    let rhs = self.lower_expr(&args[1])?;
                    let dest = self.new_value();
                    self.emit_inst(MirInst::Binary {
                        dest: dest.clone(),
                        op,
                        left: lhs,
                        right: rhs,
                    });
                    return Some(dest);
                }
                if let Some(op) = unary_op {
                    let operand = self.lower_expr(&args[0])?;
                    let dest = self.new_value();
                    self.emit_inst(MirInst::Unary {
                        dest: dest.clone(),
                        op,
                        operand,
                    });
                    return Some(dest);
                }
            }
        }
        // Internal intrinsic: __kea_internal_capture_store(cell, value) -> Unit
        // Used by callback stacking to store pre-resume bindings into state cells.
        if let HirExprKind::Var(name) = &func.kind
            && name == "__kea_internal_capture_store"
            && args.len() == 2
        {
            let cell = self.lower_expr(&args[0])?;
            let value = self.lower_expr(&args[1])?;
            self.emit_inst(MirInst::StateCellStore { cell, value });
            let unit = self.new_value();
            self.emit_inst(MirInst::Const {
                dest: unit.clone(),
                literal: MirLiteral::Int(0),
            });
            return Some(unit);
        }
        // Safety guard: reject user code calling the internal intrinsic with wrong arity
        if let HirExprKind::Var(name) = &func.kind
            && name == "__kea_internal_capture_store"
        {
            self.emit_inst(MirInst::Unsupported {
                detail: "__kea_internal_capture_store is an internal compiler function, not callable from user code".to_string(),
            });
            return None;
        }
        if let HirExprKind::Var(name) = &func.kind
            && !capture_fail_result
            && (name.ends_with(".try_from") || name == "try_from")
            && let Some(result) = self.lower_fixed_width_try_from_call(expr, name, args)
        {
            return Some(result);
        }
        if let HirExprKind::Var(name) = &func.kind
            && !capture_fail_result
            && let Some((effect, operation)) = direct_capability_operation(name)
            && self.lookup_effect_cell(effect, operation).is_none()
        {
            let mut lowered_args = Vec::with_capacity(args.len());
            for arg in args {
                lowered_args.push(self.lower_expr(arg)?);
            }
            let result = if expr.ty == Type::Unit {
                None
            } else {
                Some(self.new_value())
            };
            self.emit_inst(MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                effect: effect.to_string(),
                operation: operation.to_string(),
                args: lowered_args,
                result: result.clone(),
            });
            return result;
        }
        if let HirExprKind::Var(name) = &func.kind
            && !capture_fail_result
            && let Some(op_info) = self.effect_operations.get(name).cloned()
        {
            let effect = op_info.effect;
            let operation = op_info.operation;
            // Zero-resume: Never-returning operations have no continuation to resume.
            // If a handler clause registered a cell for this op, invoke the callback
            // and jump to the exit block (the clause body becomes the handle result).
            // Otherwise fall through to the runtime abort path.
            if op_info.returns_never {
                let mut lowered_args = Vec::with_capacity(args.len());
                for arg in args {
                    lowered_args.push(self.lower_expr(arg)?);
                }
                if let Some(cell) = self.lookup_effect_cell(&effect, &operation) {
                    // Zero-resume handler clause: invoke callback, jump to exit block.
                    let callback_result = self.new_value();
                    self.emit_inst(MirInst::Call {
                        callee: MirCallee::Value(cell),
                        args: lowered_args,
                        arg_types: vec![Type::Dynamic; op_info.arity],
                        result: Some(callback_result.clone()),
                        ret_type: Type::Dynamic,
                        callee_fail_result_abi: false,
                        capture_fail_result: false,
                        cc_manifest_id: "default".to_string(),
                    });
                    if let Some((exit_block, _)) = self.active_zero_resume_exit.clone() {
                        self.set_terminator(MirTerminator::Jump {
                            target: exit_block,
                            args: vec![callback_result],
                        });
                    }
                } else {
                    // No handler: runtime abort path.
                    self.emit_inst(MirInst::EffectOp {
                        class: MirEffectOpClass::ZeroResume,
                        effect: effect.clone(),
                        operation: operation.clone(),
                        args: lowered_args,
                        result: None,
                    });
                    self.set_terminator(MirTerminator::Unreachable);
                }
                return None;
            }
            if let Some(cell) = self.lookup_effect_cell(&effect, &operation) {
                let lowering = {
                    let Some(plan) = self.active_effect_handlers.get(&effect) else {
                        self.emit_inst(MirInst::Unsupported {
                            detail: format!(
                                "effect operation `{effect}.{operation}` is not yet supported in compiled handler lowering (missing handler operation plan for effect `{effect}`)"
                            ),
                        });
                        return None;
                    };
                    let Some(lowering) = plan.operation_lowering.get(&operation).copied() else {
                        self.emit_inst(MirInst::Unsupported {
                            detail: format!(
                                "effect operation `{effect}.{operation}` is not yet supported in compiled handler lowering (missing handler operation plan)"
                            ),
                        });
                        return None;
                    };
                    lowering
                };
                match lowering {
                    HandlerCellOpLowering::InvokeCallback {
                        arity,
                        returns_unit,
                    } => {
                        if args.len() != arity {
                            self.emit_inst(MirInst::Unsupported {
                                detail: format!(
                                    "handled operation `{effect}.{operation}` expected {arity} arg(s) for callback lowering"
                                ),
                            });
                            return None;
                        }
                        let mut lowered_args = Vec::with_capacity(args.len());
                        for arg in args {
                            lowered_args.push(self.lower_expr(arg)?);
                        }
                        let callback_result = if returns_unit || expr.ty == Type::Unit {
                            None
                        } else {
                            Some(self.new_value())
                        };
                        self.emit_inst(MirInst::Call {
                            callee: MirCallee::Value(cell),
                            args: lowered_args,
                            arg_types: vec![Type::Dynamic; arity],
                            result: callback_result.clone(),
                            ret_type: if returns_unit {
                                Type::Unit
                            } else {
                                expr.ty.clone()
                            },
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        });
                        return callback_result;
                    }
                }
            }
            let mut lowered_args = Vec::with_capacity(args.len());
            for arg in args {
                lowered_args.push(self.lower_expr(arg)?);
            }
            let result = if expr.ty == Type::Unit {
                None
            } else {
                Some(self.new_value())
            };
            self.emit_inst(MirInst::EffectOp {
                class: MirEffectOpClass::Dispatch,
                effect,
                operation,
                args: lowered_args,
                result: result.clone(),
            });
            return result;
        }
        if let HirExprKind::Var(name) = &func.kind
            && is_namespaced_symbol_name(name)
            && !self.effect_operations.contains_key(name)
            && !self.known_function_types.contains_key(name)
            && ptr_intrinsic_symbol(name).is_none()
            && !self.intrinsic_symbols.contains_key(name)
            && try_resolve_trait_dispatch_callee(name, args, &self.known_function_types, Some(&self.var_types)).is_none()
            && try_resolve_trait_dispatch_callee_by_ret(name, &expr.ty, &self.known_function_types)
                .is_none()
        {
            self.emit_inst(MirInst::Unsupported {
                detail: format!("unresolved qualified call target `{name}`"),
            });
            return None;
        }
        let callee_fail_result_abi = match &func.kind {
            HirExprKind::Var(name) => self.var_types.get(name).map_or_else(
                || uses_fail_result_abi_from_type(&func.ty),
                uses_fail_result_abi_from_type,
            ),
            _ => uses_fail_result_abi_from_type(&func.ty),
        };

        let callee = if let Some(closure_value) = materialized_local_lambda_callee {
            MirCallee::Value(closure_value)
        } else {
            match &func.kind {
                HirExprKind::Var(name) if self.vars.contains_key(name) => {
                    let callee_value = self.lower_expr(func)?;
                    MirCallee::Value(callee_value)
                }
                HirExprKind::Var(name) => {
                    if let Some(symbol) = self.intrinsic_symbols.get(name) {
                        MirCallee::External(symbol.clone())
                    } else if let Some(symbol) = ptr_intrinsic_symbol(name) {
                        MirCallee::External(symbol.to_string())
                    } else if self.known_function_types.contains_key(name) {
                        MirCallee::Local(self.canonical_known_function_name(name))
                    } else if is_namespaced_symbol_name(name) {
                        // Try to resolve as a trait method dispatch via first-argument type
                        // (e.g. `Encode.encode(x: Point)` → `Encode.Point.encode`) or via
                        // the call expression's return type (e.g. `Decode.decode(j) -> Option Point`
                        // → `Decode.Point.decode`).
                        if let Some(resolved) = try_resolve_trait_dispatch_callee(
                            name,
                            args,
                            &self.known_function_types,
                            Some(&self.var_types),
                        )
                        .or_else(|| {
                            try_resolve_trait_dispatch_callee_by_ret(
                                name,
                                &expr.ty,
                                &self.known_function_types,
                            )
                        }) {
                            MirCallee::Local(resolved)
                        } else {
                            MirCallee::External(name.clone())
                        }
                    } else {
                        MirCallee::Local(name.clone())
                    }
                }
                _ => {
                    let callee_value = self.lower_expr(func)?;
                    MirCallee::Value(callee_value)
                }
            }
        };
        let dispatch_effects = match &callee {
            MirCallee::Local(name) => self
                .known_function_dispatch_effects
                .get(name)
                .cloned()
                .unwrap_or_default(),
            MirCallee::Value(_) => self.dispatch_effects_for_function_expr(func),
            _ => Vec::new(),
        };

        let mut lowered_args = Vec::with_capacity(args.len());
        let mut arg_types = Vec::with_capacity(args.len());
        let expected_param_types: Option<Vec<Type>> = match (&func.ty, &func.kind) {
            (Type::Function(ft), _) => Some(ft.params.clone()),
            (_, HirExprKind::Var(name)) => self.known_function_types.get(name).and_then(|ty| {
                if let Type::Function(ft) = ty {
                    Some(ft.params.clone())
                } else {
                    None
                }
            }),
            _ => None,
        };
        for (idx, arg) in args.iter().enumerate() {
            let expected = expected_param_types.as_ref().and_then(|tys| tys.get(idx));
            if let HirExprKind::Var(name) = &arg.kind
                && let Some(local_lambda) = self.local_lambdas.get(name).cloned()
            {
                let incoming_scope = self.snapshot_var_scope();
                for capture in &local_lambda.captures {
                    self.vars
                        .insert(capture.name.clone(), capture.value.clone());
                    self.var_types
                        .insert(capture.name.clone(), capture.ty.clone());
                    if let Some(record_type) = &capture.record_type {
                        self.var_record_types
                            .insert(capture.name.clone(), record_type.clone());
                    }
                }
                let synthesized_ty = expected.cloned().unwrap_or_else(|| arg.ty.clone());
                let synthesized_expr = HirExpr {
                    kind: HirExprKind::Lambda {
                        params: local_lambda.params.clone(),
                        body: Box::new(local_lambda.body.clone()),
                    },
                    ty: synthesized_ty.clone(),
                    span: arg.span,
                };
                let value = self.lower_lambda_to_closure_value(
                    &synthesized_expr,
                    &local_lambda.params,
                    &local_lambda.body,
                    expected,
                    false,
                    false,
                )?;
                self.restore_var_scope(&incoming_scope);
                arg_types.push(expected.cloned().unwrap_or(synthesized_ty));
                lowered_args.push(value);
                continue;
            }
            if let HirExprKind::Lambda { params, body } = &arg.kind {
                let value = self.lower_lambda_to_closure_value(
                    arg,
                    params,
                    body.as_ref(),
                    expected,
                    false,
                    false,
                )?;
                arg_types.push(expected.cloned().unwrap_or_else(|| arg.ty.clone()));
                lowered_args.push(value);
                continue;
            }
            arg_types.push(arg.ty.clone());
            lowered_args.push(self.lower_expr(arg)?);
        }
        if let HirExprKind::Var(name) = &func.kind
            && let Some(extra_arg) = ptr_intrinsic_extra_int_arg(name, &arg_types, &expr.ty)
        {
            let extra_value = self.new_value();
            self.emit_inst(MirInst::Const {
                dest: extra_value.clone(),
                literal: MirLiteral::Int(extra_arg),
            });
            arg_types.push(Type::Int);
            lowered_args.push(extra_value);
        }
        for dispatch_op_key in dispatch_effects {
            let Some((effect, operation)) = dispatch_op_key.split_once('.') else {
                self.emit_inst(MirInst::Unsupported {
                    detail: format!("invalid dispatch operation key `{dispatch_op_key}`"),
                });
                return None;
            };
            let Some(cell) = self.lookup_effect_cell(effect, operation) else {
                self.emit_inst(MirInst::Unsupported {
                    detail: format!(
                        "missing active handler cell for operation `{dispatch_op_key}` in call lowering"
                    ),
                });
                return None;
            };
            lowered_args.push(cell);
            arg_types.push(Type::Dynamic);
        }

        let inferred_ret_type = match (&func.ty, &func.kind) {
            (Type::Function(ft), _) => Some(ft.ret.as_ref().clone()),
            (_, HirExprKind::Var(name)) => self.known_function_types.get(name).and_then(|ty| {
                if let Type::Function(ft) = ty {
                    Some(ft.ret.as_ref().clone())
                } else {
                    None
                }
            }),
            _ => None,
        };
        let call_ret_type = match (&expr.ty, inferred_ret_type) {
            // Always trust known unit-return signatures so codegen does not
            // expect a value from unit-return callees.
            (_, Some(Type::Unit)) => Type::Unit,
            // Dynamic/variable expression types should defer to known callee
            // signatures when available.
            (Type::Dynamic, Some(inferred)) | (Type::Var(_), Some(inferred)) => inferred,
            // Unit-typed call expressions without a better signature stay unit.
            (Type::Unit, Some(inferred)) => inferred,
            (Type::Unit, None) => Type::Unit,
            _ => expr.ty.clone(),
        };

        // When capturing the Fail-ABI result (catch), always allocate a result
        // variable even for Unit-returning callees — the variable holds the
        // runtime Result handle (a pointer), not the logical return value.
        let result = if call_ret_type == Type::Unit && !capture_fail_result {
            None
        } else {
            Some(self.new_value())
        };

        self.emit_inst(MirInst::Call {
            callee,
            args: lowered_args,
            arg_types,
            result: result.clone(),
            ret_type: call_ret_type.clone(),
            callee_fail_result_abi,
            capture_fail_result,
            cc_manifest_id: "default".to_string(),
        });
        if let Some(dest) = &result
            && let Some(sum_type) = self.infer_sum_type_from_type(&call_ret_type)
        {
            self.sum_value_types.insert(dest.clone(), sum_type);
        }
        // If `call_ret_type` didn't give us a sum type but the callee is a
        // known unambiguous constructor (e.g. `Some`, `Ok`), record the sum
        // type from the ctor candidate table so that equality dispatch can
        // identify the type of the resulting value.
        if let Some(dest) = &result
            && !self.sum_value_types.contains_key(dest)
            && let HirExprKind::Var(callee_name) = &func.kind
            && let Some(candidates) = self.sum_ctor_candidates.get(callee_name)
            && candidates.len() == 1
            && candidates[0].arity == args.len()
        {
            self.sum_value_types
                .insert(dest.clone(), candidates[0].sum_type.clone());
        }
        if let Some(dest) = &result
            && let Some(record_type) = self.infer_record_type_from_type(&call_ret_type)
        {
            self.record_value_types.insert(dest.clone(), record_type);
        }
        if let Some(dest) = &result
            && let Type::Tuple(items) = &call_ret_type
        {
            self.tuple_value_types.insert(dest.clone(), items.clone());
        }
        result
    }

    fn resolve_eq_trait_callee_for_type(&self, ty: &Type) -> Option<String> {
        let type_name = match ty {
            Type::Record(record) => record.name.as_str(),
            Type::Sum(sum) => sum.name.as_str(),
            _ => return None,
        };

        let mut best: Option<(usize, String)> = None;
        for (name, scheme_ty) in &self.known_function_types {
            // Accept both plain `.eq` names and monomorphized variants (`Eq.Option.eq$m3$Int`).
            // Monomorphized names use the format `{base}$m{id}[${type_suffix}]`.
            let base_name = name.split("$m").next().unwrap_or(name.as_str());
            if !base_name.ends_with(".eq") {
                continue;
            }
            let Type::Function(ft) = scheme_ty else {
                continue;
            };
            if ft.params.len() != 2 {
                continue;
            }
            if !same_nominal_equality_type(ty, &ft.params[0])
                || !same_nominal_equality_type(ty, &ft.params[1])
            {
                continue;
            }
            let score = if base_name == format!("Eq.{type_name}.eq") {
                // Monomorphized exact match scores highest; unspecialized generic is next.
                if name.contains("$m") { 5 } else { 4 }
            } else if base_name.ends_with(&format!(".{type_name}.eq")) {
                3
            } else if base_name == "Eq.eq" {
                2
            } else {
                1
            };
            if best.as_ref().is_none_or(|(best_score, _)| score > *best_score) {
                best = Some((score, name.clone()));
            }
        }
        best.map(|(_, name)| self.canonical_known_function_name(&name))
    }

    fn lower_eq_via_trait_call(
        &mut self,
        op: BinOp,
        left: &HirExpr,
        right: &HirExpr,
    ) -> Option<MirValueId> {
        let left_ty = self.resolve_equality_operand_type(left);
        let right_ty = self.resolve_equality_operand_type(right);
        if !same_nominal_equality_type(&left_ty, &right_ty) {
            return None;
        }
        let callee_name = self.resolve_eq_trait_callee_for_type(&left_ty)?;

        let left_value = self.lower_expr(left)?;
        let right_value = self.lower_expr(right)?;
        let eq_dest = self.new_value();
        // Normalize both arg types to left_ty to avoid ABI issues when the two
        // Option/Sum representations differ in their variant encoding (e.g. one
        // has empty variants from a call result and the other has explicit variants
        // from a constructor literal).
        self.emit_inst(MirInst::Call {
            callee: MirCallee::Local(callee_name),
            args: vec![left_value, right_value],
            arg_types: vec![left_ty.clone(), left_ty],
            result: Some(eq_dest.clone()),
            ret_type: Type::Bool,
            callee_fail_result_abi: false,
            capture_fail_result: false,
            cc_manifest_id: "default".to_string(),
        });
        if op == BinOp::Eq {
            return Some(eq_dest);
        }
        let neq_dest = self.new_value();
        self.emit_inst(MirInst::Unary {
            dest: neq_dest.clone(),
            op: MirUnaryOp::Not,
            operand: eq_dest,
        });
        Some(neq_dest)
    }

    fn resolve_equality_operand_type(&self, expr: &HirExpr) -> Type {
        match &expr.kind {
            HirExprKind::Var(name) => {
                let fallback = self
                    .var_types
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| expr.ty.clone());
                // For polymorphic sum types (e.g. `List a` inside a generic function),
                // fall through to sum_value_types which stores only the nominal name
                // (without type args).  This allows is_concrete_nominal_equality_type to
                // accept the type and route through lower_eq_via_trait_call.
                let is_polymorphic_sum = matches!(&fallback, Type::Sum(sum)
                    if sum.type_args.iter().any(type_contains_inference_var));
                if fallback != Type::Dynamic && !is_polymorphic_sum {
                    return fallback;
                }
                if let Some(record_type) = self.var_record_types.get(name) {
                    return Type::Record(RecordType {
                        name: record_type.clone(),
                        params: vec![],
                    });
                }
                if let Some(value_id) = self.vars.get(name)
                    && let Some(sum_type) = self.sum_value_types.get(value_id)
                {
                    return Type::Sum(SumType {
                        name: sum_type.clone(),
                        type_args: vec![],
                    });
                }
                fallback
            }
            // For direct call expressions (e.g. `f() == Some(x)` without a let binding),
            // look up the callee's return type from known_function_types so that equality
            // dispatch can identify the nominal sum type without requiring an intermediate
            // variable binding.
            HirExprKind::Call { func, .. } => {
                if matches!(expr.ty, Type::Dynamic | Type::Var(_))
                    && let HirExprKind::Var(name) = &func.kind
                    && let Some(sum_type) = self.infer_sum_type_for_known_function_return(name)
                {
                    return Type::Sum(SumType {
                        name: sum_type,
                        type_args: vec![],
                    });
                }
                expr.ty.clone()
            }
            _ => expr.ty.clone(),
        }
    }

    fn infer_sum_type_for_known_function_return(&self, name: &str) -> Option<String> {
        let ty = self.known_function_types.get(name)?;
        let Type::Function(ft) = ty else {
            return None;
        };
        self.infer_sum_type_from_type(&ft.ret)
    }

    fn dispatch_effects_for_function_expr(&self, expr: &HirExpr) -> Vec<String> {
        match &expr.ty {
            Type::Function(ft) => self.dispatch_effects_for_effect_row(&ft.effects),
            _ => {
                if let HirExprKind::Var(name) = &expr.kind {
                    if let Some(Type::Function(ft)) = self.var_types.get(name) {
                        return self.dispatch_effects_for_effect_row(&ft.effects);
                    }
                    if let Some(Type::Function(ft)) = self.known_function_types.get(name) {
                        return self.dispatch_effects_for_effect_row(&ft.effects);
                    }
                }
                Vec::new()
            }
        }
    }

    fn dispatch_effects_for_effect_row(&self, effects: &EffectRow) -> Vec<String> {
        let mut dispatch_ops = BTreeSet::new();
        for (label, _) in &effects.row.fields {
            let effect = label.as_str();
            if effect == "Fail" {
                continue;
            }
            for op in self
                .effect_operations
                .values()
                .filter(|op| op.effect == effect)
                // Never-returning ops (IO.exit, Fail.fail) use the Direct/ZeroResume path;
                // they don't participate in the callback dispatch mechanism and have no cell.
                .filter(|op| !op.returns_never)
            {
                dispatch_ops.insert(format!("{effect}.{}", op.operation));
            }
        }
        dispatch_ops.into_iter().collect()
    }

    fn infer_record_type_from_call(&self, func: &HirExpr) -> Option<String> {
        if let Type::Function(ft) = &func.ty {
            return self.infer_record_type_from_type(ft.ret.as_ref());
        }
        if let HirExprKind::Var(name) = &func.kind
            && let Some(Type::Function(ft)) = self.known_function_types.get(name)
        {
            return self.infer_record_type_from_type(ft.ret.as_ref());
        }
        None
    }

    fn infer_record_type_from_type(&self, ty: &Type) -> Option<String> {
        match ty {
            Type::Record(record_ty) => Some(record_ty.name.clone()),
            Type::AnonRecord(row) => self.infer_unique_record_type_for_row(row),
            Type::Tuple(items) => Some(tuple_layout_name(items.len())),
            _ => None,
        }
    }

    fn infer_sum_type_from_type(&self, ty: &Type) -> Option<String> {
        match ty {
            Type::Sum(sum_ty) => Some(sum_ty.name.clone()),
            _ => None,
        }
    }

    fn resolve_const_name_for_var(&self, name: &str) -> Option<String> {
        if self.known_const_exprs.contains_key(name) {
            return Some(name.to_string());
        }
        let owner = self.const_owner_stack.last()?;
        let qualified = format!("{owner}.{name}");
        self.known_const_exprs
            .contains_key(&qualified)
            .then_some(qualified)
    }

    fn lower_named_const_expr(&mut self, name: &str, raw_expr: &AstExprKind) -> Option<MirValueId> {
        if self
            .const_lowering_stack
            .iter()
            .any(|active| active == name)
        {
            self.emit_inst(MirInst::Unsupported {
                detail: format!("circular const reference detected while lowering `{name}`"),
            });
            return None;
        }
        self.const_lowering_stack.push(name.to_string());
        if let Some((owner, _)) = name.rsplit_once('.') {
            self.const_owner_stack.push(owner.to_string());
        }
        let lowered = self.lower_raw_ast_expr(raw_expr);
        if name.contains('.') {
            self.const_owner_stack.pop();
        }
        self.const_lowering_stack.pop();
        lowered
    }

    fn lower_raw_ast_expr(&mut self, raw_expr: &AstExprKind) -> Option<MirValueId> {
        match raw_expr {
            AstExprKind::Lit(lit) => {
                let dest = self.new_value();
                self.emit_inst(MirInst::Const {
                    dest: dest.clone(),
                    literal: lower_literal(lit),
                });
                Some(dest)
            }
            AstExprKind::Var(name) => {
                if let Some(value) = self.vars.get(name) {
                    return Some(value.clone());
                }
                let qualified = self.resolve_const_name_for_var(name)?;
                let expr = self.known_const_exprs.get(&qualified)?.clone();
                self.lower_named_const_expr(&qualified, &expr)
            }
            AstExprKind::FieldAccess { expr, field } => {
                let AstExprKind::Var(owner) = &expr.node else {
                    return None;
                };
                let qualified = format!("{owner}.{}", field.node);
                let const_expr = self.known_const_exprs.get(&qualified)?.clone();
                self.lower_named_const_expr(&qualified, &const_expr)
            }
            AstExprKind::UnaryOp { op, operand } => {
                let operand = self.lower_raw_ast_expr(&operand.node)?;
                let dest = self.new_value();
                self.emit_inst(MirInst::Unary {
                    dest: dest.clone(),
                    op: lower_unaryop(op.node),
                    operand,
                });
                Some(dest)
            }
            AstExprKind::BinaryOp { op, left, right } => {
                let left = self.lower_raw_ast_expr(&left.node)?;
                let right = self.lower_raw_ast_expr(&right.node)?;
                let dest = self.new_value();
                self.emit_inst(MirInst::Binary {
                    dest: dest.clone(),
                    op: lower_binop(op.node),
                    left,
                    right,
                });
                Some(dest)
            }
            AstExprKind::AnonRecord { fields, spread } => {
                if spread.is_some() {
                    return None;
                }
                let required = fields
                    .iter()
                    .map(|(name, _)| name.node.clone())
                    .collect::<BTreeSet<_>>();
                let record_type = anon_record_layout_name(&required);
                if !self
                    .layouts
                    .records
                    .iter()
                    .any(|record| record.name == record_type)
                {
                    return None;
                }
                let mut lowered_fields = Vec::with_capacity(fields.len());
                for (field_name, field_expr) in fields {
                    lowered_fields.push((
                        field_name.node.clone(),
                        self.lower_raw_ast_expr(&field_expr.node)?,
                    ));
                }
                let dest = self.new_value();
                self.emit_inst(MirInst::RecordInit {
                    dest: dest.clone(),
                    record_type: record_type.clone(),
                    fields: lowered_fields,
                });
                self.record_value_types.insert(dest.clone(), record_type);
                Some(dest)
            }
            AstExprKind::Constructor { name, args } => {
                let candidates = self.sum_ctor_candidates.get(&name.node)?;
                let matching = candidates
                    .iter()
                    .filter(|candidate| candidate.arity == args.len())
                    .collect::<Vec<_>>();
                if matching.len() != 1 {
                    return None;
                }
                let selected = matching[0].clone();
                let mut fields = Vec::with_capacity(args.len());
                for arg in args {
                    fields.push(self.lower_raw_ast_expr(&arg.value.node)?);
                }
                let dest = self.new_value();
                let sum_type = selected.sum_type.clone();
                self.emit_inst(MirInst::SumInit {
                    dest: dest.clone(),
                    sum_type,
                    variant: name.node.clone(),
                    tag: selected.tag,
                    fields,
                });
                self.sum_value_types
                    .insert(dest.clone(), selected.sum_type.clone());
                Some(dest)
            }
            _ => None,
        }
    }

    fn lower_maybe_sum_tag_operand(
        &mut self,
        op: BinOp,
        operand_expr: &HirExpr,
        operand_value: MirValueId,
        other_expr: &HirExpr,
    ) -> MirValueId {
        if !matches!(op, BinOp::Eq | BinOp::Neq) {
            return operand_value;
        }
        if !matches!(other_expr.kind, HirExprKind::Lit(kea_ast::Lit::Int(_))) {
            return operand_value;
        }
        let Some(sum_type) = self.sum_value_types.get(&operand_value).cloned() else {
            return operand_value;
        };
        // Only rewrite sum-pointer comparisons that come from case-style tag checks.
        if !matches!(
            operand_expr.kind,
            HirExprKind::Var(_)
                | HirExprKind::Call { .. }
                | HirExprKind::SumConstructor { .. }
                | HirExprKind::SumPayloadAccess { .. }
                | HirExprKind::Raw(AstExprKind::Constructor { .. })
                | HirExprKind::Let { .. }
                | HirExprKind::Block(_)
        ) {
            return operand_value;
        }
        let tag_value = self.new_value();
        self.emit_inst(MirInst::SumTagLoad {
            dest: tag_value.clone(),
            sum: operand_value,
            sum_type,
        });
        tag_value
    }

    /// When a narrow int (`IntN`) and `Int` (i64) are operands to a binary
    /// operation, widen the narrow side to `Int`.  This handles the common
    /// case where an `Int8` variable is combined with an integer literal (which
    /// defaults to `Int`) without requiring explicit widening in user code.
    fn maybe_widen_mixed_int_operands(
        &mut self,
        left_ty: &Type,
        left: MirValueId,
        right_ty: &Type,
        right: MirValueId,
    ) -> (MirValueId, MirValueId) {
        let is_int = |ty: &Type| matches!(ty, Type::Int | Type::Dynamic);
        let narrow_widen_op = |ty: &Type| match ty {
            Type::IntN(_, kea_types::Signedness::Signed) => Some(MirUnaryOp::WidenSignedToInt),
            Type::IntN(_, kea_types::Signedness::Unsigned) => Some(MirUnaryOp::WidenUnsignedToInt),
            _ => None,
        };
        if is_int(right_ty)
            && let Some(op) = narrow_widen_op(left_ty)
        {
            let widened = self.new_value();
            self.emit_inst(MirInst::Unary {
                dest: widened.clone(),
                op,
                operand: left,
            });
            return (widened, right);
        }
        if is_int(left_ty)
            && let Some(op) = narrow_widen_op(right_ty)
        {
            let widened = self.new_value();
            self.emit_inst(MirInst::Unary {
                dest: widened.clone(),
                op,
                operand: right,
            });
            return (left, widened);
        }
        (left, right)
    }

    fn narrow_op_for_target(ty: &Type) -> Option<MirUnaryOp> {
        match ty {
            Type::IntN(kea_types::IntWidth::I8, kea_types::Signedness::Signed) => {
                Some(MirUnaryOp::NarrowToI8)
            }
            Type::IntN(kea_types::IntWidth::I16, kea_types::Signedness::Signed) => {
                Some(MirUnaryOp::NarrowToI16)
            }
            Type::IntN(kea_types::IntWidth::I32, kea_types::Signedness::Signed) => {
                Some(MirUnaryOp::NarrowToI32)
            }
            Type::IntN(kea_types::IntWidth::I8, kea_types::Signedness::Unsigned) => {
                Some(MirUnaryOp::NarrowToU8)
            }
            Type::IntN(kea_types::IntWidth::I16, kea_types::Signedness::Unsigned) => {
                Some(MirUnaryOp::NarrowToU16)
            }
            Type::IntN(kea_types::IntWidth::I32, kea_types::Signedness::Unsigned) => {
                Some(MirUnaryOp::NarrowToU32)
            }
            _ => None,
        }
    }

    fn integer_bounds_for_target(ty: &Type) -> Option<(i64, i64)> {
        match ty {
            Type::IntN(kea_types::IntWidth::I8, kea_types::Signedness::Signed) => {
                Some((i8::MIN as i64, i8::MAX as i64))
            }
            Type::IntN(kea_types::IntWidth::I16, kea_types::Signedness::Signed) => {
                Some((i16::MIN as i64, i16::MAX as i64))
            }
            Type::IntN(kea_types::IntWidth::I32, kea_types::Signedness::Signed) => {
                Some((i32::MIN as i64, i32::MAX as i64))
            }
            Type::IntN(kea_types::IntWidth::I64, kea_types::Signedness::Signed) => {
                Some((i64::MIN, i64::MAX))
            }
            Type::IntN(kea_types::IntWidth::I8, kea_types::Signedness::Unsigned) => {
                Some((0, u8::MAX as i64))
            }
            Type::IntN(kea_types::IntWidth::I16, kea_types::Signedness::Unsigned) => {
                Some((0, u16::MAX as i64))
            }
            Type::IntN(kea_types::IntWidth::I32, kea_types::Signedness::Unsigned) => {
                Some((0, u32::MAX as i64))
            }
            // Source `Int` is i64-backed in bootstrap; checked conversion to
            // UInt64 therefore only rejects negatives.
            Type::IntN(kea_types::IntWidth::I64, kea_types::Signedness::Unsigned) => {
                Some((0, i64::MAX))
            }
            _ => None,
        }
    }

    fn lower_fixed_width_try_from_call(
        &mut self,
        expr: &HirExpr,
        func_name: &str,
        args: &[HirExpr],
    ) -> Option<MirValueId> {
        if args.len() != 1 {
            return None;
        }
        let target_ty = try_from_target_type_from_name(func_name).or_else(|| {
            expr.ty.as_option().and_then(|inner| {
                if matches!(inner, Type::IntN(_, _)) {
                    Some(inner.clone())
                } else {
                    None
                }
            })
        })?;
        let option_ty = Type::option(target_ty.clone());
        let (min, max) = Self::integer_bounds_for_target(&target_ty)?;

        let source = self.lower_expr(&args[0])?;
        // `source_int` is an i64 used for bounds comparison.
        // `storage_value` is typed as `target_ty` for the SumInit payload.
        let (source_int, storage_value) = match &args[0].ty {
            Type::Int => {
                // Already i64; narrow to target type for storage.
                let narrow_op = Self::narrow_op_for_target(&target_ty);
                let storage = if let Some(op) = narrow_op {
                    let narrowed = self.new_value();
                    self.emit_inst(MirInst::Unary {
                        dest: narrowed.clone(),
                        op,
                        operand: source.clone(),
                    });
                    narrowed
                } else {
                    source.clone()
                };
                (source.clone(), storage)
            }
            // Some resolved callsites still carry `Dynamic` in HIR even when
            // type checking has already constrained the argument to integer
            // input for `*.try_from(...)`.
            Type::Dynamic => (source.clone(), source.clone()),
            Type::IntN(_, kea_types::Signedness::Signed) => {
                let widened = self.new_value();
                self.emit_inst(MirInst::Unary {
                    dest: widened.clone(),
                    op: MirUnaryOp::WidenSignedToInt,
                    operand: source.clone(),
                });
                // `source` is already the right target type (IntN).
                (widened, source.clone())
            }
            Type::IntN(_, kea_types::Signedness::Unsigned) => {
                let widened = self.new_value();
                self.emit_inst(MirInst::Unary {
                    dest: widened.clone(),
                    op: MirUnaryOp::WidenUnsignedToInt,
                    operand: source.clone(),
                });
                // `source` is already the right target type (IntN).
                (widened, source.clone())
            }
            _ => {
                self.emit_inst(MirInst::Unsupported {
                    detail: format!(
                        "fixed-width try_from expects integer input, got `{}`",
                        args[0].ty
                    ),
                });
                return None;
            }
        };

        let min_value = self.new_value();
        self.emit_inst(MirInst::Const {
            dest: min_value.clone(),
            literal: MirLiteral::Int(min),
        });
        let max_value = self.new_value();
        self.emit_inst(MirInst::Const {
            dest: max_value.clone(),
            literal: MirLiteral::Int(max),
        });

        let below_min = self.new_value();
        self.emit_inst(MirInst::Binary {
            dest: below_min.clone(),
            op: MirBinaryOp::Lt,
            left: source_int.clone(),
            right: min_value,
        });
        let above_max = self.new_value();
        self.emit_inst(MirInst::Binary {
            dest: above_max.clone(),
            op: MirBinaryOp::Gt,
            left: source_int.clone(),
            right: max_value,
        });
        let out_of_range = self.new_value();
        self.emit_inst(MirInst::Binary {
            dest: out_of_range.clone(),
            op: MirBinaryOp::Or,
            left: below_min,
            right: above_max,
        });

        let none_block = self.new_block();
        let some_block = self.new_block();
        let result = self.new_value();
        let join_block = self.new_block_with_params(vec![MirBlockParam {
            id: result.clone(),
            ty: option_ty,
        }]);
        self.set_terminator(MirTerminator::Branch {
            condition: out_of_range,
            then_block: none_block.clone(),
            else_block: some_block.clone(),
        });

        // Tag order matches option.kea source: None=tag0, Some=tag1.
        self.switch_to(none_block);
        let none_value = self.new_value();
        self.emit_inst(MirInst::Const {
            dest: none_value.clone(),
            literal: MirLiteral::Int(0),
        });
        self.ensure_jump_to(join_block.clone(), vec![none_value]);

        self.switch_to(some_block);
        let some_value = self.new_value();
        self.emit_inst(MirInst::SumInit {
            dest: some_value.clone(),
            sum_type: "Option".to_string(),
            variant: "Some".to_string(),
            tag: 1,
            fields: vec![storage_value],
        });
        self.sum_value_types
            .insert(some_value.clone(), "Option".to_string());
        self.ensure_jump_to(join_block.clone(), vec![some_value]);

        self.switch_to(join_block);
        self.sum_value_types
            .insert(result.clone(), "Option".to_string());
        Some(result)
    }

    fn lower_if(
        &mut self,
        expr: &HirExpr,
        condition: &HirExpr,
        then_branch: &HirExpr,
        else_branch: Option<&HirExpr>,
    ) -> Option<MirValueId> {
        let incoming_scope = self.snapshot_var_scope();
        let condition_value = self.lower_expr(condition)?;
        self.restore_var_scope(&incoming_scope);
        let then_block = self.new_block();
        let else_block = self.new_block();
        let mut join_params = Vec::new();
        let result_value = if expr.ty == Type::Unit {
            None
        } else {
            Some(self.new_value())
        };
        if let Some(value) = &result_value {
            join_params.push(MirBlockParam {
                id: value.clone(),
                ty: expr.ty.clone(),
            });
        }
        let join_block = self.new_block_with_params(join_params);

        self.set_terminator(MirTerminator::Branch {
            condition: condition_value,
            then_block: then_block.clone(),
            else_block: else_block.clone(),
        });

        self.switch_to(then_block);
        self.restore_var_scope(&incoming_scope);
        let then_value = self.lower_expr(then_branch);
        let then_terminated = self.current_block().terminator.is_some();
        if !then_terminated {
            let then_args = match &result_value {
                Some(_) => vec![then_value.clone()?],
                None => vec![],
            };
            self.ensure_jump_to(join_block.clone(), then_args);
        }

        self.switch_to(else_block);
        self.restore_var_scope(&incoming_scope);
        let else_value = else_branch.and_then(|branch| self.lower_expr(branch));
        let else_terminated = self.current_block().terminator.is_some();
        if !else_terminated {
            let else_args = match &result_value {
                Some(_) => vec![else_value.clone()?],
                None => vec![],
            };
            self.ensure_jump_to(join_block.clone(), else_args);
        }

        self.switch_to(join_block);
        self.restore_var_scope(&incoming_scope);
        if then_terminated && else_terminated {
            self.set_terminator(MirTerminator::Unreachable);
            return None;
        }
        if let Some(result) = &result_value {
            let mut record_type = match &expr.ty {
                Type::Record(record_ty) => Some(record_ty.name.clone()),
                Type::AnonRecord(row) => self.infer_unique_record_type_for_row(row),
                Type::Tuple(items) => Some(tuple_layout_name(items.len())),
                _ => None,
            };
            if record_type.is_none() {
                let mut branch_record_types = Vec::new();
                if !then_terminated
                    && let Some(value) = &then_value
                    && let Some(name) = self.record_value_types.get(value)
                {
                    branch_record_types.push(name.clone());
                }
                if !else_terminated
                    && let Some(value) = &else_value
                    && let Some(name) = self.record_value_types.get(value)
                {
                    branch_record_types.push(name.clone());
                }
                if let Some(first) = branch_record_types.first().cloned()
                    && branch_record_types.iter().all(|name| name == &first)
                {
                    record_type = Some(first);
                }
            }
            if let Some(name) = record_type {
                self.record_value_types.insert(result.clone(), name);
            }

            let mut sum_type = self.infer_sum_type_from_type(&expr.ty);
            if sum_type.is_none() {
                let mut branch_sum_types = Vec::new();
                if !then_terminated
                    && let Some(value) = &then_value
                    && let Some(name) = self.sum_value_types.get(value)
                {
                    branch_sum_types.push(name.clone());
                }
                if !else_terminated
                    && let Some(value) = &else_value
                    && let Some(name) = self.sum_value_types.get(value)
                {
                    branch_sum_types.push(name.clone());
                }
                if let Some(first) = branch_sum_types.first().cloned()
                    && branch_sum_types.iter().all(|name| name == &first)
                {
                    sum_type = Some(first);
                }
            }
            if let Some(name) = sum_type {
                self.sum_value_types.insert(result.clone(), name);
            }
        }
        result_value
    }

    fn bind_pattern(&mut self, pattern: &HirPattern, value_id: MirValueId, value_ty: &Type) {
        if let HirPattern::Var(name) = pattern {
            self.vars.insert(name.clone(), value_id.clone());
            self.var_types.insert(name.clone(), value_ty.clone());
            if let Some(record_type) = self.record_value_types.get(&value_id) {
                self.var_record_types
                    .insert(name.clone(), record_type.clone());
            } else if let Some(items) = self.tuple_value_types.get(&value_id) {
                // Propagate tuple layout name when the static value_ty is Dynamic
                // (e.g. a generic list element bound by a Cons pattern) but the
                // concrete type was recovered during SumPayloadLoad lowering.
                self.var_record_types
                    .insert(name.clone(), tuple_layout_name(items.len()));
            }
            match value_ty {
                Type::Record(record_ty) => {
                    self.var_record_types
                        .insert(name.clone(), record_ty.name.clone());
                }
                Type::AnonRecord(row) => {
                    if let Some(record_type) = self.infer_unique_record_type_for_row(row) {
                        self.var_record_types.insert(name.clone(), record_type);
                    }
                }
                Type::Tuple(items) => {
                    self.var_record_types
                        .insert(name.clone(), tuple_layout_name(items.len()));
                }
                _ => {}
            }
        }
    }

    fn infer_unique_record_type_for_row(&self, row: &kea_types::RowType) -> Option<String> {
        let required = row
            .fields
            .iter()
            .map(|(label, _)| label.as_str().to_string())
            .collect::<BTreeSet<_>>();
        self.infer_unique_record_type_for_fields(&required)
    }

    fn infer_unique_record_type_for_fields(&self, required: &BTreeSet<String>) -> Option<String> {
        let mut candidates = self
            .layouts
            .records
            .iter()
            .filter(|record| {
                required
                    .iter()
                    .all(|field| record.fields.iter().any(|f| f.name == *field))
            })
            .map(|record| record.name.clone());
        let first = candidates.next()?;
        if candidates.next().is_some() {
            None
        } else {
            Some(first)
        }
    }

    fn collect_record_update_chain<'a>(
        expr: &'a HirExpr,
        record_type: &str,
        updates: &mut Vec<(String, &'a HirExpr)>,
    ) -> &'a HirExpr {
        if let HirExprKind::RecordUpdate {
            record_type: inner_record_type,
            base,
            fields,
        } = &expr.kind
            && inner_record_type == record_type
        {
            let root = Self::collect_record_update_chain(base, record_type, updates);
            for (field_name, field_expr) in fields {
                updates.push((field_name.clone(), field_expr));
            }
            return root;
        }
        expr
    }

    fn lower_short_circuit_binary(
        &mut self,
        op: BinOp,
        left: &HirExpr,
        right: &HirExpr,
    ) -> Option<MirValueId> {
        let incoming_scope = self.snapshot_var_scope();
        let left_value = self.lower_expr(left)?;
        self.restore_var_scope(&incoming_scope);
        let rhs_block = self.new_block();
        let short_block = self.new_block();
        let result = self.new_value();
        let join_block = self.new_block_with_params(vec![MirBlockParam {
            id: result.clone(),
            ty: Type::Bool,
        }]);

        let (then_block, else_block, short_value) = match op {
            BinOp::And => (rhs_block.clone(), short_block.clone(), false),
            BinOp::Or => (short_block.clone(), rhs_block.clone(), true),
            _ => return None,
        };
        self.set_terminator(MirTerminator::Branch {
            condition: left_value,
            then_block,
            else_block,
        });

        self.switch_to(rhs_block);
        self.restore_var_scope(&incoming_scope);
        let rhs_value = self.lower_expr(right)?;
        self.ensure_jump_to(join_block.clone(), vec![rhs_value]);

        self.switch_to(short_block);
        self.restore_var_scope(&incoming_scope);
        let short_const = self.new_value();
        self.emit_inst(MirInst::Const {
            dest: short_const.clone(),
            literal: MirLiteral::Bool(short_value),
        });
        self.ensure_jump_to(join_block.clone(), vec![short_const]);

        self.switch_to(join_block);
        self.restore_var_scope(&incoming_scope);
        Some(result)
    }
}

fn lower_literal(lit: &kea_ast::Lit) -> MirLiteral {
    match lit {
        kea_ast::Lit::Int(value) => MirLiteral::Int(*value),
        kea_ast::Lit::Float(value) => MirLiteral::Float(*value),
        kea_ast::Lit::Bool(value) => MirLiteral::Bool(*value),
        kea_ast::Lit::Char(value) => MirLiteral::Char(*value),
        kea_ast::Lit::String(value) => MirLiteral::String(value.clone()),
        kea_ast::Lit::Unit => MirLiteral::Unit,
    }
}

fn lower_binop(op: BinOp) -> MirBinaryOp {
    match op {
        BinOp::Add => MirBinaryOp::Add,
        BinOp::Sub => MirBinaryOp::Sub,
        BinOp::Mul => MirBinaryOp::Mul,
        BinOp::Div => MirBinaryOp::Div,
        BinOp::Mod => MirBinaryOp::Mod,
        BinOp::Concat => MirBinaryOp::Concat,
        BinOp::Combine => MirBinaryOp::Combine,
        BinOp::Eq => MirBinaryOp::Eq,
        BinOp::Neq => MirBinaryOp::Neq,
        BinOp::Lt => MirBinaryOp::Lt,
        BinOp::Lte => MirBinaryOp::Lte,
        BinOp::Gt => MirBinaryOp::Gt,
        BinOp::Gte => MirBinaryOp::Gte,
        BinOp::And => MirBinaryOp::And,
        BinOp::Or => MirBinaryOp::Or,
        BinOp::In => MirBinaryOp::In,
        BinOp::NotIn => MirBinaryOp::NotIn,
    }
}

fn lower_unaryop(op: UnaryOp) -> MirUnaryOp {
    match op {
        UnaryOp::Neg => MirUnaryOp::Neg,
        UnaryOp::Not => MirUnaryOp::Not,
    }
}

fn is_primitive_equality_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Int
            | Type::Bool
            | Type::Char
            | Type::Float
            | Type::String
            | Type::Unit
            | Type::Dynamic
            | Type::IntN { .. }
            | Type::FloatN(_)
    )
}

fn is_concrete_nominal_equality_type(ty: &Type) -> bool {
    match ty {
        Type::Record(record) => !record.params.iter().any(type_contains_inference_var),
        Type::Sum(sum) => !sum.type_args.iter().any(type_contains_inference_var),
        _ => false,
    }
}

fn same_nominal_equality_type(query: &Type, candidate: &Type) -> bool {
    match (query, candidate) {
        (Type::Record(query_record), Type::Record(candidate_record)) => {
            query_record.name == candidate_record.name
                && query_record.params.len() == candidate_record.params.len()
                && query_record
                    .params
                    .iter()
                    .zip(candidate_record.params.iter())
                    .all(|(lhs, rhs)| {
                        lhs == rhs
                            || *lhs == Type::Dynamic
                            || *rhs == Type::Dynamic
                            || matches!(lhs, Type::Var(_))
                            || matches!(rhs, Type::Var(_))
                    })
        }
        (Type::Sum(query_sum), Type::Sum(candidate_sum)) => {
            if query_sum.name != candidate_sum.name {
                return false;
            }
            // If one side has erased type args (empty, e.g. from sum_ctor_candidates)
            // and the other side has only TypeVar/Dynamic args, accept as compatible.
            let q_len = query_sum.type_args.len();
            let c_len = candidate_sum.type_args.len();
            if q_len == 0 && candidate_sum.type_args.iter().all(|t| matches!(t, Type::Var(_) | Type::Dynamic)) {
                return true;
            }
            if c_len == 0 && query_sum.type_args.iter().all(|t| matches!(t, Type::Var(_) | Type::Dynamic)) {
                return true;
            }
            q_len == c_len
                && query_sum
                    .type_args
                    .iter()
                    .zip(candidate_sum.type_args.iter())
                    .all(|(lhs, rhs)| {
                        lhs == rhs
                            || *lhs == Type::Dynamic
                            || *rhs == Type::Dynamic
                            || matches!(lhs, Type::Var(_))
                            || matches!(rhs, Type::Var(_))
                    })
        }
        _ => query == candidate,
    }
}

fn type_contains_inference_var(ty: &Type) -> bool {
    match ty {
        Type::Var(_) => true,
        Type::Set(inner) => type_contains_inference_var(inner),
        Type::Map(key, value) => {
            type_contains_inference_var(key) || type_contains_inference_var(value)
        }
        Type::Tuple(items) => items.iter().any(type_contains_inference_var),
        Type::Record(record) => record.params.iter().any(type_contains_inference_var),
        Type::Sum(sum) => sum.type_args.iter().any(type_contains_inference_var),
        Type::Opaque { params, .. } => params.iter().any(type_contains_inference_var),
        Type::App(head, args) => {
            type_contains_inference_var(head) || args.iter().any(type_contains_inference_var)
        }
        Type::Function(ft) => {
            ft.params.iter().any(type_contains_inference_var)
                || type_contains_inference_var(&ft.ret)
                || ft.effects.row.fields.iter().any(|(_, ty)| type_contains_inference_var(ty))
                || ft.effects.row.rest.is_some()
        }
        Type::FixedSizeList { element, .. } | Type::Tensor { element, .. } => {
            type_contains_inference_var(element)
        }
        Type::AnonRecord(row) | Type::Row(row) => {
            row.fields
                .iter()
                .any(|(_, field_ty)| type_contains_inference_var(field_ty))
                || row.rest.is_some()
        }
        Type::Forall(scheme) => type_contains_inference_var(&scheme.ty),
        Type::Existential {
            associated_types, ..
        } => associated_types.values().any(type_contains_inference_var),
        Type::Constructor { fixed_args, .. } => {
            fixed_args.iter().any(|(_, ty)| type_contains_inference_var(ty))
        }
        Type::Int
        | Type::IntN(_, _)
        | Type::Float
        | Type::FloatN(_)
        | Type::Bool
        | Type::Char
        | Type::String
        | Type::Html
        | Type::Markdown
        | Type::Unit
        | Type::Never
        | Type::Atom
        | Type::Date
        | Type::DateTime => false,
        Type::Dynamic => true,
    }
}

fn is_heap_managed_type(ty: &Type, layouts: &MirLayoutCatalog) -> bool {
    match ty {
        Type::String
        | Type::AnonRecord(_)
        | Type::Tuple(_)
        | Type::Function(_)
        | Type::Opaque { .. } => true,
        Type::Record(record) => !layouts
            .records
            .iter()
            .find(|layout| layout.name == record.name)
            .is_some_and(|layout| layout.is_unboxed),
        // Conservative: any named sum type is heap-managed. Even if only some
        // variants have fields (e.g. List has Nil + Cons), the allocation
        // carries a reference count and releasing it may free inner nodes.
        // When the sum type's `variants` field is empty (a partially-resolved
        // generic reference like `List a` with type args but no variant info),
        // we treat it as heap-managed rather than risk a use-after-free on the
        // extracted payload.
        Type::Sum(sum_ty) => !sum_ty.name.is_empty(),
        _ => false,
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use kea_ast::{
        Argument, DeclKind, EffectDecl, EffectOperation, ExprKind, Lit, RecordDef, Span,
        Spanned, TypeAnnotation, TypeDef,
        TypeVariant, VariantField,
    };
    use kea_hir::{HirExpr, HirExprKind, HirFunction, HirParam};
    use kea_types::{FunctionType, Label, RecordType, RowType, RowVarId, SumType};

    fn sp<T>(node: T) -> Spanned<T> {
        Spanned::new(node, kea_ast::Span::synthetic())
    }

    #[test]
    fn memory_op_classifier_matches_contract() {
        let retain = MirInst::Retain {
            value: MirValueId(1),
        };
        let effect = MirInst::EffectOp {
            class: MirEffectOpClass::Direct,
            effect: "IO".to_string(),
            operation: "stdout".to_string(),
            args: vec![],
            result: None,
        };

        assert!(retain.is_memory_op());
        assert!(!effect.is_memory_op());
    }

    #[test]
    fn lower_hir_module_collects_record_layout_field_order() {
        let hir = HirModule {
            declarations: vec![HirDecl::Raw(DeclKind::RecordDef(RecordDef {
                public: true,
                name: sp("User".to_string()),
                doc: None,
                annotations: vec![],
                params: vec![],
                fields: vec![
                    (
                        sp("name".to_string()),
                        TypeAnnotation::Named("String".to_string()),
                    ),
                    (
                        sp("age".to_string()),
                        TypeAnnotation::Named("Int".to_string()),
                    ),
                ],
                const_fields: vec![],
                field_annotations: vec![],
            methods: vec![],
            }))],
        };

        let mir = lower_hir_module(&hir);
        assert!(mir.functions.is_empty());
        assert_eq!(mir.layouts.records.len(), 1);
        assert_eq!(mir.layouts.records[0].name, "User");
        assert_eq!(mir.layouts.records[0].fields.len(), 2);
        assert_eq!(mir.layouts.records[0].fields[0].name, "name");
        assert_eq!(
            mir.layouts.records[0].fields[0].annotation,
            TypeAnnotation::Named("String".to_string())
        );
        assert_eq!(mir.layouts.records[0].fields[1].name, "age");
        assert_eq!(
            mir.layouts.records[0].fields[1].annotation,
            TypeAnnotation::Named("Int".to_string())
        );
    }

    #[test]
    fn lower_hir_module_collects_sum_layout_tags_in_declaration_order() {
        let hir = HirModule {
            declarations: vec![HirDecl::Raw(DeclKind::TypeDef(TypeDef {
                public: true,
                name: sp("Option".to_string()),
                doc: None,
                annotations: vec![],
                params: vec!["a".to_string()],
                variants: vec![
                    TypeVariant {
                        annotations: vec![],
                        name: sp("Some".to_string()),
                        fields: vec![VariantField {
                            annotations: vec![],
                            name: None,
                            ty: sp(TypeAnnotation::Named("a".to_string())),
                            span: kea_ast::Span::synthetic(),
                        }],
                        where_clause: vec![],
                    },
                    TypeVariant {
                        annotations: vec![],
                        name: sp("None".to_string()),
                        fields: vec![],
                        where_clause: vec![],
                    },
                ],
            methods: vec![],
            }))],
        };

        let mir = lower_hir_module(&hir);
        assert!(mir.functions.is_empty());
        let option = mir
            .layouts
            .sums
            .iter()
            .find(|sum| sum.name == "Option")
            .expect("expected Option layout");
        assert_eq!(option.name, "Option");
        assert_eq!(option.variants.len(), 2);
        assert_eq!(option.variants[0].name, "Some");
        assert_eq!(option.variants[0].tag, 0);
        assert_eq!(option.variants[0].fields.len(), 1);
        assert_eq!(
            option.variants[0].fields[0].annotation,
            TypeAnnotation::Named("a".to_string())
        );
        assert_eq!(option.variants[1].name, "None");
        assert_eq!(option.variants[1].tag, 1);
        assert_eq!(option.variants[1].fields.len(), 0);
    }

    #[test]
    fn lower_hir_module_seeds_builtin_option_and_result_layouts() {
        let mir = lower_hir_module(&HirModule {
            declarations: vec![],
        });

        let option = mir
            .layouts
            .sums
            .iter()
            .find(|sum| sum.name == "Option")
            .expect("expected built-in Option layout");
        // Tag order matches option.kea source: None=tag0 (first), Some=tag1 (second).
        assert_eq!(option.variants.len(), 2);
        assert_eq!(option.variants[0].name, "None");
        assert_eq!(option.variants[0].tag, 0);
        assert_eq!(option.variants[1].name, "Some");
        assert_eq!(option.variants[1].tag, 1);

        let result = mir
            .layouts
            .sums
            .iter()
            .find(|sum| sum.name == "Result")
            .expect("expected built-in Result layout");
        assert_eq!(result.variants.len(), 2);
        assert_eq!(result.variants[0].name, "Ok");
        assert_eq!(result.variants[0].tag, 0);
        assert_eq!(result.variants[1].name, "Err");
        assert_eq!(result.variants[1].tag, 1);
    }

    #[test]
    fn lower_hir_module_preserves_function_effect_row() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "write".to_string(),
                params: vec![HirParam {
                    name: Some("msg".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::Var("msg".to_string()),
                    ty: Type::String,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(kea_types::FunctionType::with_effects(
                    vec![Type::String],
                    Type::Unit,
                    EffectRow::closed(vec![(kea_types::Label::new("IO"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(kea_types::Label::new("IO"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        assert_eq!(mir.functions.len(), 1);
        assert_eq!(mir.functions[0].signature.effects.to_string(), "[IO]");
    }

    #[test]
    fn lower_hir_module_lowers_var_return_to_param_value() {
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
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        assert_eq!(mir.functions.len(), 1);
        let function = &mir.functions[0];
        assert_eq!(function.signature.params, vec![Type::Int]);
        assert!(matches!(
            function.blocks[0].terminator,
            MirTerminator::Return {
                value: Some(MirValueId(0))
            }
        ));
    }

    #[test]
    fn lower_hir_module_lowers_binary_expression() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "sum".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::Add,
                        left: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }),
                        right: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(2)),
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
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks[0].instructions.len(), 3);
        assert!(matches!(
            function.blocks[0].instructions[2],
            MirInst::Binary {
                op: MirBinaryOp::Add,
                ..
            }
        ));
    }

    #[test]
    fn lower_hir_module_lowers_bitwise_method_call_to_mir_binary_op() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "masked".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("bit_and".to_string()),
                            ty: Type::Function(FunctionType::pure(
                                vec![Type::Int, Type::Int],
                                Type::Int,
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![
                            HirExpr {
                                kind: HirExprKind::Lit(kea_ast::Lit::Int(42)),
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            },
                            HirExpr {
                                kind: HirExprKind::Lit(kea_ast::Lit::Int(15)),
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            },
                        ],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks[0].instructions.len(), 3);
        assert!(matches!(
            function.blocks[0].instructions[2],
            MirInst::Binary {
                op: MirBinaryOp::BitAnd,
                ..
            }
        ));
    }

    #[test]
    fn lower_hir_module_rewrites_sum_pointer_eq_to_tag_compare() {
        let sum_ty = Type::Sum(SumType {
            name: "Option".to_string(),
            type_args: vec![Type::Int],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "is_some_tag".to_string(),
                params: vec![HirParam {
                    name: Some("x".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::Eq,
                        left: Box::new(HirExpr {
                            kind: HirExprKind::Var("x".to_string()),
                            ty: sum_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        }),
                        right: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(0)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }),
                    },
                    ty: Type::Bool,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![sum_ty], Type::Bool)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };
        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::SumTagLoad { .. }))
        );
    }

    #[test]
    fn lower_hir_module_rewrites_sum_payload_eq_to_tag_compare() {
        let maybe_int_ty = Type::Sum(SumType {
            name: "Maybe".to_string(),
            type_args: vec![Type::Int],
        });
        let maybe_maybe_ty = Type::Sum(SumType {
            name: "Maybe".to_string(),
            type_args: vec![maybe_int_ty.clone()],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "is_nested_just".to_string(),
                params: vec![HirParam {
                    name: Some("x".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::Eq,
                        left: Box::new(HirExpr {
                            kind: HirExprKind::SumPayloadAccess {
                                expr: Box::new(HirExpr {
                                    kind: HirExprKind::Var("x".to_string()),
                                    ty: maybe_maybe_ty.clone(),
                                    span: kea_ast::Span::synthetic(),
                                }),
                                sum_type: "Maybe".to_string(),
                                variant: "Just".to_string(),
                                field_index: 0,
                            },
                            ty: maybe_int_ty,
                            span: kea_ast::Span::synthetic(),
                        }),
                        right: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(0)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }),
                    },
                    ty: Type::Bool,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![maybe_maybe_ty], Type::Bool)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::SumTagLoad { .. })),
            "expected nested sum payload tag comparison to lower via SumTagLoad"
        );
    }

    #[test]
    fn lower_hir_module_lowers_unary_expression() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "negate".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Unary {
                        op: kea_ast::UnaryOp::Neg,
                        operand: Box::new(HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
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
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::Unary {
                op: MirUnaryOp::Neg,
                ..
            }
        ));
    }

    #[test]
    fn lower_hir_module_lowers_bit_not_method_call_to_mir_unary_op() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "flipped".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("bit_not".to_string()),
                            ty: Type::Function(FunctionType::pure(vec![Type::Int], Type::Int)),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(255)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::Unary {
                op: MirUnaryOp::BitNot,
                ..
            }
        ));
    }

    #[test]
    fn lower_hir_module_lowers_popcount_method_call_to_mir_unary_op() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "ones".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("popcount".to_string()),
                            ty: Type::Function(FunctionType::pure(vec![Type::Int], Type::Int)),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(11)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::Unary {
                op: MirUnaryOp::Popcount,
                ..
            }
        ));
    }

    #[test]
    fn lower_hir_module_lowers_fixed_width_try_from_to_checked_option_path() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "narrow".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("Int8.try_from".to_string()),
                            ty: Type::Function(FunctionType::pure(
                                vec![Type::Int],
                                Type::option(Type::IntN(
                                    kea_types::IntWidth::I8,
                                    kea_types::Signedness::Signed,
                                )),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(42)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::option(Type::IntN(
                        kea_types::IntWidth::I8,
                        kea_types::Signedness::Signed,
                    )),
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(
                    vec![],
                    Type::option(Type::IntN(
                        kea_types::IntWidth::I8,
                        kea_types::Signedness::Signed,
                    )),
                )),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .any(|inst| matches!(
                    inst,
                    MirInst::Binary {
                        op: MirBinaryOp::Lt,
                        ..
                    }
                )),
            "expected lower bound check in try_from lowering"
        );
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .any(|inst| matches!(
                    inst,
                    MirInst::Binary {
                        op: MirBinaryOp::Gt,
                        ..
                    }
                )),
            "expected upper bound check in try_from lowering"
        );
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .any(|inst| matches!(
                    inst,
                    MirInst::SumInit {
                        sum_type,
                        variant,
                        tag,
                        ..
                    } if sum_type == "Option" && variant == "Some" && *tag == 1
                )),
            "expected Some construction in try_from lowering"
        );
    }

    #[test]
    fn lower_hir_module_widens_signed_fixed_width_input_before_try_from_checks() {
        let option_int8 = Type::option(Type::IntN(
            kea_types::IntWidth::I8,
            kea_types::Signedness::Signed,
        ));
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "narrow_param".to_string(),
                params: vec![HirParam {
                    name: Some("x".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("Int8.try_from".to_string()),
                            ty: Type::Function(FunctionType::pure(
                                vec![Type::Dynamic],
                                option_int8.clone(),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Var("x".to_string()),
                            ty: Type::IntN(kea_types::IntWidth::I8, kea_types::Signedness::Signed),
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: option_int8.clone(),
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(
                    vec![Type::IntN(
                        kea_types::IntWidth::I8,
                        kea_types::Signedness::Signed,
                    )],
                    option_int8,
                )),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .any(|inst| matches!(
                    inst,
                    MirInst::Unary {
                        op: MirUnaryOp::WidenSignedToInt,
                        ..
                    }
                )),
            "expected signed widening before try_from range checks"
        );
    }

    #[test]
    fn lower_hir_module_lowers_record_field_access_expression() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });

        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "get_age".to_string(),
                params: vec![HirParam {
                    name: Some("user".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::FieldAccess {
                        expr: Box::new(HirExpr {
                            kind: HirExprKind::Var("user".to_string()),
                            ty: user_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        }),
                        field: "age".to_string(),
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![user_ty], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        // RecordFieldLoad followed by Release for the record parameter (Perceus ownership).
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::RecordFieldLoad {
                record: MirValueId(0),
                ref record_type,
                ref field,
                field_ty: Type::Int,
                ..
            } if record_type == "User" && field == "age"
        ));
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::Release { value: MirValueId(0) }
        ));
    }

    // --- Ownership / release insertion adversarial tests ---

    /// `get_age_fip(user: User) -> Int` with `@fip` — no Release should be inserted.
    #[test]
    fn fip_function_does_not_get_release_for_record_param() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "get_age_fip".to_string(),
                params: vec![HirParam {
                    name: Some("user".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::FieldAccess {
                        expr: Box::new(HirExpr {
                            kind: HirExprKind::Var("user".to_string()),
                            ty: user_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        }),
                        field: "age".to_string(),
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![user_ty], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: true, // @fip — must have zero Release instructions
            })],
        };
        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        let has_release = function.blocks.iter().flat_map(|b| b.instructions.iter()).any(
            |inst| matches!(inst, MirInst::Release { value: MirValueId(0) }),
        );
        assert!(!has_release, "@fip function must not have Release for its record param");
    }

    /// `get_age(user: User) -> Int` where User is an `@unboxed` record (all-primitive).
    /// No Release should be inserted for stack-allocated records.
    #[test]
    fn unboxed_record_param_does_not_get_release() {
        let user_ty = Type::Record(RecordType {
            name: "Point".to_string(),
            params: vec![],
        });
        // Register Point as an unboxed record layout.
        let hir = HirModule {
            declarations: vec![
                HirDecl::Raw(kea_ast::DeclKind::RecordDef(kea_ast::RecordDef {
                    public: true,
                    name: sp("Point".to_string()),
                    doc: None,
                    params: vec![],
                    fields: vec![
                        (sp("x".to_string()), kea_ast::TypeAnnotation::Named("Int".to_string())),
                        (sp("y".to_string()), kea_ast::TypeAnnotation::Named("Int".to_string())),
                    ],
                    annotations: vec![kea_ast::Annotation {
                        name: sp("unboxed".to_string()),
                        args: vec![],
                        span: kea_ast::Span::synthetic(),
                    }],
                    const_fields: vec![],
                    field_annotations: vec![],
                methods: vec![],
                })),
                HirDecl::Function(HirFunction {
                    name: "get_x".to_string(),
                    params: vec![HirParam {
                        name: Some("p".to_string()),
                        span: kea_ast::Span::synthetic(),
                    }],
                    body: HirExpr {
                        kind: HirExprKind::FieldAccess {
                            expr: Box::new(HirExpr {
                                kind: HirExprKind::Var("p".to_string()),
                                ty: user_ty.clone(),
                                span: kea_ast::Span::synthetic(),
                            }),
                            field: "x".to_string(),
                        },
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(vec![user_ty], Type::Int)),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
            ],
        };
        let mir = lower_hir_module(&hir);
        let function = mir.functions.iter().find(|f| f.name == "get_x").unwrap();
        let has_release = function.blocks.iter().flat_map(|b| b.instructions.iter()).any(
            |inst| matches!(inst, MirInst::Release { .. }),
        );
        assert!(!has_release, "@unboxed record param must not get a Release");
    }

    /// `sum_payload_with_managed_child` takes `Option (List Int)`.
    /// The SumPayloadLoad extracts a `Dynamic` child (managed).
    /// Case 2 must NOT insert a Release (would double-free the extracted child).
    #[test]
    fn sum_param_with_dynamic_payload_does_not_get_release() {
        let list_ty = Type::Sum(kea_types::SumType {
            name: "List".to_string(),
            type_args: vec![Type::Int],
        });
        let option_list_ty = Type::Sum(kea_types::SumType {
            name: "Option".to_string(),
            type_args: vec![list_ty.clone()],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "unwrap_list".to_string(),
                params: vec![HirParam {
                    name: Some("opt".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::SumPayloadAccess {
                        expr: Box::new(HirExpr {
                            kind: HirExprKind::Var("opt".to_string()),
                            ty: option_list_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        }),
                        sum_type: "Option".to_string(),
                        variant: "Some".to_string(),
                        field_index: 0,
                    },
                    ty: list_ty.clone(), // managed: Sum type
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![option_list_ty], list_ty)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };
        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        let has_release = function.blocks.iter().flat_map(|b| b.instructions.iter()).any(
            |inst| matches!(inst, MirInst::Release { value: MirValueId(0) }),
        );
        assert!(
            !has_release,
            "sum param with managed child payload must NOT get a Release \
             (would double-free extracted child)"
        );
    }

    // Table test: release insertion for record params across different function shapes.
    //
    // Each row: (description, last_instruction_is_release, instructions_count)
    // All functions: `f(user: User) -> ...` where User has a String field.

    /// Record param consumed by a direct return → no Release (caller owns returned value).
    #[test]
    fn record_param_returned_directly_has_no_release() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "identity".to_string(),
                params: vec![HirParam {
                    name: Some("user".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::Var("user".to_string()),
                    ty: user_ty.clone(),
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![user_ty.clone()], user_ty)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };
        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        let has_release = function.blocks.iter().flat_map(|b| b.instructions.iter()).any(
            |inst| matches!(inst, MirInst::Release { value: MirValueId(0) }),
        );
        assert!(!has_release, "param returned directly must not have Release (caller takes ownership)");
    }

    #[test]
    fn lower_hir_module_lowers_record_literal_expression() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });

        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "make_user".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::RecordLit {
                        record_type: "User".to_string(),
                        fields: vec![
                            (
                                "age".to_string(),
                                HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::Int(42)),
                                    ty: Type::Int,
                                    span: kea_ast::Span::synthetic(),
                                },
                            ),
                            (
                                "name".to_string(),
                                HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::String("a".to_string())),
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                },
                            ),
                        ],
                    },
                    ty: user_ty.clone(),
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], user_ty)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks[0].instructions.len(), 3);
        assert!(matches!(
            function.blocks[0].instructions[2],
            MirInst::RecordInit {
                ref record_type,
                ref fields,
                ..
            } if record_type == "User" && fields.len() == 2
        ));
    }

    #[test]
    fn lower_hir_module_seeds_synthetic_layout_for_raw_anon_record_literal() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Raw(ExprKind::AnonRecord {
                        fields: vec![
                            (
                                sp("age".to_string()),
                                sp(ExprKind::Lit(kea_ast::Lit::Int(4))),
                            ),
                            (
                                sp("score".to_string()),
                                sp(ExprKind::Lit(kea_ast::Lit::Int(9))),
                            ),
                        ],
                        spread: None,
                    }),
                    ty: Type::Dynamic,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Dynamic)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let layout = mir
            .layouts
            .records
            .iter()
            .find(|layout| layout.name == "__AnonRecord$age$score")
            .expect("expected synthetic anon-record layout");
        assert_eq!(layout.fields.len(), 2);
        assert_eq!(layout.fields[0].name, "age");
        assert_eq!(layout.fields[1].name, "score");
    }

    #[test]
    fn lower_hir_module_lowers_raw_anon_record_literal_field_access_expression() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "get_age".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("user".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Raw(ExprKind::AnonRecord {
                                        fields: vec![
                                            (
                                                sp("age".to_string()),
                                                sp(ExprKind::Lit(kea_ast::Lit::Int(4))),
                                            ),
                                            (
                                                sp("score".to_string()),
                                                sp(ExprKind::Lit(kea_ast::Lit::Int(9))),
                                            ),
                                        ],
                                        spread: None,
                                    }),
                                    ty: Type::Dynamic,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::Dynamic,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::FieldAccess {
                                expr: Box::new(HirExpr {
                                    kind: HirExprKind::Var("user".to_string()),
                                    ty: Type::Dynamic,
                                    span: kea_ast::Span::synthetic(),
                                }),
                                field: "age".to_string(),
                            },
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(function.blocks[0].instructions.iter().any(|inst| matches!(
            inst,
            MirInst::RecordInit {
                record_type,
                fields,
                ..
            } if record_type == "__AnonRecord$age$score" && fields.len() == 2
        )));
        assert!(function.blocks[0].instructions.iter().any(|inst| matches!(
            inst,
            MirInst::RecordFieldLoad {
                record_type,
                field,
                field_ty: Type::Int,
                ..
            } if record_type == "__AnonRecord$age$score" && field == "age"
        )));
    }

    #[test]
    fn lower_hir_module_lowers_record_update_with_memory_ops() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "bump_age".to_string(),
                params: vec![HirParam {
                    name: Some("user".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::RecordUpdate {
                        record_type: "User".to_string(),
                        base: Box::new(HirExpr {
                            kind: HirExprKind::Var("user".to_string()),
                            ty: user_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        }),
                        fields: vec![(
                            "age".to_string(),
                            HirExpr {
                                kind: HirExprKind::Lit(kea_ast::Lit::Int(10)),
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            },
                        )],
                    },
                    ty: user_ty.clone(),
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![user_ty.clone()], user_ty)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Retain { .. }))
        );
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::TryClaim { .. }))
        );
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Freeze { .. }))
        );
        assert!(function.blocks[0].instructions.iter().any(|inst| matches!(
            inst,
            MirInst::CowUpdate {
                record_type,
                updates,
                ..
            } if record_type == "User" && updates.len() == 1 && updates[0].field == "age"
        )));
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Release { .. }))
        );
    }

    #[test]
    fn lower_hir_module_fuses_nested_record_updates_into_single_cow_update() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });
        let base_var = HirExpr {
            kind: HirExprKind::Var("user".to_string()),
            ty: user_ty.clone(),
            span: kea_ast::Span::synthetic(),
        };
        let inner = HirExpr {
            kind: HirExprKind::RecordUpdate {
                record_type: "User".to_string(),
                base: Box::new(base_var.clone()),
                fields: vec![(
                    "age".to_string(),
                    HirExpr {
                        kind: HirExprKind::Lit(kea_ast::Lit::Int(5)),
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                )],
            },
            ty: user_ty.clone(),
            span: kea_ast::Span::synthetic(),
        };
        let outer = HirExpr {
            kind: HirExprKind::RecordUpdate {
                record_type: "User".to_string(),
                base: Box::new(inner),
                fields: vec![(
                    "score".to_string(),
                    HirExpr {
                        kind: HirExprKind::Lit(kea_ast::Lit::Int(8)),
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                )],
            },
            ty: user_ty.clone(),
            span: kea_ast::Span::synthetic(),
        };
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "fuse_updates".to_string(),
                params: vec![HirParam {
                    name: Some("user".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: outer,
                ty: Type::Function(FunctionType::pure(vec![user_ty.clone()], user_ty)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        let cow_updates = function.blocks[0]
            .instructions
            .iter()
            .filter(|inst| matches!(inst, MirInst::CowUpdate { .. }))
            .collect::<Vec<_>>();
        assert_eq!(
            cow_updates.len(),
            1,
            "nested updates should fuse into one CowUpdate"
        );
        assert!(matches!(
            cow_updates[0],
            MirInst::CowUpdate { updates, .. }
                if updates.len() == 2
                    && updates.iter().any(|u| u.field == "age")
                    && updates.iter().any(|u| u.field == "score")
        ));
    }

    #[test]
    fn lower_hir_module_transfers_linear_local_record_update_base_without_retain() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("user".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::RecordLit {
                                        record_type: "User".to_string(),
                                        fields: vec![(
                                            "age".to_string(),
                                            HirExpr {
                                                kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                                                ty: Type::Int,
                                                span: kea_ast::Span::synthetic(),
                                            },
                                        )],
                                    },
                                    ty: user_ty.clone(),
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: user_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("updated".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::RecordUpdate {
                                        record_type: "User".to_string(),
                                        base: Box::new(HirExpr {
                                            kind: HirExprKind::Var("user".to_string()),
                                            ty: user_ty.clone(),
                                            span: kea_ast::Span::synthetic(),
                                        }),
                                        fields: vec![(
                                            "age".to_string(),
                                            HirExpr {
                                                kind: HirExprKind::Lit(kea_ast::Lit::Int(2)),
                                                ty: Type::Int,
                                                span: kea_ast::Span::synthetic(),
                                            },
                                        )],
                                    },
                                    ty: user_ty.clone(),
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: user_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(0)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let instructions = &mir.functions[0].blocks[0].instructions;
        assert!(
            instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::CowUpdate { .. })),
            "expected record update lowering to emit CowUpdate"
        );
        assert!(
            !instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Retain { .. })),
            "linear local record-update base should transfer ownership without retain: {instructions:?}"
        );
    }

    #[test]
    fn lower_hir_module_keeps_retain_when_record_update_fields_read_base_binding() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("user".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::RecordLit {
                                        record_type: "User".to_string(),
                                        fields: vec![(
                                            "age".to_string(),
                                            HirExpr {
                                                kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                                                ty: Type::Int,
                                                span: kea_ast::Span::synthetic(),
                                            },
                                        )],
                                    },
                                    ty: user_ty.clone(),
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: user_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("updated".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::RecordUpdate {
                                        record_type: "User".to_string(),
                                        base: Box::new(HirExpr {
                                            kind: HirExprKind::Var("user".to_string()),
                                            ty: user_ty.clone(),
                                            span: kea_ast::Span::synthetic(),
                                        }),
                                        fields: vec![(
                                            "age".to_string(),
                                            HirExpr {
                                                kind: HirExprKind::Binary {
                                                    op: BinOp::Add,
                                                    left: Box::new(HirExpr {
                                                        kind: HirExprKind::FieldAccess {
                                                            expr: Box::new(HirExpr {
                                                                kind: HirExprKind::Var(
                                                                    "user".to_string(),
                                                                ),
                                                                ty: user_ty.clone(),
                                                                span: kea_ast::Span::synthetic(),
                                                            }),
                                                            field: "age".to_string(),
                                                        },
                                                        ty: Type::Int,
                                                        span: kea_ast::Span::synthetic(),
                                                    }),
                                                    right: Box::new(HirExpr {
                                                        kind: HirExprKind::Lit(kea_ast::Lit::Int(
                                                            1,
                                                        )),
                                                        ty: Type::Int,
                                                        span: kea_ast::Span::synthetic(),
                                                    }),
                                                },
                                                ty: Type::Int,
                                                span: kea_ast::Span::synthetic(),
                                            },
                                        )],
                                    },
                                    ty: user_ty.clone(),
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: user_ty,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(0)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let instructions = &mir.functions[0].blocks[0].instructions;
        assert!(
            instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Retain { .. })),
            "record-update fields that read the base binding must keep retain for safety: {instructions:?}"
        );
    }

    #[test]
    fn lower_hir_module_lowers_payload_constructor_from_raw_hir() {
        let sum_decl = HirDecl::Raw(DeclKind::TypeDef(TypeDef {
            public: false,
            name: sp("Option".to_string()),
            doc: None,
            annotations: vec![],
            params: vec![],
            variants: vec![
                TypeVariant {
                    annotations: vec![],
                    name: sp("Some".to_string()),
                    fields: vec![VariantField {
                        annotations: vec![],
                        name: None,
                        ty: sp(TypeAnnotation::Named("Int".to_string())),
                        span: kea_ast::Span::synthetic(),
                    }],
                    where_clause: vec![],
                },
                TypeVariant {
                    annotations: vec![],
                    name: sp("None".to_string()),
                    fields: vec![],
                    where_clause: vec![],
                },
            ],
        methods: vec![],
        }));
        let option_ty = Type::Sum(kea_types::SumType {
            name: "Option".to_string(),
            type_args: vec![Type::Int],
        });
        let function_decl = HirDecl::Function(HirFunction {
            name: "make_some".to_string(),
            params: vec![],
            body: HirExpr {
                kind: HirExprKind::Raw(ExprKind::Constructor {
                    name: sp("Some".to_string()),
                    args: vec![Argument {
                        label: None,
                        value: sp(ExprKind::Lit(kea_ast::Lit::Int(7))),
                    }],
                }),
                ty: option_ty.clone(),
                span: kea_ast::Span::synthetic(),
            },
            ty: Type::Function(FunctionType::pure(vec![], option_ty)),
            effects: EffectRow::pure(),
            span: kea_ast::Span::synthetic(),
            is_fip: false,
        });

        let mir = lower_hir_module(&HirModule {
            declarations: vec![sum_decl, function_decl],
        });
        let function = &mir.functions[0];
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::SumInit {
                ref sum_type,
                ref variant,
                tag: 0,
                ref fields,
                ..
            } if sum_type == "Option" && variant == "Some" && fields.len() == 1
        ));
    }

    #[test]
    fn lower_hir_module_lowers_payload_constructor_with_expression_field() {
        let option_ty = Type::Sum(kea_types::SumType {
            name: "Option".to_string(),
            type_args: vec![Type::Int],
        });
        let function_decl = HirDecl::Function(HirFunction {
            name: "make_some".to_string(),
            params: vec![],
            body: HirExpr {
                kind: HirExprKind::SumConstructor {
                    sum_type: "Option".to_string(),
                    variant: "Some".to_string(),
                    tag: 0,
                    fields: vec![HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::Add,
                            left: Box::new(HirExpr {
                                kind: HirExprKind::Lit(kea_ast::Lit::Int(3)),
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            }),
                            right: Box::new(HirExpr {
                                kind: HirExprKind::Lit(kea_ast::Lit::Int(4)),
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            }),
                        },
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    }],
                },
                ty: option_ty.clone(),
                span: kea_ast::Span::synthetic(),
            },
            ty: Type::Function(FunctionType::pure(vec![], option_ty)),
            effects: EffectRow::pure(),
            span: kea_ast::Span::synthetic(),
            is_fip: false,
        });

        let mir = lower_hir_module(&HirModule {
            declarations: vec![function_decl],
        });
        let function = &mir.functions[0];
        assert!(function.blocks[0].instructions.iter().any(|inst| matches!(
            inst,
            MirInst::Binary {
                op: MirBinaryOp::Add,
                ..
            }
        )));
        assert!(function.blocks[0].instructions.iter().any(|inst| matches!(
            inst,
            MirInst::SumInit {
                sum_type,
                variant,
                tag: 0,
                fields,
                ..
            } if sum_type == "Option" && variant == "Some" && fields.len() == 1
        )));
    }

    #[test]
    fn lower_hir_module_lowers_sum_payload_access_expression() {
        let option_ty = Type::Sum(kea_types::SumType {
            name: "Option".to_string(),
            type_args: vec![Type::Int],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "unwrap_some".to_string(),
                params: vec![HirParam {
                    name: Some("opt".to_string()),
                    span: kea_ast::Span::synthetic(),
                }],
                body: HirExpr {
                    kind: HirExprKind::SumPayloadAccess {
                        expr: Box::new(HirExpr {
                            kind: HirExprKind::Var("opt".to_string()),
                            ty: option_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        }),
                        sum_type: "Option".to_string(),
                        variant: "Some".to_string(),
                        field_index: 0,
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![option_ty], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        // Expect SumPayloadLoad + Release for the managed `opt` param.
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::SumPayloadLoad {
                sum: MirValueId(0),
                ref sum_type,
                ref variant,
                field_index: 0,
                field_ty: Type::Int,
                ..
            } if sum_type == "Option" && variant == "Some"
        ));
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::Release { value: MirValueId(0) }
        ));
    }

    #[test]
    fn lower_hir_module_resolves_record_field_load_for_let_bound_record_var() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "get_age".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("user".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::RecordLit {
                                        record_type: "User".to_string(),
                                        fields: vec![(
                                            "age".to_string(),
                                            HirExpr {
                                                kind: HirExprKind::Lit(kea_ast::Lit::Int(9)),
                                                ty: Type::Int,
                                                span: kea_ast::Span::synthetic(),
                                            },
                                        )],
                                    },
                                    ty: user_ty.clone(),
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: user_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::FieldAccess {
                                expr: Box::new(HirExpr {
                                    kind: HirExprKind::Var("user".to_string()),
                                    ty: Type::Dynamic,
                                    span: kea_ast::Span::synthetic(),
                                }),
                                field: "age".to_string(),
                            },
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::RecordFieldLoad { .. }))
        );
    }

    #[test]
    fn lower_hir_module_resolves_record_field_load_for_anon_record_param() {
        let anon_row = RowType::open(vec![(Label::new("age"), Type::Int)], RowVarId(7));
        let hir = HirModule {
            declarations: vec![
                HirDecl::Raw(DeclKind::RecordDef(RecordDef {
                    public: true,
                    name: sp("User".to_string()),
                    doc: None,
                    annotations: vec![],
                    params: vec![],
                    fields: vec![
                        (
                            sp("age".to_string()),
                            TypeAnnotation::Named("Int".to_string()),
                        ),
                        (
                            sp("score".to_string()),
                            TypeAnnotation::Named("Int".to_string()),
                        ),
                    ],
                    const_fields: vec![],
                    field_annotations: vec![],
                methods: vec![],
                })),
                HirDecl::Function(HirFunction {
                    name: "get_age".to_string(),
                    params: vec![HirParam {
                        name: Some("u".to_string()),
                        span: kea_ast::Span::synthetic(),
                    }],
                    body: HirExpr {
                        kind: HirExprKind::FieldAccess {
                            expr: Box::new(HirExpr {
                                kind: HirExprKind::Var("u".to_string()),
                                ty: Type::AnonRecord(anon_row.clone()),
                                span: kea_ast::Span::synthetic(),
                            }),
                            field: "age".to_string(),
                        },
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(
                        vec![Type::AnonRecord(anon_row)],
                        Type::Int,
                    )),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
            ],
        };

        let mir = lower_hir_module(&hir);
        let function = mir
            .functions
            .iter()
            .find(|f| f.name == "get_age")
            .expect("get_age function");
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::RecordFieldLoad {
                ref record_type,
                ref field,
                field_ty: Type::Int,
                ..
            } if record_type == "User" && field == "age"
        ));
    }

    #[test]
    fn lower_hir_module_lowers_unit_if_into_branch_blocks() {
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
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 4);
        assert!(matches!(
            function.blocks[0].terminator,
            MirTerminator::Branch { .. }
        ));
        assert!(matches!(
            function.blocks[1].terminator,
            MirTerminator::Jump { .. }
        ));
        assert!(matches!(
            function.blocks[2].terminator,
            MirTerminator::Jump { .. }
        ));
        assert!(matches!(
            function.blocks[3].terminator,
            MirTerminator::Return { value: None }
        ));
    }

    #[test]
    fn lower_hir_module_lowers_value_if_with_join_param() {
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
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 4);
        assert_eq!(function.blocks[3].params.len(), 1);
        assert_eq!(function.blocks[3].params[0].ty, Type::Int);
        let join_value = function.blocks[3].params[0].id.clone();

        let MirTerminator::Jump {
            args: then_args, ..
        } = &function.blocks[1].terminator
        else {
            panic!("then block should jump to join");
        };
        let MirTerminator::Jump {
            args: else_args, ..
        } = &function.blocks[2].terminator
        else {
            panic!("else block should jump to join");
        };
        assert_eq!(then_args.len(), 1);
        assert_eq!(else_args.len(), 1);

        assert!(matches!(
            function.blocks[3].terminator,
            MirTerminator::Return {
                value: Some(ref value)
            } if value == &join_value
        ));
    }

    #[test]
    fn lower_hir_module_lowers_short_circuit_and_control_flow() {
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
                        op: BinOp::And,
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
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 4);
        assert!(matches!(
            function.blocks[0].terminator,
            MirTerminator::Branch { .. }
        ));

        let MirTerminator::Jump { args: rhs_args, .. } = &function.blocks[1].terminator else {
            panic!("rhs branch should jump to join");
        };
        assert_eq!(rhs_args.len(), 1);
        assert_eq!(rhs_args[0], MirValueId(1));

        assert!(matches!(
            function.blocks[2].instructions.first(),
            Some(MirInst::Const {
                literal: MirLiteral::Bool(false),
                ..
            })
        ));
        assert_eq!(function.blocks[3].params.len(), 1);
        assert!(matches!(
            function.blocks[3].terminator,
            MirTerminator::Return { value: Some(_) }
        ));
    }

    #[test]
    fn lower_hir_module_lowers_short_circuit_or_control_flow() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "either".to_string(),
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
                        op: BinOp::Or,
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
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 4);
        assert!(matches!(
            function.blocks[0].terminator,
            MirTerminator::Branch { .. }
        ));
        assert!(matches!(
            function.blocks[2].instructions.first(),
            Some(MirInst::Const {
                literal: MirLiteral::Bool(true),
                ..
            })
        ));

        let MirTerminator::Jump { args: rhs_args, .. } = &function.blocks[1].terminator else {
            panic!("rhs branch should jump to join");
        };
        assert_eq!(rhs_args.len(), 1);
        assert_eq!(rhs_args[0], MirValueId(1));
    }

    #[test]
    fn lower_hir_module_lowers_fail_qualified_call_to_zero_resume_effect_op() {
        let fail_decl = HirDecl::Raw(DeclKind::EffectDecl(EffectDecl {
            public: false,
            name: Spanned { node: "Fail".to_string(), span: Span::synthetic() },
            doc: None,
            type_params: vec!["E".to_string()],
            operations: vec![EffectOperation {
                name: Spanned { node: "fail".to_string(), span: Span::synthetic() },
                params: vec![],
                return_annotation: Spanned {
                    node: TypeAnnotation::Named("Never".to_string()),
                    span: Span::synthetic(),
                },
                doc: None,
                span: Span::synthetic(),
            }],
        }));
        let hir = HirModule {
            declarations: vec![fail_decl, HirDecl::Function(HirFunction {
                name: "boom".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("Fail.fail".to_string()),
                            ty: Type::Dynamic,
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(7)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Unit,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Unit,
                    EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::Const {
                literal: MirLiteral::Int(7),
                ..
            }
        ));
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::EffectOp {
                class: MirEffectOpClass::ZeroResume,
                ref effect,
                ref operation,
                result: None,
                ..
            } if effect == "Fail" && operation == "fail"
        ));
        assert!(matches!(
            function.blocks[0].terminator,
            MirTerminator::Unreachable
        ));
    }

    #[test]
    fn lower_hir_module_lowers_io_stdout_call_to_direct_effect_op() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "hello".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("IO.stdout".to_string()),
                            ty: Type::Function(FunctionType::with_effects(
                                vec![Type::String],
                                Type::Unit,
                                EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::String("hello".to_string())),
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Unit,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Unit,
                    EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::Const {
                literal: MirLiteral::String(ref s),
                ..
            } if s == "hello"
        ));
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                result: None,
                ..
            } if effect == "IO" && operation == "stdout"
        ));
    }

    #[test]
    fn lower_hir_module_lowers_io_stderr_call_to_direct_effect_op() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "hello_err".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("IO.stderr".to_string()),
                            ty: Type::Function(FunctionType::with_effects(
                                vec![Type::String],
                                Type::Unit,
                                EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::String("oops".to_string())),
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Unit,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Unit,
                    EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::Const {
                literal: MirLiteral::String(ref s),
                ..
            } if s == "oops"
        ));
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                result: None,
                ..
            } if effect == "IO" && operation == "stderr"
        ));
    }

    #[test]
    fn lower_hir_module_lowers_clock_now_call_to_direct_effect_op_with_result() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "now_tick".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("Clock.now".to_string()),
                            ty: Type::Function(FunctionType::with_effects(
                                vec![],
                                Type::Int,
                                EffectRow::closed(vec![(Label::new("Clock"), Type::Unit)]),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Int,
                    EffectRow::closed(vec![(Label::new("Clock"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Clock"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 1);
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                args: ref lowered_args,
                result: Some(_),
                ..
            } if effect == "Clock" && operation == "now" && lowered_args.is_empty()
        ));
    }

    #[test]
    fn lower_hir_module_lowers_io_read_file_call_to_direct_effect_op_with_result() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "read_config".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("IO.read_file".to_string()),
                            ty: Type::Function(FunctionType::with_effects(
                                vec![Type::String],
                                Type::String,
                                EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(Lit::String("config".to_string())),
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::String,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::String,
                    EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                args: ref lowered_args,
                result: Some(_),
                ..
            } if effect == "IO" && operation == "read_file" && lowered_args.len() == 1
        ));
    }

    #[test]
    fn lower_hir_module_lowers_io_write_file_call_to_direct_effect_op() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "write_config".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("IO.write_file".to_string()),
                            ty: Type::Function(FunctionType::with_effects(
                                vec![Type::String, Type::String],
                                Type::Unit,
                                EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![
                            HirExpr {
                                kind: HirExprKind::Lit(Lit::String("config".to_string())),
                                ty: Type::String,
                                span: kea_ast::Span::synthetic(),
                            },
                            HirExpr {
                                kind: HirExprKind::Lit(Lit::String("hello".to_string())),
                                ty: Type::String,
                                span: kea_ast::Span::synthetic(),
                            },
                        ],
                    },
                    ty: Type::Unit,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Unit,
                    EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("IO"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 3);
        assert!(matches!(
            function.blocks[0].instructions[2],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                args: ref lowered_args,
                result: None,
                ..
            } if effect == "IO" && operation == "write_file" && lowered_args.len() == 2
        ));
    }

    #[test]
    fn lower_hir_module_lowers_clock_monotonic_call_to_direct_effect_op_with_result() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "monotonic_tick".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("Clock.monotonic".to_string()),
                            ty: Type::Function(FunctionType::with_effects(
                                vec![],
                                Type::Int,
                                EffectRow::closed(vec![(Label::new("Clock"), Type::Unit)]),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Int,
                    EffectRow::closed(vec![(Label::new("Clock"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Clock"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 1);
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                args: ref lowered_args,
                result: Some(_),
                ..
            } if effect == "Clock" && operation == "monotonic" && lowered_args.is_empty()
        ));
    }

    #[test]
    fn lower_hir_module_lowers_rand_int_call_to_direct_effect_op_with_result() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "rand_tick".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("Rand.int".to_string()),
                            ty: Type::Function(FunctionType::with_effects(
                                vec![],
                                Type::Int,
                                EffectRow::closed(vec![(Label::new("Rand"), Type::Unit)]),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Int,
                    EffectRow::closed(vec![(Label::new("Rand"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Rand"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 1);
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                args: ref lowered_args,
                result: Some(_),
                ..
            } if effect == "Rand" && operation == "int" && lowered_args.is_empty()
        ));
    }

    #[test]
    fn lower_hir_module_lowers_rand_seed_call_to_direct_effect_op() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "seed_rng".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("Rand.seed".to_string()),
                            ty: Type::Function(FunctionType::with_effects(
                                vec![Type::Int],
                                Type::Unit,
                                EffectRow::closed(vec![(Label::new("Rand"), Type::Unit)]),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(Lit::Int(123)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Unit,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Unit,
                    EffectRow::closed(vec![(Label::new("Rand"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Rand"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[0],
            MirInst::Const {
                literal: MirLiteral::Int(123),
                ..
            }
        ));
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                args: ref lowered_args,
                result: None,
                ..
            } if effect == "Rand" && operation == "seed" && lowered_args.len() == 1
        ));
    }

    #[test]
    fn lower_hir_module_lowers_net_connect_call_to_direct_effect_op_with_result() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "open_conn".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("Net.connect".to_string()),
                            ty: Type::Function(FunctionType::with_effects(
                                vec![Type::String],
                                Type::Int,
                                EffectRow::closed(vec![(Label::new("Net"), Type::Unit)]),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(Lit::String("127.0.0.1:0".to_string())),
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Int,
                    EffectRow::closed(vec![(Label::new("Net"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Net"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 2);
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                args: ref lowered_args,
                result: Some(_),
                ..
            } if effect == "Net" && operation == "connect" && lowered_args.len() == 1
        ));
    }

    #[test]
    fn lower_hir_module_lowers_net_send_and_recv_calls_to_direct_effect_ops() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "exchange".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Call {
                                func: Box::new(HirExpr {
                                    kind: HirExprKind::Var("Net.send".to_string()),
                                    ty: Type::Function(FunctionType::with_effects(
                                        vec![Type::Int, Type::String],
                                        Type::Unit,
                                        EffectRow::closed(vec![(Label::new("Net"), Type::Unit)]),
                                    )),
                                    span: kea_ast::Span::synthetic(),
                                }),
                                args: vec![
                                    HirExpr {
                                        kind: HirExprKind::Lit(Lit::Int(1)),
                                        ty: Type::Int,
                                        span: kea_ast::Span::synthetic(),
                                    },
                                    HirExpr {
                                        kind: HirExprKind::Lit(Lit::String("ping".to_string())),
                                        ty: Type::String,
                                        span: kea_ast::Span::synthetic(),
                                    },
                                ],
                            },
                            ty: Type::Unit,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Call {
                                func: Box::new(HirExpr {
                                    kind: HirExprKind::Var("Net.recv".to_string()),
                                    ty: Type::Function(FunctionType::with_effects(
                                        vec![Type::Int, Type::Int],
                                        Type::Int,
                                        EffectRow::closed(vec![(Label::new("Net"), Type::Unit)]),
                                    )),
                                    span: kea_ast::Span::synthetic(),
                                }),
                                args: vec![
                                    HirExpr {
                                        kind: HirExprKind::Lit(Lit::Int(1)),
                                        ty: Type::Int,
                                        span: kea_ast::Span::synthetic(),
                                    },
                                    HirExpr {
                                        kind: HirExprKind::Lit(Lit::Int(4)),
                                        ty: Type::Int,
                                        span: kea_ast::Span::synthetic(),
                                    },
                                ],
                            },
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![],
                    Type::Int,
                    EffectRow::closed(vec![(Label::new("Net"), Type::Unit)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Net"), Type::Unit)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 6);
        assert!(matches!(
            function.blocks[0].instructions[2],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                args: ref lowered_args,
                result: None,
                ..
            } if effect == "Net" && operation == "send" && lowered_args.len() == 2
        ));
        assert!(matches!(
            function.blocks[0].instructions[5],
            MirInst::EffectOp {
                class: MirEffectOpClass::Direct,
                ref effect,
                ref operation,
                args: ref lowered_args,
                result: Some(_),
                ..
            } if effect == "Net" && operation == "recv" && lowered_args.len() == 2
        ));
    }

    #[test]
    fn lower_hir_module_lowers_param_callee_to_indirect_call() {
        let fn_ty = Type::Function(FunctionType::pure(vec![Type::Int], Type::Int));
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "apply".to_string(),
                params: vec![
                    kea_hir::HirParam {
                        name: Some("f".to_string()),
                        span: kea_ast::Span::synthetic(),
                    },
                    kea_hir::HirParam {
                        name: Some("x".to_string()),
                        span: kea_ast::Span::synthetic(),
                    },
                ],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("f".to_string()),
                            ty: fn_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Var("x".to_string()),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(
                    vec![fn_ty.clone(), Type::Int],
                    Type::Int,
                )),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].instructions.len(), 1);
        assert!(matches!(
            &function.blocks[0].instructions[0],
            MirInst::Call {
                callee: MirCallee::Value(MirValueId(0)),
                args,
                result: Some(MirValueId(2)),
                ret_type: Type::Int,
                callee_fail_result_abi: false,
                ..
            } if args == &vec![MirValueId(1)]
        ));
    }

    #[test]
    fn lower_hir_module_inlines_let_bound_lambda_call() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("f".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Lambda {
                                        params: vec![kea_hir::HirParam {
                                            name: Some("x".to_string()),
                                            span: kea_ast::Span::synthetic(),
                                        }],
                                        body: Box::new(HirExpr {
                                            kind: HirExprKind::Binary {
                                                op: BinOp::Add,
                                                left: Box::new(HirExpr {
                                                    kind: HirExprKind::Var("x".to_string()),
                                                    ty: Type::Int,
                                                    span: kea_ast::Span::synthetic(),
                                                }),
                                                right: Box::new(HirExpr {
                                                    kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                                                    ty: Type::Int,
                                                    span: kea_ast::Span::synthetic(),
                                                }),
                                            },
                                            ty: Type::Int,
                                            span: kea_ast::Span::synthetic(),
                                        }),
                                    },
                                    ty: Type::Function(FunctionType::pure(
                                        vec![Type::Int],
                                        Type::Int,
                                    )),
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::Function(FunctionType::pure(vec![Type::Int], Type::Int)),
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Call {
                                func: Box::new(HirExpr {
                                    kind: HirExprKind::Var("f".to_string()),
                                    ty: Type::Function(FunctionType::pure(
                                        vec![Type::Int],
                                        Type::Int,
                                    )),
                                    span: kea_ast::Span::synthetic(),
                                }),
                                args: vec![HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::Int(41)),
                                    ty: Type::Int,
                                    span: kea_ast::Span::synthetic(),
                                }],
                            },
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::ClosureInit { .. })),
            "let-bound lambda should lower to a first-class closure value"
        );
        assert!(
            function.blocks[0].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::Call {
                    callee: MirCallee::Value(_),
                    ..
                }
            )),
            "let-bound lambda call should lower through closure indirect-call path"
        );
    }

    #[test]
    fn lower_hir_module_releases_dropped_heap_locals_at_block_exit() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("s".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::String("x".to_string())),
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Release { .. })),
            "heap local dropped at block exit should emit Release"
        );
    }

    #[test]
    fn lower_hir_module_avoids_adjacent_retain_release_churn_for_heap_alias_binding() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("s".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::String("x".to_string())),
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("t".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Var("s".to_string()),
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        let has_retain = function.blocks[0]
            .instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::Retain { .. }));
        let has_adjacent_retain_release_same =
            function.blocks[0].instructions.windows(2).any(|pair| {
                matches!(
                    (&pair[0], &pair[1]),
                    (MirInst::Retain { value: lhs }, MirInst::Release { value: rhs }) if lhs == rhs
                )
            });
        assert!(
            !has_adjacent_retain_release_same,
            "heap alias lowering should not leave adjacent retain/release churn: {:?}",
            function.blocks[0].instructions
        );
        assert!(
            has_retain
                || function.blocks[0]
                    .instructions
                    .iter()
                    .any(|inst| matches!(inst, MirInst::Release { .. })),
            "heap alias lowering should keep memory lifecycle ops observable"
        );
    }

    #[test]
    fn lower_hir_module_transfers_linear_local_heap_alias_without_retain() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("s".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::String("x".to_string())),
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("t".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Var("s".to_string()),
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let instructions = &mir.functions[0].blocks[0].instructions;
        let source_value = instructions
            .iter()
            .find_map(|inst| match inst {
                MirInst::Const {
                    dest,
                    literal: MirLiteral::String(_),
                } => Some(dest.clone()),
                _ => None,
            })
            .expect("expected string literal source value");
        let retain_count = instructions
            .iter()
            .filter(|inst| matches!(inst, MirInst::Retain { value } if *value == source_value))
            .count();
        let release_count = instructions
            .iter()
            .filter(|inst| matches!(inst, MirInst::Release { value } if *value == source_value))
            .count();
        assert_eq!(
            retain_count, 0,
            "linear local alias should transfer ownership without retain: {instructions:?}"
        );
        assert_eq!(
            release_count, 1,
            "linear local alias should keep a single release for lifecycle balance: {instructions:?}"
        );
    }

    #[test]
    fn lower_hir_module_keeps_outer_heap_binding_alive_across_inner_alias_block() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("s".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::String("x".to_string())),
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Block(vec![
                                HirExpr {
                                    kind: HirExprKind::Let {
                                        pattern: HirPattern::Var("t".to_string()),
                                        value: Box::new(HirExpr {
                                            kind: HirExprKind::Var("s".to_string()),
                                            ty: Type::String,
                                            span: kea_ast::Span::synthetic(),
                                        }),
                                    },
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                },
                                HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                                    ty: Type::Int,
                                    span: kea_ast::Span::synthetic(),
                                },
                            ]),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Var("s".to_string()),
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::String,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::String)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        let instructions = &function.blocks[0].instructions;
        let source_value = instructions
            .iter()
            .find_map(|inst| match inst {
                MirInst::Const {
                    dest,
                    literal: MirLiteral::String(_),
                } => Some(dest.clone()),
                _ => None,
            })
            .expect("expected string literal source value");
        let (retain_count, release_count) =
            instructions
                .iter()
                .fold((0usize, 0usize), |(retains, releases), inst| match inst {
                    MirInst::Retain { value } if *value == source_value => (retains + 1, releases),
                    MirInst::Release { value } if *value == source_value => (retains, releases + 1),
                    _ => (retains, releases),
                });
        assert!(
            release_count <= retain_count,
            "outer binding must remain alive across inner alias block; retains={retain_count}, releases={release_count}, instructions={instructions:?}"
        );
        assert!(
            matches!(
                &function.blocks[0].terminator,
                MirTerminator::Return {
                    value: Some(ret)
                } if ret == &source_value
            ),
            "test expects function to return the original outer binding"
        );
    }

    #[test]
    fn lower_hir_module_schedules_block_exit_releases_after_last_use() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Block(vec![
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("s".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Lit(kea_ast::Lit::String("x".to_string())),
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Let {
                                pattern: HirPattern::Var("t".to_string()),
                                value: Box::new(HirExpr {
                                    kind: HirExprKind::Var("s".to_string()),
                                    ty: Type::String,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::String,
                            span: kea_ast::Span::synthetic(),
                        },
                        HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        },
                    ]),
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let instructions = &mir.functions[0].blocks[0].instructions;
        let int_const_idx = instructions
            .iter()
            .position(|inst| {
                matches!(
                    inst,
                    MirInst::Const {
                        literal: MirLiteral::Int(1),
                        ..
                    }
                )
            })
            .expect("expected final int literal in lowered block");
        let release_indices = instructions
            .iter()
            .enumerate()
            .filter_map(|(idx, inst)| matches!(inst, MirInst::Release { .. }).then_some(idx))
            .collect::<Vec<_>>();
        assert!(!release_indices.is_empty(), "expected release instructions");
        assert!(
            release_indices.iter().all(|idx| *idx < int_const_idx),
            "expected releases before unrelated trailing work; releases={release_indices:?}, int_const_idx={int_const_idx}, instructions={instructions:?}"
        );
    }

    #[test]
    fn elide_adjacent_retain_release_pairs_removes_trivial_churn() {
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::Int(7),
                    },
                    MirInst::Retain {
                        value: MirValueId(0),
                    },
                    MirInst::Release {
                        value: MirValueId(0),
                    },
                    MirInst::Nop,
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(0)),
                },
            }],
        };

        elide_adjacent_retain_release_pairs(&mut function);
        assert_eq!(
            function.blocks[0].instructions,
            vec![
                MirInst::Const {
                    dest: MirValueId(0),
                    literal: MirLiteral::Int(7),
                },
                MirInst::Nop,
            ],
            "adjacent retain/release pair should be removed"
        );
    }

    #[test]
    fn elide_adjacent_retain_release_pairs_removes_nop_separated_churn() {
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::Int(7),
                    },
                    MirInst::Retain {
                        value: MirValueId(0),
                    },
                    MirInst::Nop,
                    MirInst::Nop,
                    MirInst::Release {
                        value: MirValueId(0),
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(0)),
                },
            }],
        };

        elide_adjacent_retain_release_pairs(&mut function);
        assert_eq!(
            function.blocks[0].instructions,
            vec![
                MirInst::Const {
                    dest: MirValueId(0),
                    literal: MirLiteral::Int(7),
                },
                MirInst::Nop,
                MirInst::Nop,
            ],
            "nop-separated retain/release pair should be removed"
        );
    }

    #[test]
    fn elide_adjacent_retain_release_pairs_removes_non_interfering_window_churn() {
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::Int(7),
                    },
                    MirInst::Retain {
                        value: MirValueId(0),
                    },
                    MirInst::Const {
                        dest: MirValueId(1),
                        literal: MirLiteral::Int(99),
                    },
                    MirInst::Release {
                        value: MirValueId(0),
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(1)),
                },
            }],
        };

        elide_adjacent_retain_release_pairs(&mut function);
        assert_eq!(
            function.blocks[0].instructions,
            vec![
                MirInst::Const {
                    dest: MirValueId(0),
                    literal: MirLiteral::Int(7),
                },
                MirInst::Const {
                    dest: MirValueId(1),
                    literal: MirLiteral::Int(99),
                },
            ],
            "non-interfering retain/release window should be removed"
        );
    }

    #[test]
    fn fuse_release_alloc_same_layout_rewrites_to_record_init_reuse() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::Int(1),
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(1),
                        record_type: "Point".to_string(),
                        fields: vec![("x".to_string(), MirValueId(0))],
                    },
                    MirInst::Release {
                        value: MirValueId(1),
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(2),
                        record_type: "Point".to_string(),
                        fields: vec![("x".to_string(), MirValueId(0))],
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(2)),
                },
            }],
        };

        fuse_release_alloc_same_layout(&mut function, &layouts);

        assert!(
            function.blocks[0].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::RecordInitReuse {
                    source,
                    record_type,
                    ..
                } if *source == MirValueId(1) && record_type == "Point"
            )),
            "expected release+alloc pair to fuse into RecordInitReuse: {:?}",
            function.blocks[0].instructions
        );
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::Release { value } if *value == MirValueId(1))),
            "fused path should consume the source without a standalone release"
        );
    }

    #[test]
    fn fuse_release_alloc_same_layout_skips_managed_record_layouts() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Boxed".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "s".to_string(),
                    annotation: TypeAnnotation::Named("String".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::String("x".to_string()),
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(1),
                        record_type: "Boxed".to_string(),
                        fields: vec![("s".to_string(), MirValueId(0))],
                    },
                    MirInst::Release {
                        value: MirValueId(1),
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(2),
                        record_type: "Boxed".to_string(),
                        fields: vec![("s".to_string(), MirValueId(0))],
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(2)),
                },
            }],
        };

        fuse_release_alloc_same_layout(&mut function, &layouts);

        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::RecordInitReuse { .. })),
            "managed-field records should not be fused into reuse init"
        );
    }

    #[test]
    fn fuse_release_alloc_same_layout_rewrites_non_adjacent_non_interfering_init() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::Int(1),
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(1),
                        record_type: "Point".to_string(),
                        fields: vec![("x".to_string(), MirValueId(0))],
                    },
                    MirInst::Release {
                        value: MirValueId(1),
                    },
                    MirInst::Const {
                        dest: MirValueId(2),
                        literal: MirLiteral::Int(99),
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(3),
                        record_type: "Point".to_string(),
                        fields: vec![("x".to_string(), MirValueId(2))],
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(3)),
                },
            }],
        };

        fuse_release_alloc_same_layout(&mut function, &layouts);

        assert!(matches!(
            function.blocks[0].instructions[2],
            MirInst::Const {
                dest: MirValueId(2),
                literal: MirLiteral::Int(99)
            }
        ));
        assert!(matches!(
            function.blocks[0].instructions[3],
            MirInst::RecordInitReuse {
                source: MirValueId(1),
                dest: MirValueId(3),
                ..
            }
        ));
    }

    #[test]
    fn fuse_release_alloc_same_layout_stops_when_released_value_is_read_before_alloc() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::Int(1),
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(1),
                        record_type: "Point".to_string(),
                        fields: vec![("x".to_string(), MirValueId(0))],
                    },
                    MirInst::Release {
                        value: MirValueId(1),
                    },
                    MirInst::RecordFieldLoad {
                        dest: MirValueId(2),
                        record: MirValueId(1),
                        record_type: "Point".to_string(),
                        field: "x".to_string(),
                        field_ty: Type::Int,
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(3),
                        record_type: "Point".to_string(),
                        fields: vec![("x".to_string(), MirValueId(2))],
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(3)),
                },
            }],
        };

        fuse_release_alloc_same_layout(&mut function, &layouts);

        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::RecordInitReuse { .. })),
            "released value use before alloc should block reuse fusion"
        );
    }

    #[test]
    fn fuse_release_alloc_same_layout_rewrites_sum_init_to_sum_init_reuse() {
        let layouts = MirLayoutCatalog {
            records: vec![],
            sums: vec![MirSumLayout {
                name: "Pairish".to_string(),
                variants: vec![
                    MirVariantLayout {
                        name: "Left".to_string(),
                        tag: 0,
                        fields: vec![MirVariantFieldLayout {
                            name: None,
                            annotation: TypeAnnotation::Named("Int".to_string()),
                        }],
                    },
                    MirVariantLayout {
                        name: "Right".to_string(),
                        tag: 1,
                        fields: vec![MirVariantFieldLayout {
                            name: None,
                            annotation: TypeAnnotation::Named("Int".to_string()),
                        }],
                    },
                ],
            }],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::Int(1),
                    },
                    MirInst::SumInit {
                        dest: MirValueId(1),
                        sum_type: "Pairish".to_string(),
                        variant: "Left".to_string(),
                        tag: 0,
                        fields: vec![MirValueId(0)],
                    },
                    MirInst::Release {
                        value: MirValueId(1),
                    },
                    MirInst::Const {
                        dest: MirValueId(2),
                        literal: MirLiteral::Int(2),
                    },
                    MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Pairish".to_string(),
                        variant: "Right".to_string(),
                        tag: 1,
                        fields: vec![MirValueId(2)],
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(3)),
                },
            }],
        };

        fuse_release_alloc_same_layout(&mut function, &layouts);

        assert!(
            function.blocks[0].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::SumInitReuse {
                    source,
                    sum_type,
                    variant,
                    ..
                } if *source == MirValueId(1) && sum_type == "Pairish" && variant == "Right"
            )),
            "expected release+sum init pair to fuse into SumInitReuse: {:?}",
            function.blocks[0].instructions
        );
    }

    #[test]
    fn fuse_release_alloc_same_layout_skips_sum_reuse_for_unit_mixed_layouts() {
        let layouts = MirLayoutCatalog {
            records: vec![],
            sums: vec![MirSumLayout {
                name: "Option".to_string(),
                variants: vec![
                    MirVariantLayout {
                        name: "Some".to_string(),
                        tag: 0,
                        fields: vec![MirVariantFieldLayout {
                            name: None,
                            annotation: TypeAnnotation::Named("Int".to_string()),
                        }],
                    },
                    MirVariantLayout {
                        name: "None".to_string(),
                        tag: 1,
                        fields: vec![],
                    },
                ],
            }],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::Int(1),
                    },
                    MirInst::SumInit {
                        dest: MirValueId(1),
                        sum_type: "Option".to_string(),
                        variant: "Some".to_string(),
                        tag: 0,
                        fields: vec![MirValueId(0)],
                    },
                    MirInst::Release {
                        value: MirValueId(1),
                    },
                    MirInst::Const {
                        dest: MirValueId(2),
                        literal: MirLiteral::Int(2),
                    },
                    MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Option".to_string(),
                        variant: "Some".to_string(),
                        tag: 0,
                        fields: vec![MirValueId(2)],
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(3)),
                },
            }],
        };

        fuse_release_alloc_same_layout(&mut function, &layouts);

        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::SumInitReuse { .. })),
            "mixed unit/payload sum layouts should not be fused into SumInitReuse"
        );
    }

    #[test]
    fn fuse_release_alloc_cross_block_jump_rewrites_successor_init_to_reuse() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
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
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(0))],
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
                            name: "Point".to_string(),
                            params: vec![],
                        }),
                    }],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(9),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(3),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(2))],
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(3)),
                    },
                },
            ],
        };

        fuse_release_alloc_cross_block_jump(&mut function, &layouts);

        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::Release { value } if *value == MirValueId(1))),
            "release should be consumed by cross-block reuse rewrite"
        );
        assert!(matches!(
            function.blocks[1].instructions[1],
            MirInst::RecordInitReuse {
                source: MirValueId(10),
                record_type: ref name,
                ..
            } if name == "Point"
        ));
    }

    #[test]
    fn fuse_release_alloc_cross_block_jump_rewrites_with_trailing_nops_after_release() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
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
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(0))],
                        },
                        MirInst::Release {
                            value: MirValueId(1),
                        },
                        MirInst::Nop,
                        MirInst::Nop,
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
                            name: "Point".to_string(),
                            params: vec![],
                        }),
                    }],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(9),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(3),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(2))],
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(3)),
                    },
                },
            ],
        };

        fuse_release_alloc_cross_block_jump(&mut function, &layouts);

        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::Release { value } if *value == MirValueId(1)))
        );
        assert!(matches!(
            function.blocks[1].instructions[1],
            MirInst::RecordInitReuse {
                source: MirValueId(10),
                record_type: ref name,
                ..
            } if name == "Point"
        ));
    }

    #[test]
    fn fuse_release_alloc_cross_block_jump_rewrites_join_when_all_predecessors_release() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
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
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(0))],
                        },
                        MirInst::Release {
                            value: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(2),
                        args: vec![MirValueId(1)],
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(2),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(5),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(4))],
                        },
                        MirInst::Release {
                            value: MirValueId(5),
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(2),
                        args: vec![MirValueId(5)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![MirBlockParam {
                        id: MirValueId(10),
                        ty: Type::Record(RecordType {
                            name: "Point".to_string(),
                            params: vec![],
                        }),
                    }],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(9),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(3),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(2))],
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(3)),
                    },
                },
            ],
        };

        fuse_release_alloc_cross_block_jump(&mut function, &layouts);

        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::Release { value } if *value == MirValueId(1)))
        );
        assert!(
            function.blocks[1]
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::Release { value } if *value == MirValueId(5)))
        );
        assert!(matches!(
            function.blocks[2].instructions[1],
            MirInst::RecordInitReuse {
                source: MirValueId(10),
                record_type: ref name,
                ..
            } if name == "Point"
        ));
    }

    #[test]
    fn fuse_release_alloc_cross_block_jump_skips_when_any_predecessor_lacks_release() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
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
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(0))],
                        },
                        MirInst::Release {
                            value: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(2),
                        args: vec![MirValueId(1)],
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(2),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(5),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(4))],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(2),
                        args: vec![MirValueId(5)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![MirBlockParam {
                        id: MirValueId(10),
                        ty: Type::Record(RecordType {
                            name: "Point".to_string(),
                            params: vec![],
                        }),
                    }],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(9),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(3),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(2))],
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(3)),
                    },
                },
            ],
        };

        fuse_release_alloc_cross_block_jump(&mut function, &layouts);

        assert!(matches!(
            function.blocks[0].instructions.last(),
            Some(MirInst::Release {
                value: MirValueId(1)
            })
        ));
        assert!(matches!(
            function.blocks[2].instructions[1],
            MirInst::RecordInit { .. }
        ));
    }

    #[test]
    fn fuse_release_alloc_cross_block_jump_skips_when_non_nop_follows_release() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
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
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(0))],
                        },
                        MirInst::Release {
                            value: MirValueId(1),
                        },
                        MirInst::Const {
                            dest: MirValueId(7),
                            literal: MirLiteral::Int(0),
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
                            name: "Point".to_string(),
                            params: vec![],
                        }),
                    }],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(9),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(3),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(2))],
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(3)),
                    },
                },
            ],
        };

        fuse_release_alloc_cross_block_jump(&mut function, &layouts);

        assert!(matches!(
            function.blocks[0].instructions[2],
            MirInst::Release {
                value: MirValueId(1)
            }
        ));
        assert!(matches!(
            function.blocks[1].instructions[1],
            MirInst::RecordInit { .. }
        ));
    }

    #[test]
    fn emit_reuse_tokens_for_mixed_predecessor_join_rewrites_release_and_target_init() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
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
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(0))],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(2),
                        args: vec![MirValueId(1)],
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(2),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(3),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(2))],
                        },
                        MirInst::Release {
                            value: MirValueId(3),
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(2),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![MirBlockParam {
                        id: MirValueId(10),
                        ty: Type::Record(RecordType {
                            name: "Point".to_string(),
                            params: vec![],
                        }),
                    }],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(9),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(5),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(4))],
                        },
                    ],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(5)),
                    },
                },
            ],
        };

        emit_reuse_tokens_for_mixed_predecessor_joins(&mut function, &layouts);

        assert_eq!(function.blocks[2].params.len(), 2);
        let token_param = function.blocks[2].params[1].id.clone();
        assert!(matches!(
            function.blocks[2].instructions[1],
            MirInst::RecordInitFromToken {
                token: ref t,
                record_type: ref name,
                ..
            } if *t == token_param && name == "Point"
        ));

        assert!(matches!(
            function.blocks[1].instructions[2],
            MirInst::ReuseToken {
                source: MirValueId(3),
                ..
            }
        ));
        assert!(matches!(
            function.blocks[0].instructions.last(),
            Some(MirInst::Const {
                literal: MirLiteral::Int(0),
                ..
            })
        ));

        let MirTerminator::Jump {
            args: block0_args, ..
        } = &function.blocks[0].terminator
        else {
            panic!("expected block0 jump terminator");
        };
        let MirTerminator::Jump {
            args: block1_args, ..
        } = &function.blocks[1].terminator
        else {
            panic!("expected block1 jump terminator");
        };
        assert_eq!(block0_args.len(), 2);
        assert_eq!(block1_args.len(), 2);
    }

    #[test]
    fn emit_reuse_tokens_for_loop_backedge_join_rewrites_all_releasing_predecessors() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
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
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(0))],
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
                            name: "Point".to_string(),
                            params: vec![],
                        }),
                    }],
                    instructions: vec![MirInst::Release {
                        value: MirValueId(10),
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(2),
                        args: vec![MirValueId(10)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![MirBlockParam {
                        id: MirValueId(11),
                        ty: Type::Record(RecordType {
                            name: "Point".to_string(),
                            params: vec![],
                        }),
                    }],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(2),
                        },
                        MirInst::RecordInit {
                            dest: MirValueId(3),
                            record_type: "Point".to_string(),
                            fields: vec![("x".to_string(), MirValueId(2))],
                        },
                        MirInst::Release {
                            value: MirValueId(3),
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(2),
                        args: vec![MirValueId(3)],
                    },
                },
            ],
        };

        emit_reuse_tokens_for_mixed_predecessor_joins(&mut function, &layouts);
        emit_reuse_tokens_for_loop_backedge_joins(&mut function, &layouts);

        assert_eq!(function.blocks[2].params.len(), 2);
        let token_param = function.blocks[2].params[1].id.clone();
        assert!(matches!(
            function.blocks[2].instructions[1],
            MirInst::RecordInitFromToken {
                token: ref t,
                record_type: ref name,
                ..
            } if *t == token_param && name == "Point"
        ));

        assert!(matches!(
            function.blocks[1].instructions[0],
            MirInst::ReuseToken {
                source: MirValueId(10),
                ..
            }
        ));
        assert!(matches!(
            function.blocks[2].instructions[2],
            MirInst::ReuseToken {
                source: MirValueId(3),
                ..
            }
        ));

        let MirTerminator::Jump {
            args: block1_args, ..
        } = &function.blocks[1].terminator
        else {
            panic!("expected block1 jump terminator");
        };
        let MirTerminator::Jump {
            args: block2_args, ..
        } = &function.blocks[2].terminator
        else {
            panic!("expected block2 jump terminator");
        };
        assert_eq!(block1_args.len(), 2);
        assert_eq!(block2_args.len(), 2);
    }

    #[test]
    fn emit_reuse_tokens_for_trailing_release_alloc_rewrites_same_block_init() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
            is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "main".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Record(RecordType {
                    name: "Point".to_string(),
                    params: vec![],
                })],
                ret: Type::Record(RecordType {
                    name: "Point".to_string(),
                    params: vec![],
                }),
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(1),
                        literal: MirLiteral::Int(9),
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(2),
                        record_type: "Point".to_string(),
                        fields: vec![("x".to_string(), MirValueId(1))],
                    },
                    MirInst::Release {
                        value: MirValueId(0),
                    },
                ],
                terminator: MirTerminator::Return {
                    value: Some(MirValueId(2)),
                },
            }],
        };

        emit_reuse_tokens_for_trailing_release_alloc(&mut function, &layouts);

        assert_eq!(function.blocks[0].instructions.len(), 3);
        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::ReuseToken {
                source: MirValueId(0),
                ..
            }
        ));
        assert!(matches!(
            function.blocks[0].instructions[2],
            MirInst::RecordInitFromToken { .. }
        ));
    }

    #[test]
    fn emit_reuse_tokens_for_trailing_release_alloc_skips_self_released_init() {
        let layouts = MirLayoutCatalog {
            records: vec![MirRecordLayout {
                name: "Point".to_string(),
                is_unboxed: false,
                fields: vec![MirRecordFieldLayout {
                    name: "x".to_string(),
                    annotation: TypeAnnotation::Named("Int".to_string()),
                }],
            }],
            sums: vec![],
        };
        let mut function = MirFunction {
            name: "consume".to_string(),
            signature: MirFunctionSignature {
                params: vec![],
                ret: Type::Unit,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Const {
                        dest: MirValueId(0),
                        literal: MirLiteral::Int(1),
                    },
                    MirInst::RecordInit {
                        dest: MirValueId(1),
                        record_type: "Point".to_string(),
                        fields: vec![("x".to_string(), MirValueId(0))],
                    },
                    MirInst::Release {
                        value: MirValueId(1),
                    },
                ],
                terminator: MirTerminator::Return { value: None },
            }],
        };

        emit_reuse_tokens_for_trailing_release_alloc(&mut function, &layouts);

        assert!(matches!(
            function.blocks[0].instructions[1],
            MirInst::RecordInit { .. }
        ));
        assert!(matches!(
            function.blocks[0].instructions[2],
            MirInst::Release {
                value: MirValueId(1)
            }
        ));
        assert!(
            !function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(
                    inst,
                    MirInst::ReuseToken { .. } | MirInst::RecordInitFromToken { .. }
                ))
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_rewrites_recursive_constructor_call() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(7),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(6)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(7)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(8),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(8)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert_eq!(function.blocks.len(), 4);
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should remove recursive call from constructor branch"
        );
        assert!(matches!(
            function.blocks[0].terminator,
            MirTerminator::Jump { .. }
        ));
        assert!(matches!(
            function.blocks[1].terminator,
            MirTerminator::Branch { .. }
        ));
        assert!(matches!(
            function.blocks[2].terminator,
            MirTerminator::Jump { .. }
        ));
        assert!(matches!(
            function.blocks[3].terminator,
            MirTerminator::Return { .. }
        ));
        let step_instructions = &function.blocks[2].instructions;
        let step_sum_dest = step_instructions.iter().find_map(|inst| match inst {
            MirInst::SumInit { dest, .. } => Some(dest.clone()),
            _ => None,
        });
        let step_next_i_dest = step_instructions.iter().find_map(|inst| match inst {
            MirInst::Binary {
                dest,
                op: MirBinaryOp::Add,
                ..
            } => Some(dest.clone()),
            _ => None,
        });
        assert!(
            step_sum_dest.is_some() && step_next_i_dest.is_some(),
            "rewritten step block should contain sum construction + index increment"
        );
        assert_ne!(
            step_sum_dest, step_next_i_dest,
            "rewritten accumulator sum value and next loop index must use distinct SSA value IDs"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_nonzero_base_threshold() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(2),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(7),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(6)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(7)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(8),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(8)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should remove recursive call for non-zero lte base thresholds"
        );

        let entry_block = &function.blocks[0];
        let Some(base_start_const) = entry_block.instructions.iter().find_map(|inst| match inst {
            MirInst::Const {
                dest,
                literal: MirLiteral::Int(3),
            } => Some(dest.clone()),
            _ => None,
        }) else {
            panic!("rewritten entry block should materialize loop start literal threshold+1");
        };
        let Some(loop_start_value) = entry_block.instructions.iter().find_map(|inst| match inst {
            MirInst::Binary {
                dest,
                op: MirBinaryOp::Add,
                left,
                ..
            } if *left == base_start_const => Some(dest.clone()),
            _ => None,
        }) else {
            panic!("rewritten entry block should compute loop start from threshold+1");
        };
        let MirTerminator::Jump { args, .. } = &entry_block.terminator else {
            panic!("rewritten entry block should terminate with jump");
        };
        assert_eq!(
            args.first(),
            Some(&loop_start_value),
            "loop should start at threshold+1 for non-zero base thresholds"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_step_two_decrement() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(2),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(7),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(6)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(7)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(8),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(8)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        let loop_i = function.blocks[1].params[0].id.clone();
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should remove recursive call for descending n - 2 recursion"
        );

        let step_const = function.blocks[0]
            .instructions
            .iter()
            .find_map(|inst| match inst {
                MirInst::Const {
                    dest,
                    literal: MirLiteral::Int(2),
                } => Some(dest.clone()),
                _ => None,
            })
            .expect("entry block should contain step=2 literal");
        assert!(
            function.blocks[2].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::Binary {
                    op: MirBinaryOp::Add,
                    left,
                    right,
                    ..
                } if *left == loop_i && *right == step_const
            )),
            "step block should advance loop index by the extracted decrement amount"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_add_negative_step_decrement() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(-2),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Add,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(7),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(6)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(7)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(8),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(8)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        let loop_i = function.blocks[1].params[0].id.clone();
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should remove recursive call for descending n + (-2) recursion"
        );

        let step_const = function.blocks[0]
            .instructions
            .iter()
            .find_map(|inst| match inst {
                MirInst::Const {
                    dest,
                    literal: MirLiteral::Int(2),
                } => Some(dest.clone()),
                _ => None,
            })
            .expect("entry block should normalize n + (-2) to step=2 literal");
        assert!(
            function.blocks[2].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::Binary {
                    op: MirBinaryOp::Add,
                    left,
                    right,
                    ..
                } if *left == loop_i && *right == step_const
            )),
            "step block should advance loop index by the normalized positive decrement amount"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_expression_threshold_and_step() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(3),
                            op: MirBinaryOp::Add,
                            left: MirValueId(1),
                            right: MirValueId(2),
                        },
                        MirInst::Binary {
                            dest: MirValueId(4),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(3),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(4),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(5),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(5)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(6),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Const {
                            dest: MirValueId(7),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(8),
                            op: MirBinaryOp::Add,
                            left: MirValueId(6),
                            right: MirValueId(7),
                        },
                        MirInst::Binary {
                            dest: MirValueId(9),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(8),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(9)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(10)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(11),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(10)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(11)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(12),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(12)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should fold simple integer constant expressions used by threshold and decrement step"
        );

        let entry_block = &function.blocks[0];
        let Some(base_start_const) = entry_block.instructions.iter().find_map(|inst| match inst {
            MirInst::Const {
                dest,
                literal: MirLiteral::Int(3),
            } => Some(dest.clone()),
            _ => None,
        }) else {
            panic!(
                "rewritten entry block should materialize loop start literal threshold+1 for folded `n <= 1 + 1`"
            );
        };
        assert!(
            entry_block.instructions.iter().any(|inst| matches!(
                inst,
                MirInst::Binary {
                    op: MirBinaryOp::Add,
                    left,
                    ..
                } if *left == base_start_const
            )),
            "rewritten entry block should compute loop start from folded threshold expression"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_pre_call_non_recursive_helper_call() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("weight".to_string()),
                            args: vec![MirValueId(0)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Int,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(7)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(8),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(6), MirValueId(7)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(8)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(9),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(9)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        let loop_i = function.blocks[1].params[0].id.clone();
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(
                    inst,
                    MirInst::Call {
                        callee: MirCallee::Local(name),
                        ..
                    } if name == "build"
                )),
            "rewrite should remove recursive self call even when recurse branch has a pre-call helper invocation"
        );
        assert!(
            function.blocks[2].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::Call {
                    callee: MirCallee::Local(name),
                    args,
                    ..
                } if name == "weight" && args.len() == 1 && args[0] == loop_i
            )),
            "step block should preserve/remap non-recursive helper call before constructor assembly"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_hoisted_step_constant() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(2),
                        },
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(3),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(2),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(3),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(4),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(4)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(7),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(6)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(7)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(8),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(8)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should support descending recursion when decrement constant is hoisted outside recurse block"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_lt_base_threshold() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(3),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Lt,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(7),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(6)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(7)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(8),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(8)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should support `<` threshold guards by translating them to equivalent <= threshold"
        );
        let entry_block = &function.blocks[0];
        let Some(base_start_const) = entry_block.instructions.iter().find_map(|inst| match inst {
            MirInst::Const {
                dest,
                literal: MirLiteral::Int(3),
            } => Some(dest.clone()),
            _ => None,
        }) else {
            panic!("rewritten entry block should materialize loop start literal 3 for `n < 3`");
        };
        let Some(loop_start_value) = entry_block.instructions.iter().find_map(|inst| match inst {
            MirInst::Binary {
                dest,
                op: MirBinaryOp::Add,
                left,
                ..
            } if *left == base_start_const => Some(dest.clone()),
            _ => None,
        }) else {
            panic!("rewritten entry block should compute loop start from translated threshold");
        };
        let MirTerminator::Jump { args, .. } = &entry_block.terminator else {
            panic!("rewritten entry block should terminate with jump");
        };
        assert_eq!(
            args.first(),
            Some(&loop_start_value),
            "loop should start at 3 for `n < 3` (equivalent to `n <= 2`)"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_gt_recurse_branch() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Gt,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(2),
                        else_block: MirBlockId(1),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(7),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(6)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(7)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(8),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(8)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should support `if n > c then recurse else base` orientation"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_flipped_gte_threshold() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(2),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Gte,
                            left: MirValueId(1),
                            right: MirValueId(0),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(7),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(6)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(7)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(8),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(8)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should support flipped `const >= n` thresholds"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_rejects_non_ordering_base_condition() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Eq,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(6)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(7),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(0), MirValueId(6)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(7)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(8),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(8)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .any(|inst| matches!(inst, MirInst::Call { .. })),
            "rewrite must not fire when the base condition is not an ordering threshold check"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_preserves_pre_call_constructor_fields() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(1),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(2),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(1),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(2),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(3),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(3)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(4),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(5),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(4),
                        },
                        MirInst::Binary {
                            dest: MirValueId(6),
                            op: MirBinaryOp::Add,
                            left: MirValueId(0),
                            right: MirValueId(0),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(5)],
                            arg_types: vec![Type::Int],
                            result: Some(MirValueId(7)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(8),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(6), MirValueId(7)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(8)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(9),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(9)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        let loop_i = function.blocks[1].params[0].id.clone();
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should remove recursive call from constructor branch"
        );
        assert!(
            function.blocks[2].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::Binary {
                    op: MirBinaryOp::Add,
                    left,
                    right,
                    ..
                } if *left == loop_i && *right == loop_i
            )),
            "step block should keep pre-call constructor field expressions remapped to loop index"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_passthrough_extra_params() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int, Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(3),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(2),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(3),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(4),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(4)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(5),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(6),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(5),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(6), MirValueId(1)],
                            arg_types: vec![Type::Int, Type::Int],
                            result: Some(MirValueId(7)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(8),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(1), MirValueId(7)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(8)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(9),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(9)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should remove recursive call when non-recursive params are passthrough"
        );
        assert!(
            function.blocks[2].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::SumInit { fields, .. } if fields.first() == Some(&MirValueId(1))
            )),
            "step block should preserve passthrough extra parameter in constructor fields"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_supports_recursive_second_param() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int, Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(3),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(1),
                            right: MirValueId(2),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(3),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(4),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(4)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(5),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(6),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(1),
                            right: MirValueId(5),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(0), MirValueId(6)],
                            arg_types: vec![Type::Int, Type::Int],
                            result: Some(MirValueId(7)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(8),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(1), MirValueId(7)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(8)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(9),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(9)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert_eq!(function.blocks.len(), 4);
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "rewrite should support descending recursion when the recursive parameter is not arg0"
        );
    }

    #[test]
    fn rewrite_trmc_descending_sum_chain_rejects_rewritten_extra_params() {
        let mut function = MirFunction {
            name: "build".to_string(),
            signature: MirFunctionSignature {
                params: vec![Type::Int, Type::Int],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(2),
                            literal: MirLiteral::Int(0),
                        },
                        MirInst::Binary {
                            dest: MirValueId(3),
                            op: MirBinaryOp::Lte,
                            left: MirValueId(0),
                            right: MirValueId(2),
                        },
                    ],
                    terminator: MirTerminator::Branch {
                        condition: MirValueId(3),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumInit {
                        dest: MirValueId(4),
                        sum_type: "Chain".to_string(),
                        variant: "End".to_string(),
                        tag: 0,
                        fields: vec![],
                    }],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(4)],
                    },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![
                        MirInst::Const {
                            dest: MirValueId(5),
                            literal: MirLiteral::Int(1),
                        },
                        MirInst::Binary {
                            dest: MirValueId(6),
                            op: MirBinaryOp::Sub,
                            left: MirValueId(0),
                            right: MirValueId(5),
                        },
                        MirInst::Binary {
                            dest: MirValueId(7),
                            op: MirBinaryOp::Add,
                            left: MirValueId(1),
                            right: MirValueId(5),
                        },
                        MirInst::Call {
                            callee: MirCallee::Local("build".to_string()),
                            args: vec![MirValueId(6), MirValueId(7)],
                            arg_types: vec![Type::Int, Type::Int],
                            result: Some(MirValueId(8)),
                            ret_type: Type::Dynamic,
                            callee_fail_result_abi: false,
                            capture_fail_result: false,
                            cc_manifest_id: "default".to_string(),
                        },
                        MirInst::SumInit {
                            dest: MirValueId(9),
                            sum_type: "Chain".to_string(),
                            variant: "Node".to_string(),
                            tag: 1,
                            fields: vec![MirValueId(7), MirValueId(8)],
                        },
                    ],
                    terminator: MirTerminator::Jump {
                        target: MirBlockId(3),
                        args: vec![MirValueId(9)],
                    },
                },
                MirBlock {
                    id: MirBlockId(3),
                    params: vec![MirBlockParam {
                        id: MirValueId(10),
                        ty: Type::Dynamic,
                    }],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return {
                        value: Some(MirValueId(10)),
                    },
                },
            ],
        };

        rewrite_trmc_descending_sum_chain(&mut function);

        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .any(|inst| matches!(inst, MirInst::Call { .. })),
            "rewrite should not fire when extra parameters are transformed before recursive call"
        );
    }

    #[test]
    fn lower_hir_module_inlines_let_bound_lambda_from_factory_call() {
        let inner_fn_ty = Type::Function(FunctionType::pure(vec![Type::Int], Type::Int));
        let make_adder_ty =
            Type::Function(FunctionType::pure(vec![Type::Int], inner_fn_ty.clone()));
        let hir = HirModule {
            declarations: vec![
                HirDecl::Function(HirFunction {
                    name: "make_adder".to_string(),
                    params: vec![kea_hir::HirParam {
                        name: Some("y".to_string()),
                        span: kea_ast::Span::synthetic(),
                    }],
                    body: HirExpr {
                        kind: HirExprKind::Lambda {
                            params: vec![kea_hir::HirParam {
                                name: Some("x".to_string()),
                                span: kea_ast::Span::synthetic(),
                            }],
                            body: Box::new(HirExpr {
                                kind: HirExprKind::Binary {
                                    op: BinOp::Add,
                                    left: Box::new(HirExpr {
                                        kind: HirExprKind::Var("x".to_string()),
                                        ty: Type::Int,
                                        span: kea_ast::Span::synthetic(),
                                    }),
                                    right: Box::new(HirExpr {
                                        kind: HirExprKind::Var("y".to_string()),
                                        ty: Type::Int,
                                        span: kea_ast::Span::synthetic(),
                                    }),
                                },
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            }),
                        },
                        ty: inner_fn_ty.clone(),
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: make_adder_ty.clone(),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
                HirDecl::Function(HirFunction {
                    name: "main".to_string(),
                    params: vec![],
                    body: HirExpr {
                        kind: HirExprKind::Block(vec![
                            HirExpr {
                                kind: HirExprKind::Let {
                                    pattern: HirPattern::Var("add2".to_string()),
                                    value: Box::new(HirExpr {
                                        kind: HirExprKind::Call {
                                            func: Box::new(HirExpr {
                                                kind: HirExprKind::Var("make_adder".to_string()),
                                                ty: make_adder_ty.clone(),
                                                span: kea_ast::Span::synthetic(),
                                            }),
                                            args: vec![HirExpr {
                                                kind: HirExprKind::Lit(kea_ast::Lit::Int(2)),
                                                ty: Type::Int,
                                                span: kea_ast::Span::synthetic(),
                                            }],
                                        },
                                        ty: inner_fn_ty.clone(),
                                        span: kea_ast::Span::synthetic(),
                                    }),
                                },
                                ty: inner_fn_ty.clone(),
                                span: kea_ast::Span::synthetic(),
                            },
                            HirExpr {
                                kind: HirExprKind::Call {
                                    func: Box::new(HirExpr {
                                        kind: HirExprKind::Var("add2".to_string()),
                                        ty: inner_fn_ty.clone(),
                                        span: kea_ast::Span::synthetic(),
                                    }),
                                    args: vec![HirExpr {
                                        kind: HirExprKind::Lit(kea_ast::Lit::Int(40)),
                                        ty: Type::Int,
                                        span: kea_ast::Span::synthetic(),
                                    }],
                                },
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            },
                        ]),
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
            ],
        };

        let mir = lower_hir_module(&hir);
        let main_fn = mir
            .functions
            .iter()
            .find(|func| func.name == "main")
            .expect("main should lower");
        assert!(
            main_fn.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Call { callee: MirCallee::Local(name), .. } if name == "make_adder")),
            "factory call should stay as a regular local call"
        );
        assert!(
            main_fn.blocks[0].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::Call {
                    callee: MirCallee::Value(_),
                    ..
                }
            )),
            "factory-returned closure call should lower through indirect closure dispatch"
        );
    }

    #[test]
    fn lower_hir_module_resolves_record_field_load_for_call_result_var_type() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        });
        let hir = HirModule {
            declarations: vec![
                HirDecl::Raw(DeclKind::RecordDef(RecordDef {
                    public: true,
                    name: sp("User".to_string()),
                    doc: None,
                    annotations: vec![],
                    params: vec![],
                    fields: vec![(
                        sp("age".to_string()),
                        TypeAnnotation::Named("Int".to_string()),
                    )],
                    const_fields: vec![],
                    field_annotations: vec![],
                methods: vec![],
                })),
                HirDecl::Function(HirFunction {
                    name: "id_user".to_string(),
                    params: vec![HirParam {
                        name: Some("u".to_string()),
                        span: kea_ast::Span::synthetic(),
                    }],
                    body: HirExpr {
                        kind: HirExprKind::Var("u".to_string()),
                        ty: user_ty.clone(),
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(vec![user_ty.clone()], user_ty.clone())),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
                HirDecl::Function(HirFunction {
                    name: "main".to_string(),
                    params: vec![],
                    body: HirExpr {
                        kind: HirExprKind::FieldAccess {
                            expr: Box::new(HirExpr {
                                kind: HirExprKind::Call {
                                    func: Box::new(HirExpr {
                                        kind: HirExprKind::Var("id_user".to_string()),
                                        ty: Type::Dynamic,
                                        span: kea_ast::Span::synthetic(),
                                    }),
                                    args: vec![HirExpr {
                                        kind: HirExprKind::RecordLit {
                                            record_type: "User".to_string(),
                                            fields: vec![(
                                                "age".to_string(),
                                                HirExpr {
                                                    kind: HirExprKind::Lit(kea_ast::Lit::Int(42)),
                                                    ty: Type::Int,
                                                    span: kea_ast::Span::synthetic(),
                                                },
                                            )],
                                        },
                                        ty: user_ty.clone(),
                                        span: kea_ast::Span::synthetic(),
                                    }],
                                },
                                ty: Type::Dynamic,
                                span: kea_ast::Span::synthetic(),
                            }),
                            field: "age".to_string(),
                        },
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
            ],
        };

        let mir = lower_hir_module(&hir);
        let main_fn = mir
            .functions
            .iter()
            .find(|func| func.name == "main")
            .expect("main should lower");
        assert!(
            main_fn
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .any(|inst| matches!(
                    inst,
                    MirInst::RecordFieldLoad {
                        record_type,
                        field,
                        field_ty: Type::Int,
                        ..
                    } if record_type == "User" && field == "age"
                )),
            "expected call-result field access to resolve record layout"
        );
    }

    #[test]
    fn lower_hir_module_lowers_escaping_capturing_factory_call_to_closure_value() {
        let inner_fn_ty = Type::Function(FunctionType::pure(vec![Type::Int], Type::Int));
        let make_adder_ty =
            Type::Function(FunctionType::pure(vec![Type::Int], inner_fn_ty.clone()));
        let hir = HirModule {
            declarations: vec![
                HirDecl::Function(HirFunction {
                    name: "make_adder".to_string(),
                    params: vec![kea_hir::HirParam {
                        name: Some("y".to_string()),
                        span: kea_ast::Span::synthetic(),
                    }],
                    body: HirExpr {
                        kind: HirExprKind::Lambda {
                            params: vec![kea_hir::HirParam {
                                name: Some("x".to_string()),
                                span: kea_ast::Span::synthetic(),
                            }],
                            body: Box::new(HirExpr {
                                kind: HirExprKind::Binary {
                                    op: BinOp::Add,
                                    left: Box::new(HirExpr {
                                        kind: HirExprKind::Var("x".to_string()),
                                        ty: Type::Int,
                                        span: kea_ast::Span::synthetic(),
                                    }),
                                    right: Box::new(HirExpr {
                                        kind: HirExprKind::Var("y".to_string()),
                                        ty: Type::Int,
                                        span: kea_ast::Span::synthetic(),
                                    }),
                                },
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            }),
                        },
                        ty: inner_fn_ty.clone(),
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: make_adder_ty.clone(),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
                HirDecl::Function(HirFunction {
                    name: "factory_use".to_string(),
                    params: vec![],
                    body: HirExpr {
                        kind: HirExprKind::Call {
                            func: Box::new(HirExpr {
                                kind: HirExprKind::Var("make_adder".to_string()),
                                ty: make_adder_ty,
                                span: kea_ast::Span::synthetic(),
                            }),
                            args: vec![HirExpr {
                                kind: HirExprKind::Lit(kea_ast::Lit::Int(2)),
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            }],
                        },
                        ty: inner_fn_ty.clone(),
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(vec![], inner_fn_ty)),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
            ],
        };

        let mir = lower_hir_module(&hir);
        let factory_use = mir
            .functions
            .iter()
            .find(|func| func.name == "factory_use")
            .expect("factory_use should lower");
        assert!(
            factory_use
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .any(|inst| matches!(inst, MirInst::Call { callee: MirCallee::Local(name), .. } if name == "make_adder")),
            "escaping capturing factory value should lower via normal call result"
        );
        assert!(
            !factory_use
                .blocks
                .iter()
                .flat_map(|block| block.instructions.iter())
                .any(|inst| matches!(inst, MirInst::Unsupported { .. })),
            "escaping capturing factory value should stay on compiled path"
        );
    }

    #[test]
    fn lower_hir_module_inlines_direct_lambda_call() {
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "main".to_string(),
                params: vec![],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Lambda {
                                params: vec![kea_hir::HirParam {
                                    name: Some("x".to_string()),
                                    span: kea_ast::Span::synthetic(),
                                }],
                                body: Box::new(HirExpr {
                                    kind: HirExprKind::Binary {
                                        op: BinOp::Add,
                                        left: Box::new(HirExpr {
                                            kind: HirExprKind::Var("x".to_string()),
                                            ty: Type::Int,
                                            span: kea_ast::Span::synthetic(),
                                        }),
                                        right: Box::new(HirExpr {
                                            kind: HirExprKind::Lit(kea_ast::Lit::Int(1)),
                                            ty: Type::Int,
                                            span: kea_ast::Span::synthetic(),
                                        }),
                                    },
                                    ty: Type::Int,
                                    span: kea_ast::Span::synthetic(),
                                }),
                            },
                            ty: Type::Function(FunctionType::pure(vec![Type::Int], Type::Int)),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(41)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(vec![], Type::Int)),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::Call { .. })),
            "direct lambda call should inline without emitting a call instruction"
        );
        assert!(
            function.blocks[0].instructions.iter().any(|inst| matches!(
                inst,
                MirInst::Binary {
                    op: MirBinaryOp::Add,
                    ..
                }
            )),
            "inlined direct lambda body should produce add instruction"
        );
    }

    #[test]
    fn lower_hir_module_marks_failful_param_callee_with_fail_result_abi() {
        let fn_ty = Type::Function(FunctionType::with_effects(
            vec![Type::Int],
            Type::Int,
            EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
        ));
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "apply_fail".to_string(),
                params: vec![
                    kea_hir::HirParam {
                        name: Some("f".to_string()),
                        span: kea_ast::Span::synthetic(),
                    },
                    kea_hir::HirParam {
                        name: Some("x".to_string()),
                        span: kea_ast::Span::synthetic(),
                    },
                ],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("f".to_string()),
                            ty: fn_ty.clone(),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Var("x".to_string()),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![fn_ty.clone(), Type::Int],
                    Type::Int,
                    EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(matches!(
            &function.blocks[0].instructions[0],
            MirInst::Call {
                callee: MirCallee::Value(MirValueId(0)),
                callee_fail_result_abi: true,
                ..
            }
        ));
    }

    #[test]
    fn lower_hir_module_marks_failful_param_callee_when_var_expr_type_is_dynamic() {
        let fn_ty = Type::Function(FunctionType::with_effects(
            vec![Type::Int],
            Type::Int,
            EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
        ));
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
                name: "apply_fail".to_string(),
                params: vec![
                    kea_hir::HirParam {
                        name: Some("f".to_string()),
                        span: kea_ast::Span::synthetic(),
                    },
                    kea_hir::HirParam {
                        name: Some("x".to_string()),
                        span: kea_ast::Span::synthetic(),
                    },
                ],
                body: HirExpr {
                    kind: HirExprKind::Call {
                        func: Box::new(HirExpr {
                            kind: HirExprKind::Var("f".to_string()),
                            ty: Type::Dynamic,
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Var("x".to_string()),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Int,
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::with_effects(
                    vec![fn_ty.clone(), Type::Int],
                    Type::Int,
                    EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                )),
                effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                span: kea_ast::Span::synthetic(),
                is_fip: false,
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(matches!(
            &function.blocks[0].instructions[0],
            MirInst::Call {
                callee: MirCallee::Value(MirValueId(0)),
                callee_fail_result_abi: true,
                ..
            }
        ));
    }

    #[test]
    fn lower_hir_module_lowers_catch_call_to_capture_fail_result_call() {
        let fail_fn_ty = Type::Function(FunctionType::with_effects(
            vec![],
            Type::Int,
            EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
        ));
        let result_ty = Type::Sum(kea_types::SumType {
            name: "Result".to_string(),
            type_args: vec![Type::Int, Type::Int],
        });
        let hir = HirModule {
            declarations: vec![
                HirDecl::Function(HirFunction {
                    name: "f".to_string(),
                    params: vec![],
                    body: HirExpr {
                        kind: HirExprKind::Lit(kea_ast::Lit::Int(0)),
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: fail_fn_ty.clone(),
                    effects: EffectRow::closed(vec![(Label::new("Fail"), Type::Int)]),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
                HirDecl::Function(HirFunction {
                    name: "main".to_string(),
                    params: vec![],
                    body: HirExpr {
                        kind: HirExprKind::Catch {
                            expr: Box::new(HirExpr {
                                kind: HirExprKind::Call {
                                    func: Box::new(HirExpr {
                                        kind: HirExprKind::Var("f".to_string()),
                                        ty: fail_fn_ty,
                                        span: kea_ast::Span::synthetic(),
                                    }),
                                    args: vec![],
                                },
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            }),
                        },
                        ty: result_ty.clone(),
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(vec![], result_ty)),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
            ],
        };

        let mir = lower_hir_module(&hir);
        let main = mir
            .functions
            .iter()
            .find(|function| function.name == "main")
            .expect("expected lowered main function");
        assert!(matches!(
            main.blocks[0].instructions.first(),
            Some(MirInst::Call {
                callee: MirCallee::Local(name),
                callee_fail_result_abi: true,
                capture_fail_result: true,
                ..
            }) if name == "f"
        ));
    }

    #[test]
    fn lower_hir_module_lowers_top_level_function_reference_value() {
        let fn_ty = Type::Function(FunctionType::pure(vec![Type::Int], Type::Int));
        let hir = HirModule {
            declarations: vec![
                HirDecl::Function(HirFunction {
                    name: "inc".to_string(),
                    params: vec![kea_hir::HirParam {
                        name: Some("n".to_string()),
                        span: kea_ast::Span::synthetic(),
                    }],
                    body: HirExpr {
                        kind: HirExprKind::Var("n".to_string()),
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(vec![Type::Int], Type::Int)),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
                HirDecl::Function(HirFunction {
                    name: "apply".to_string(),
                    params: vec![
                        kea_hir::HirParam {
                            name: Some("f".to_string()),
                            span: kea_ast::Span::synthetic(),
                        },
                        kea_hir::HirParam {
                            name: Some("x".to_string()),
                            span: kea_ast::Span::synthetic(),
                        },
                    ],
                    body: HirExpr {
                        kind: HirExprKind::Call {
                            func: Box::new(HirExpr {
                                kind: HirExprKind::Var("f".to_string()),
                                ty: fn_ty.clone(),
                                span: kea_ast::Span::synthetic(),
                            }),
                            args: vec![HirExpr {
                                kind: HirExprKind::Var("x".to_string()),
                                ty: Type::Int,
                                span: kea_ast::Span::synthetic(),
                            }],
                        },
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(
                        vec![fn_ty.clone(), Type::Int],
                        Type::Int,
                    )),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
                HirDecl::Function(HirFunction {
                    name: "caller".to_string(),
                    params: vec![kea_hir::HirParam {
                        name: Some("y".to_string()),
                        span: kea_ast::Span::synthetic(),
                    }],
                    body: HirExpr {
                        kind: HirExprKind::Call {
                            func: Box::new(HirExpr {
                                kind: HirExprKind::Var("apply".to_string()),
                                ty: Type::Function(FunctionType::pure(
                                    vec![fn_ty.clone(), Type::Int],
                                    Type::Int,
                                )),
                                span: kea_ast::Span::synthetic(),
                            }),
                            args: vec![
                                HirExpr {
                                    kind: HirExprKind::Var("inc".to_string()),
                                    ty: fn_ty.clone(),
                                    span: kea_ast::Span::synthetic(),
                                },
                                HirExpr {
                                    kind: HirExprKind::Var("y".to_string()),
                                    ty: Type::Int,
                                    span: kea_ast::Span::synthetic(),
                                },
                            ],
                        },
                        ty: Type::Int,
                        span: kea_ast::Span::synthetic(),
                    },
                    ty: Type::Function(FunctionType::pure(vec![Type::Int], Type::Int)),
                    effects: EffectRow::pure(),
                    span: kea_ast::Span::synthetic(),
                    is_fip: false,
                }),
            ],
        };

        let mir = lower_hir_module(&hir);
        let caller = mir
            .functions
            .iter()
            .find(|function| function.name == "caller")
            .expect("caller function");
        assert!(matches!(
            caller.blocks[0]
                .instructions
                .iter()
                .find(|inst| matches!(inst, MirInst::ClosureInit { .. })),
            Some(MirInst::ClosureInit { .. })
        ));
        assert!(matches!(
            caller.blocks[0]
                .instructions
                .iter()
                .find(|inst| matches!(inst, MirInst::Call { callee: MirCallee::Local(_), .. })),
            Some(MirInst::Call {
                callee: MirCallee::Local(name),
                ..
            }) if name == "apply"
        ));
    }

    // -----------------------------------------------------------------------
    // insert_retains_for_reused_call_args — direct MirFunction tests
    // -----------------------------------------------------------------------

    fn make_record_layout(name: &str, is_unboxed: bool) -> MirRecordLayout {
        MirRecordLayout {
            name: name.to_string(),
            is_unboxed,
            fields: vec![MirRecordFieldLayout {
                name: "name".to_string(),
                annotation: kea_ast::TypeAnnotation::Named("String".to_string()),
            }],
        }
    }

    fn make_layouts_with_record(name: &str) -> MirLayoutCatalog {
        MirLayoutCatalog {
            records: vec![make_record_layout(name, false)],
            sums: vec![],
        }
    }

    fn user_record_type() -> Type {
        Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
        })
    }

    /// When a heap value is passed to a call AND used after the call (in a later
    /// instruction), a Retain must be inserted just before the call.
    #[test]
    fn insert_retains_adds_retain_before_call_when_value_reused_after() {
        // Block 0: Call(callee, [v0]) → v1; RecordFieldLoad(v0) → v2; Return(v2)
        // v0 is passed to the call and then also used after → Retain(v0) needed.
        let layouts = make_layouts_with_record("User");
        let v0 = MirValueId(0);
        let v1 = MirValueId(1);
        let v2 = MirValueId(2);
        let mut function = MirFunction {
            name: "test".to_string(),
            signature: MirFunctionSignature {
                params: vec![user_record_type()],
                ret: Type::Int,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![
                    MirInst::Call {
                        callee: MirCallee::Local("consume_user".to_string()),
                        args: vec![v0.clone()],
                        arg_types: vec![user_record_type()],
                        result: Some(v1.clone()),
                        ret_type: Type::Int,
                        callee_fail_result_abi: false,
                        capture_fail_result: false,
                        cc_manifest_id: String::new(),
                    },
                    MirInst::RecordFieldLoad {
                        dest: v2.clone(),
                        record: v0.clone(),
                        record_type: "User".to_string(),
                        field: "name".to_string(),
                        field_ty: Type::String,
                    },
                ],
                terminator: MirTerminator::Return { value: Some(v2.clone()) },
            }],
        };
        insert_retains_for_reused_call_args(&mut function, &layouts);
        // Retain(v0) should appear before the Call.
        let insts = &function.blocks[0].instructions;
        assert!(
            insts.iter().position(|i| matches!(i, MirInst::Retain { value } if value == &v0))
                < insts.iter().position(|i| matches!(i, MirInst::Call { .. })),
            "Retain(v0) must appear before the Call"
        );
    }

    /// When a heap value is passed to a call but NOT used after, no Retain is needed.
    #[test]
    fn insert_retains_does_not_add_retain_when_value_not_reused() {
        let layouts = make_layouts_with_record("User");
        let v0 = MirValueId(0);
        let v1 = MirValueId(1);
        let mut function = MirFunction {
            name: "test".to_string(),
            signature: MirFunctionSignature {
                params: vec![user_record_type()],
                ret: Type::Int,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![MirInst::Call {
                    callee: MirCallee::Local("consume_user".to_string()),
                    args: vec![v0.clone()],
                    arg_types: vec![user_record_type()],
                    result: Some(v1.clone()),
                    ret_type: Type::Int,
                    callee_fail_result_abi: false,
                    capture_fail_result: false,
                    cc_manifest_id: String::new(),
                }],
                terminator: MirTerminator::Return { value: Some(v1.clone()) },
            }],
        };
        insert_retains_for_reused_call_args(&mut function, &layouts);
        let has_retain = function.blocks[0]
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::Retain { .. }));
        assert!(!has_retain, "no Retain when value is not reused after the call");
    }

    // -----------------------------------------------------------------------
    // insert_releases_for_dead_params — direct MirFunction tests
    // -----------------------------------------------------------------------

    /// Case 2 fires for a heap record param used in a single block that has no successors.
    /// The Release should appear AFTER the last use of the param.
    #[test]
    fn insert_releases_case2_fires_for_single_block_record_param() {
        let layouts = make_layouts_with_record("User");
        let v0 = MirValueId(0); // User param
        let v1 = MirValueId(1); // field load result
        let mut function = MirFunction {
            name: "get_name".to_string(),
            signature: MirFunctionSignature {
                params: vec![user_record_type()],
                ret: Type::String,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![MirInst::RecordFieldLoad {
                    dest: v1.clone(),
                    record: v0.clone(),
                    record_type: "User".to_string(),
                    field: "name".to_string(),
                    field_ty: Type::String,
                }],
                terminator: MirTerminator::Return { value: Some(v1.clone()) },
            }],
        };
        insert_releases_for_dead_params(&mut function, &layouts);
        let insts = &function.blocks[0].instructions;
        assert_eq!(insts.len(), 2, "Release should be appended after RecordFieldLoad");
        assert!(
            matches!(&insts[1], MirInst::Release { value } if value == &v0),
            "second instruction must be Release(v0)"
        );
    }

    /// Case 1 fires for a branch target block where the param is dead (neither branch uses it).
    /// Release is inserted at the head of the dead block.
    #[test]
    fn insert_releases_case1_fires_for_dead_branch_block() {
        let layouts = make_layouts_with_record("User");
        let v0 = MirValueId(0); // User param
        let v1 = MirValueId(1); // some Int (cond)
        // Block 0: Branch(v1, then: b1, else: b2)
        // b1: uses v0 via RecordFieldLoad → Return
        // b2: no use of v0 → Return 0  ← Case 1 release here
        let mut function = MirFunction {
            name: "maybe_get_name".to_string(),
            signature: MirFunctionSignature {
                params: vec![user_record_type(), Type::Bool],
                ret: Type::String,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Branch {
                        condition: v1.clone(),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::RecordFieldLoad {
                        dest: MirValueId(2),
                        record: v0.clone(),
                        record_type: "User".to_string(),
                        field: "name".to_string(),
                        field_ty: Type::String,
                    }],
                    terminator: MirTerminator::Return { value: Some(MirValueId(2)) },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return { value: None },
                },
            ],
        };
        insert_releases_for_dead_params(&mut function, &layouts);
        let b2 = &function.blocks[2];
        let has_release_in_b2 = b2
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::Release { value } if value == &v0));
        assert!(has_release_in_b2, "Case 1: Release(v0) must appear in the dead branch block b2");
        // b1 must NOT have a Release (the param is used there via RecordFieldLoad).
        let b1 = &function.blocks[1];
        let has_release_in_b1 = b1
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::Release { value } if value == &v0));
        // b1 IS live (uses v0). Case 2 would fire for b1 only if its last read is NOT
        // a managed-payload SumPayloadLoad. For RecordFieldLoad, Case 2 CAN fire.
        // (b1 has no dead successors, so let's just verify Case 1 didn't fire for it.)
        let _ = has_release_in_b1; // explicitly not asserting — b1 may get Case 2 release
    }

    /// A param consumed by a Call (ownership transferred) must NOT also get a Release.
    #[test]
    fn insert_releases_does_not_add_release_when_param_consumed_by_call() {
        let layouts = make_layouts_with_record("User");
        let v0 = MirValueId(0);
        let v1 = MirValueId(1);
        let mut function = MirFunction {
            name: "forward_user".to_string(),
            signature: MirFunctionSignature {
                params: vec![user_record_type()],
                ret: Type::Int,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![MirInst::Call {
                    callee: MirCallee::Local("consume_user".to_string()),
                    args: vec![v0.clone()],
                    arg_types: vec![user_record_type()],
                    result: Some(v1.clone()),
                    ret_type: Type::Int,
                    callee_fail_result_abi: false,
                    capture_fail_result: false,
                    cc_manifest_id: String::new(),
                }],
                terminator: MirTerminator::Return { value: Some(v1.clone()) },
            }],
        };
        insert_releases_for_dead_params(&mut function, &layouts);
        let has_release = function.blocks[0]
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::Release { value } if value == &v0));
        assert!(!has_release, "param consumed by Call must not get a Release (ownership transferred)");
    }

    /// Sum-typed param: Case 2 fires when all fields are primitive (not Dynamic/managed).
    /// This is tested via HIR lowering (see `lower_hir_module_lowers_sum_payload_access_expression`).
    /// This test verifies the same via a direct MirFunction with field_ty=Int.
    #[test]
    fn insert_releases_case2_fires_for_sum_param_with_primitive_payload() {
        // Option Int: SumPayloadLoad(v0, "Some", 0, Int) → v1; Return v1
        let layouts = MirLayoutCatalog {
            records: vec![],
            sums: vec![], // Option is seeded by lower_hir_module, but here we go direct
        };
        let v0 = MirValueId(0);
        let v1 = MirValueId(1);
        let option_int_ty = Type::Sum(kea_types::SumType {
            name: "Option".to_string(),
            type_args: vec![Type::Int],
        });
        let mut function = MirFunction {
            name: "unwrap_option_int".to_string(),
            signature: MirFunctionSignature {
                params: vec![option_int_ty],
                ret: Type::Int,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![MirInst::SumPayloadLoad {
                    dest: v1.clone(),
                    sum: v0.clone(),
                    sum_type: "Option".to_string(),
                    variant: "Some".to_string(),
                    field_index: 0,
                    field_ty: Type::Int,
                }],
                terminator: MirTerminator::Return { value: Some(v1.clone()) },
            }],
        };
        insert_releases_for_dead_params(&mut function, &layouts);
        let has_release = function.blocks[0]
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::Release { value } if value == &v0));
        assert!(has_release, "sum param with primitive payload should get a Case 2 Release");
    }

    /// Sum-typed param: Case 2 must NOT fire when payload field_ty is Dynamic.
    #[test]
    fn insert_releases_case2_does_not_fire_for_sum_param_with_dynamic_payload() {
        let layouts = MirLayoutCatalog { records: vec![], sums: vec![] };
        let v0 = MirValueId(0);
        let v1 = MirValueId(1);
        let list_ty = Type::Sum(kea_types::SumType {
            name: "List".to_string(),
            type_args: vec![Type::Dynamic],
        });
        let mut function = MirFunction {
            name: "head_list".to_string(),
            signature: MirFunctionSignature {
                params: vec![list_ty.clone()],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![MirBlock {
                id: MirBlockId(0),
                params: vec![],
                instructions: vec![MirInst::SumPayloadLoad {
                    dest: v1.clone(),
                    sum: v0.clone(),
                    sum_type: "List".to_string(),
                    variant: "Cons".to_string(),
                    field_index: 0,
                    field_ty: Type::Dynamic, // ← Dynamic → must NOT release v0
                }],
                terminator: MirTerminator::Return { value: Some(v1.clone()) },
            }],
        };
        insert_releases_for_dead_params(&mut function, &layouts);
        let has_release = function.blocks[0]
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::Release { value } if value == &v0));
        assert!(
            !has_release,
            "sum param with Dynamic payload must NOT get a Release \
             (would double-free extracted child)"
        );
    }

    /// Sum-typed param: Case 1 must NOT fire even when there is a dead branch.
    #[test]
    fn insert_releases_case1_does_not_fire_for_sum_param() {
        let layouts = MirLayoutCatalog { records: vec![], sums: vec![] };
        let v0 = MirValueId(0);
        let v1 = MirValueId(1); // Bool cond
        let list_ty = Type::Sum(kea_types::SumType {
            name: "List".to_string(),
            type_args: vec![Type::Dynamic],
        });
        // b0: Branch(v1, b1, b2)
        // b1: SumPayloadLoad(v0, Cons, 0, Dynamic) → v2; Return v2
        // b2: Nop; Return None  ← dead for v0, but Case 1 must NOT fire (sum param)
        let mut function = MirFunction {
            name: "maybe_head".to_string(),
            signature: MirFunctionSignature {
                params: vec![list_ty, Type::Bool],
                ret: Type::Dynamic,
                effects: EffectRow::pure(),
            },
            entry: MirBlockId(0),
            is_fip: false,
            blocks: vec![
                MirBlock {
                    id: MirBlockId(0),
                    params: vec![],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Branch {
                        condition: v1.clone(),
                        then_block: MirBlockId(1),
                        else_block: MirBlockId(2),
                    },
                },
                MirBlock {
                    id: MirBlockId(1),
                    params: vec![],
                    instructions: vec![MirInst::SumPayloadLoad {
                        dest: MirValueId(2),
                        sum: v0.clone(),
                        sum_type: "List".to_string(),
                        variant: "Cons".to_string(),
                        field_index: 0,
                        field_ty: Type::Dynamic,
                    }],
                    terminator: MirTerminator::Return { value: Some(MirValueId(2)) },
                },
                MirBlock {
                    id: MirBlockId(2),
                    params: vec![],
                    instructions: vec![MirInst::Nop],
                    terminator: MirTerminator::Return { value: None },
                },
            ],
        };
        insert_releases_for_dead_params(&mut function, &layouts);
        let b2_has_release = function.blocks[2]
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::Release { value } if value == &v0));
        assert!(
            !b2_has_release,
            "Case 1 must NOT fire for sum-typed params \
             (releasing at dead-branch boundary is unsafe without Perceus RC=1 check)"
        );
    }
}

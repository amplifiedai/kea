//! Backend-neutral mid-level IR (MIR) for Kea.
//!
//! This crate defines explicit control-flow + memory/effect operations that are
//! independent of any specific backend API (Cranelift, LLVM, etc.).

use std::collections::{BTreeMap, BTreeSet};

use kea_ast::{BinOp, DeclKind, ExprKind as AstExprKind, TypeAnnotation, UnaryOp};
use kea_hir::{HirDecl, HirExpr, HirExprKind, HirFunction, HirHandleClause, HirModule, HirPattern};
use kea_types::{EffectRow, FunctionType, SumType, Type};

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
    SumInit {
        dest: MirValueId,
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
                | MirInst::SumInit { .. }
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
    let known_functions = module
        .declarations
        .iter()
        .filter_map(|decl| match decl {
            HirDecl::Function(function) => Some(function.name.clone()),
            HirDecl::Raw(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let known_function_types = module
        .declarations
        .iter()
        .filter_map(|decl| match decl {
            HirDecl::Function(function) => Some((function.name.clone(), function.ty.clone())),
            HirDecl::Raw(_) => None,
        })
        .collect::<BTreeMap<_, _>>();
    let intrinsic_symbols = collect_intrinsic_symbols(module);
    let effect_operations = collect_effect_operations(module);
    let known_function_dispatch_effects =
        collect_function_dispatch_effects(module, &effect_operations);
    let lambda_factories = collect_lambda_factory_templates(module, &known_functions);
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
            functions.extend(lower_hir_function(
                function,
                &layouts,
                &known_functions,
                &known_function_types,
                &intrinsic_symbols,
                &effect_operations,
                &known_function_dispatch_effects,
                &lambda_factories,
            ));
        }
    }
    for function in &mut functions {
        schedule_trailing_releases_after_last_use(function);
    }

    MirModule { functions, layouts }
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
        | MirInst::SumInit { dest, .. }
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
        MirInst::SumInit { fields, .. } => fields.iter().any(|field| field == value),
        MirInst::SumTagLoad { sum, .. } => sum == value,
        MirInst::SumPayloadLoad { sum, .. } => sum == value,
        MirInst::RecordFieldLoad { record, .. } => record == value,
        MirInst::ClosureInit {
            entry, captures, ..
        } => entry == value || captures.iter().any(|capture| capture == value),
        MirInst::ClosureCaptureLoad { closure, .. } => closure == value,
        MirInst::StateCellNew { initial, .. } => initial == value,
        MirInst::StateCellLoad { cell, .. } => cell == value,
        MirInst::StateCellStore { cell, value: stored } => cell == value || stored == value,
        MirInst::Retain { value: retained } | MirInst::Release { value: retained } => retained == value,
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
            MirCallee::Value(callee_value) => callee_value == value || args.iter().any(|arg| arg == value),
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

fn is_direct_capability_effect(effect: &str) -> bool {
    DIRECT_CAPABILITIES
        .iter()
        .any(|capability| capability.effect == effect)
}

#[derive(Debug, Clone)]
struct EffectOperationInfo {
    effect: String,
    operation: String,
    arity: usize,
    returns_unit: bool,
}

fn is_unit_type_annotation(annotation: &TypeAnnotation) -> bool {
    matches!(annotation, TypeAnnotation::Named(name) if name == "Unit")
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
            };
            operations.insert(format!("{effect}.{operation}"), info.clone());
            operations.insert(format!("{module_path}.{operation}"), info);
        }
    }
    operations
}

fn handler_cell_lowering_for_operation(op: &EffectOperationInfo) -> Option<HandlerCellOpLowering> {
    match (op.arity, op.returns_unit) {
        (0, _) => Some(HandlerCellOpLowering::LoadCell),
        (1, true) => Some(HandlerCellOpLowering::StoreArgAndReturnUnit),
        _ => None,
    }
}

fn handler_plan_for_effect(
    effect_operations: &BTreeMap<String, EffectOperationInfo>,
    effect: &str,
) -> Option<ActiveEffectHandlerPlan> {
    let mut operation_lowering = BTreeMap::new();
    for op in effect_operations.values().filter(|op| op.effect == effect) {
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
        let effects = ft
            .effects
            .row
            .fields
            .iter()
            .map(|(label, _)| label.as_str().to_string())
            .filter(|effect| dispatchable_effects.contains(effect))
            .filter(|effect| effect != "Fail")
            .filter(|effect| !is_direct_capability_effect(effect))
            .collect::<Vec<_>>();
        if !effects.is_empty() {
            mapping.insert(function.name.clone(), effects);
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
                && !matches!(ft.ret.as_ref(), Type::Result(_, _))
        }
        _ => false,
    }
}

fn collect_layout_metadata(raw_decl: &DeclKind, layouts: &mut MirLayoutCatalog) {
    match raw_decl {
        DeclKind::RecordDef(record) => layouts.records.push(MirRecordLayout {
            name: record.name.node.clone(),
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
        layouts.sums.push(MirSumLayout {
            name: "Option".to_string(),
            variants: vec![
                MirVariantLayout {
                    name: "Some".to_string(),
                    tag: 0,
                    fields: vec![MirVariantFieldLayout {
                        name: None,
                        annotation: kea_ast::TypeAnnotation::Named("Dynamic".to_string()),
                    }],
                },
                MirVariantLayout {
                    name: "None".to_string(),
                    tag: 1,
                    fields: vec![],
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
        HirExprKind::SumConstructor { fields, .. } | HirExprKind::Tuple(fields) => {
            for field_expr in fields {
                collect_anon_record_layouts_from_expr(field_expr, layouts, known);
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

#[allow(clippy::too_many_arguments)]
fn lower_hir_function(
    function: &HirFunction,
    layouts: &MirLayoutCatalog,
    known_functions: &BTreeSet<String>,
    known_function_types: &BTreeMap<String, Type>,
    intrinsic_symbols: &BTreeMap<String, String>,
    effect_operations: &BTreeMap<String, EffectOperationInfo>,
    known_function_dispatch_effects: &BTreeMap<String, Vec<String>>,
    lambda_factories: &BTreeMap<String, LambdaFactoryTemplate>,
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
                    _ => {}
                }
            }
        }
        if let Some(param_ty) = declared_params.get(index)
            && let Some(sum_type) = ctx.infer_sum_type_from_type(param_ty)
        {
            ctx.sum_value_types.insert(MirValueId(index as u32), sum_type);
        }
    }
    let return_value = ctx.lower_expr(&function.body);
    let lifted_functions = ctx.lifted_functions.clone();
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
    intrinsic_symbols: BTreeMap<String, String>,
    effect_operations: BTreeMap<String, EffectOperationInfo>,
    known_function_dispatch_effects: BTreeMap<String, Vec<String>>,
    active_effect_cells: BTreeMap<String, MirValueId>,
    active_effect_handlers: BTreeMap<String, ActiveEffectHandlerPlan>,
    lambda_factories: BTreeMap<String, LambdaFactoryTemplate>,
    var_record_types: BTreeMap<String, String>,
    record_value_types: BTreeMap<MirValueId, String>,
    sum_value_types: BTreeMap<MirValueId, String>,
    sum_ctor_candidates: BTreeMap<String, Vec<SumCtorCandidate>>,
    lifted_functions: Vec<MirFunction>,
    named_function_closure_entries: BTreeMap<String, String>,
    next_lifted_lambda_id: u32,
    next_closure_entry_id: u32,
    next_value_id: u32,
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
    LoadCell,
    StoreArgAndReturnUnit,
}

#[derive(Debug, Clone, Default)]
struct ActiveEffectHandlerPlan {
    operation_lowering: BTreeMap<String, HandlerCellOpLowering>,
}

#[derive(Debug, Clone)]
struct VarScope {
    vars: BTreeMap<String, MirValueId>,
    var_types: BTreeMap<String, Type>,
    local_lambdas: BTreeMap<String, LocalLambda>,
    var_record_types: BTreeMap<String, String>,
    active_effect_cells: BTreeMap<String, MirValueId>,
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
        for (idx, effect) in hidden_dispatch_effects.iter().enumerate() {
            active_effect_cells.insert(effect.clone(), MirValueId((param_count + idx) as u32));
            if let Some(plan) = handler_plan_for_effect(effect_operations, effect) {
                active_effect_handlers.insert(effect.clone(), plan);
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
            intrinsic_symbols: intrinsic_symbols.clone(),
            effect_operations: effect_operations.clone(),
            known_function_dispatch_effects: known_function_dispatch_effects.clone(),
            active_effect_cells,
            active_effect_handlers,
            lambda_factories: lambda_factories.clone(),
            var_record_types: BTreeMap::new(),
            record_value_types: BTreeMap::new(),
            sum_value_types: BTreeMap::new(),
            sum_ctor_candidates,
            lifted_functions: Vec::new(),
            named_function_closure_entries: BTreeMap::new(),
            next_lifted_lambda_id: 0,
            next_closure_entry_id: 0,
            next_value_id: (param_count + hidden_dispatch_effects.len()) as u32,
        }
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

    #[allow(clippy::too_many_arguments)]
    fn build_closure_entry_wrapper(
        &self,
        entry_name: String,
        target_name: String,
        capture_types: Vec<Type>,
        call_param_types: Vec<Type>,
        return_type: Type,
        effects: EffectRow,
        callee_fail_result_abi: bool,
    ) -> MirFunction {
        let mut instructions = Vec::new();
        let mut next_value_id = 1 + call_param_types.len() as u32;
        let closure_value = MirValueId(0);

        let mut call_args = Vec::new();
        let mut call_arg_types = Vec::new();

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

        for (idx, param_ty) in call_param_types.iter().enumerate() {
            call_args.push(MirValueId(1 + idx as u32));
            call_arg_types.push(param_ty.clone());
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
                .collect(),
            ret: return_type,
            effects,
        };

        MirFunction {
            name: entry_name,
            signature: wrapper_signature,
            entry: MirBlockId(0),
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
        let Type::Function(ft) = self.known_function_types.get(name)?.clone() else {
            let dest = self.new_value();
            self.emit_inst(MirInst::FunctionRef {
                dest: dest.clone(),
                function: name.to_string(),
            });
            return Some(dest);
        };

        let entry_name = if let Some(existing) = self.named_function_closure_entries.get(name) {
            existing.clone()
        } else {
            let entry_name = self.allocate_generated_closure_entry_name("named");
            let callee_fail_result_abi =
                uses_fail_result_abi_from_type(&Type::Function(ft.clone()));
            let wrapper = self.build_closure_entry_wrapper(
                entry_name.clone(),
                name.to_string(),
                Vec::new(),
                ft.params.clone(),
                ft.ret.as_ref().clone(),
                ft.effects.clone(),
                callee_fail_result_abi,
            );
            self.register_generated_function(wrapper);
            self.named_function_closure_entries
                .insert(name.to_string(), entry_name.clone());
            entry_name
        };

        self.emit_closure_value(entry_name, Vec::new())
    }

    fn lower_lambda_to_closure_value(
        &mut self,
        expr: &HirExpr,
        params: &[kea_hir::HirParam],
        body: &HirExpr,
        expected_ty: Option<&Type>,
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
        };
        let mut known = self.known_functions.clone();
        known.insert(lambda_name.clone());
        let mut known_types = self.known_function_types.clone();
        known_types.insert(lambda_name.clone(), lifted.ty.clone());
        let lowered_functions = lower_hir_function(
            &lifted,
            &self.layouts,
            &known,
            &known_types,
            &self.intrinsic_symbols,
            &self.effect_operations,
            &self.known_function_dispatch_effects,
            &self.lambda_factories,
        );
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
            resolved_fn_ty.ret.as_ref().clone(),
            resolved_fn_ty.effects.clone(),
            callee_fail_result_abi,
        );
        self.register_generated_function(wrapper);

        self.emit_closure_value(
            entry_name,
            captures
                .into_iter()
                .map(|(_, ty, value)| (value, ty))
                .collect(),
        )
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
                None
            }
            HirExprKind::Binary { op, left, right } => {
                if expr.ty == Type::Bool && matches!(op, BinOp::And | BinOp::Or) {
                    return self.lower_short_circuit_binary(*op, left, right);
                }
                let left_value = self.lower_expr(left)?;
                let right_value = self.lower_expr(right)?;
                let left_value = self.lower_maybe_sum_tag_operand(*op, left, left_value, right);
                let right_value = self.lower_maybe_sum_tag_operand(*op, right, right_value, left);
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
                self.emit_inst(MirInst::Retain {
                    value: target.clone(),
                });
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

                let dest = self.new_value();
                let block_id = self.current_block.clone();
                self.emit_inst(MirInst::CowUpdate {
                    dest: dest.clone(),
                    target: frozen,
                    record_type: record_type.clone(),
                    updates,
                    unique_path: block_id.clone(),
                    copy_path: block_id,
                });
                self.emit_inst(MirInst::Release { value: target });
                self.record_value_types
                    .insert(dest.clone(), record_type.clone());
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
                    _ => match &base.kind {
                        HirExprKind::Var(name) => self.var_record_types.get(name).cloned(),
                        HirExprKind::Call { func, .. } => self.infer_record_type_from_call(func),
                        _ => self.record_value_types.get(&record).cloned(),
                    },
                }?;
                let dest = self.new_value();
                self.emit_inst(MirInst::RecordFieldLoad {
                    dest: dest.clone(),
                    record,
                    record_type,
                    field: field.clone(),
                    field_ty: expr.ty.clone(),
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
                let dest = self.new_value();
                self.emit_inst(MirInst::SumPayloadLoad {
                    dest: dest.clone(),
                    sum,
                    sum_type: sum_type.clone(),
                    variant: variant.clone(),
                    field_index: *field_index,
                    field_ty: expr.ty.clone(),
                });
                if let Some(inner_sum_type) = self.infer_sum_type_from_type(&expr.ty) {
                    self.sum_value_types.insert(dest.clone(), inner_sum_type);
                }
                Some(dest)
            }
            HirExprKind::Call { func, args } => self.lower_call_expr(expr, func, args, false),
            HirExprKind::Catch { expr: caught } => {
                let HirExprKind::Call { func, args } = &caught.kind else {
                    return None;
                };
                let result = self.lower_call_expr(caught, func, args, true)?;
                self.sum_value_types
                    .insert(result.clone(), "Result".to_string());
                Some(result)
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
                if let (HirPattern::Var(_), HirExprKind::Var(source_name)) = (pattern, &value.kind)
                    && self.vars.contains_key(source_name)
                    && is_heap_managed_type(&value.ty)
                {
                    self.emit_inst(MirInst::Retain {
                        value: value_id.clone(),
                    });
                }
                self.bind_pattern(pattern, value_id.clone(), &value.ty);
                Some(value_id)
            }
            HirExprKind::Block(exprs) => {
                let incoming_scope = self.snapshot_var_scope();
                let mut last = None;
                for expr in exprs {
                    last = self.lower_expr(expr);
                    if self.current_block().terminator.is_some() {
                        break;
                    }
                }
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
                        let Some(ty) = self.var_types.get(name) else {
                            continue;
                        };
                        if !is_heap_managed_type(ty) {
                            continue;
                        }
                        if last.as_ref().is_some_and(|result_id| result_id == value_id) {
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
                self.lower_lambda_to_closure_value(expr, params, body, None)
            }
            HirExprKind::Tuple(_) | HirExprKind::Raw(_) => match &expr.kind {
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
        let mut initial_expr: Option<&HirExpr> = None;
        for clause in clauses
            .iter()
            .filter(|clause| clause.effect == target_effect)
        {
            let resume_value = match &clause.body.kind {
                HirExprKind::Resume { value } => value.as_ref(),
                _ => {
                    self.emit_inst(MirInst::Unsupported {
                        detail: format!(
                            "handler clause `{target_effect}.{} {}`",
                            clause.operation,
                            "must be tail-resumptive (`resume ...`) for compiled lowering"
                        ),
                    });
                    return None;
                }
            };

            if plan.operation_lowering.contains_key(&clause.operation) {
                self.emit_inst(MirInst::Unsupported {
                    detail: format!(
                        "duplicate handler clause for `{target_effect}.{}` is not supported",
                        clause.operation
                    ),
                });
                return None;
            }

            match clause.args.len() {
                0 => {
                    if initial_expr.is_none() {
                        initial_expr = Some(resume_value);
                    }
                    plan.operation_lowering
                        .insert(clause.operation.clone(), HandlerCellOpLowering::LoadCell);
                }
                1 => {
                    if !matches!(resume_value.kind, HirExprKind::Lit(kea_ast::Lit::Unit)) {
                        self.emit_inst(MirInst::Unsupported {
                            detail: format!(
                                "single-argument handler clause `{target_effect}.{} {}`",
                                clause.operation,
                                "must use `resume ()` for compiled lowering"
                            ),
                        });
                        return None;
                    }
                    plan.operation_lowering.insert(
                        clause.operation.clone(),
                        HandlerCellOpLowering::StoreArgAndReturnUnit,
                    );
                }
                arity => {
                    self.emit_inst(MirInst::Unsupported {
                        detail: format!(
                            "handler clause `{target_effect}.{} has unsupported arity {arity}; compiled lowering currently supports arity 0/1",
                            clause.operation
                        ),
                    });
                    return None;
                }
            }
        }
        if plan.operation_lowering.is_empty() {
            self.emit_inst(MirInst::Unsupported {
                detail: format!(
                    "handler lowering received no clauses for effect `{target_effect}`"
                ),
            });
            return None;
        }

        let initial = if let Some(initial_expr) = initial_expr {
            self.lower_expr(initial_expr)?
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
        self.emit_inst(MirInst::HandlerEnter {
            effect: target_effect.clone(),
        });
        let incoming_scope = self.snapshot_var_scope();
        self.active_effect_cells
            .insert(target_effect.clone(), cell.clone());
        self.active_effect_handlers
            .insert(target_effect.clone(), plan);
        let result = self.lower_expr(handled);
        self.restore_var_scope(&incoming_scope);
        self.emit_inst(MirInst::HandlerExit {
            effect: target_effect,
        });
        self.emit_inst(MirInst::Release { value: cell });
        let Some(then_expr) = then_clause else {
            return result;
        };
        if self.current_block().terminator.is_some() {
            return None;
        }

        let handled_value = if let Some(value) = result {
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
                    detail: "handle then-clause lambda must accept exactly one parameter".to_string(),
                });
                return None;
            }
            let incoming_scope = self.snapshot_var_scope();
            if let Some(param_name) = &params[0].name {
                self.vars.insert(param_name.clone(), handled_value);
                self.var_types.insert(param_name.clone(), handled.ty.clone());
            }
            let lowered = self.lower_expr(body);
            self.restore_var_scope(&incoming_scope);
            return lowered;
        }

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
        call_result
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
            let result = self.lower_expr(&template.lambda_body);
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
            let result = self.lower_expr(body);
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
                Type::Function(FunctionType::pure(
                    args.iter().map(|arg| arg.ty.clone()).collect(),
                    if expr.ty == Type::Dynamic {
                        local_lambda.body.ty.clone()
                    } else {
                        expr.ty.clone()
                    },
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
            && name == "Fail.fail"
            && !capture_fail_result
        {
            let mut lowered_args = Vec::with_capacity(args.len());
            for arg in args {
                lowered_args.push(self.lower_expr(arg)?);
            }
            self.emit_inst(MirInst::EffectOp {
                class: MirEffectOpClass::ZeroResume,
                effect: "Fail".to_string(),
                operation: "fail".to_string(),
                args: lowered_args,
                result: None,
            });
            self.set_terminator(MirTerminator::Unreachable);
            return None;
        }
        if let HirExprKind::Var(name) = &func.kind
            && !capture_fail_result
            && let Some(op_info) = self.effect_operations.get(name).cloned()
        {
            let effect = op_info.effect;
            let operation = op_info.operation;
            if let Some(cell) = self.active_effect_cells.get(&effect).cloned() {
                let Some(plan) = self.active_effect_handlers.get(&effect) else {
                    self.emit_inst(MirInst::Unsupported {
                        detail: format!(
                            "missing handler operation plan for effect `{effect}` in call lowering"
                        ),
                    });
                    return None;
                };
                let Some(lowering) = plan.operation_lowering.get(&operation).copied() else {
                    self.emit_inst(MirInst::Unsupported {
                        detail: format!(
                            "missing handler operation plan for `{effect}.{operation}` in call lowering"
                        ),
                    });
                    return None;
                };
                match lowering {
                    HandlerCellOpLowering::LoadCell => {
                        if !args.is_empty() {
                            self.emit_inst(MirInst::Unsupported {
                                detail: format!(
                                    "handled operation `{effect}.{operation}` expected 0 args for load lowering"
                                ),
                            });
                            return None;
                        }
                        if expr.ty == Type::Unit {
                            return None;
                        }
                        let dest = self.new_value();
                        self.emit_inst(MirInst::StateCellLoad {
                            dest: dest.clone(),
                            cell,
                        });
                        return Some(dest);
                    }
                    HandlerCellOpLowering::StoreArgAndReturnUnit => {
                        if args.len() != 1 {
                            self.emit_inst(MirInst::Unsupported {
                                detail: format!(
                                    "handled operation `{effect}.{operation}` expected 1 arg for store lowering"
                                ),
                            });
                            return None;
                        }
                        let value = self.lower_expr(&args[0])?;
                        self.emit_inst(MirInst::StateCellStore { cell, value });
                        return None;
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
                    } else if self.known_function_types.contains_key(name) {
                        MirCallee::Local(name.clone())
                    } else if is_namespaced_symbol_name(name) {
                        MirCallee::External(name.clone())
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
                )?;
                self.restore_var_scope(&incoming_scope);
                arg_types.push(expected.cloned().unwrap_or(synthesized_ty));
                lowered_args.push(value);
                continue;
            }
            if let HirExprKind::Lambda { params, body } = &arg.kind {
                let value =
                    self.lower_lambda_to_closure_value(arg, params, body.as_ref(), expected)?;
                arg_types.push(expected.cloned().unwrap_or_else(|| arg.ty.clone()));
                lowered_args.push(value);
                continue;
            }
            arg_types.push(arg.ty.clone());
            lowered_args.push(self.lower_expr(arg)?);
        }
        for effect in dispatch_effects {
            let Some(cell) = self.active_effect_cells.get(&effect).cloned() else {
                self.emit_inst(MirInst::Unsupported {
                    detail: format!(
                        "missing active handler cell for effect `{effect}` in call lowering"
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

        let result = if call_ret_type == Type::Unit {
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
        result
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
            _ => None,
        }
    }

    fn infer_sum_type_from_type(&self, ty: &Type) -> Option<String> {
        match ty {
            Type::Sum(sum_ty) => Some(sum_ty.name.clone()),
            Type::Option(_) => Some("Option".to_string()),
            Type::Result(_, _) => Some("Result".to_string()),
            _ => None,
        }
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
            AstExprKind::Var(name) => self.vars.get(name).cloned(),
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
        let target_ty = try_from_target_type_from_name(func_name).or_else(|| match &expr.ty {
            Type::Option(inner) => match inner.as_ref() {
                Type::IntN(_, _) => Some((**inner).clone()),
                _ => None,
            },
            _ => None,
        })?;
        let option_ty = Type::Option(Box::new(target_ty.clone()));
        let (min, max) = Self::integer_bounds_for_target(&target_ty)?;

        let source = self.lower_expr(&args[0])?;
        let source_int = match &args[0].ty {
            Type::Int => source.clone(),
            // Some resolved callsites still carry `Dynamic` in HIR even when
            // type checking has already constrained the argument to integer
            // input for `*.try_from(...)`.
            Type::Dynamic => source.clone(),
            Type::IntN(_, kea_types::Signedness::Signed) => {
                let widened = self.new_value();
                self.emit_inst(MirInst::Unary {
                    dest: widened.clone(),
                    op: MirUnaryOp::WidenSignedToInt,
                    operand: source.clone(),
                });
                widened
            }
            Type::IntN(_, kea_types::Signedness::Unsigned) => {
                let widened = self.new_value();
                self.emit_inst(MirInst::Unary {
                    dest: widened.clone(),
                    op: MirUnaryOp::WidenUnsignedToInt,
                    operand: source.clone(),
                });
                widened
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

        self.switch_to(none_block);
        let none_value = self.new_value();
        self.emit_inst(MirInst::Const {
            dest: none_value.clone(),
            literal: MirLiteral::Int(1),
        });
        self.ensure_jump_to(join_block.clone(), vec![none_value]);

        self.switch_to(some_block);
        let some_value = self.new_value();
        self.emit_inst(MirInst::SumInit {
            dest: some_value.clone(),
            sum_type: "Option".to_string(),
            variant: "Some".to_string(),
            tag: 0,
            fields: vec![source_int],
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
                Some(_) => vec![then_value?],
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
                Some(_) => vec![else_value?],
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
        result_value
    }

    fn bind_pattern(&mut self, pattern: &HirPattern, value_id: MirValueId, value_ty: &Type) {
        if let HirPattern::Var(name) = pattern {
            self.vars.insert(name.clone(), value_id.clone());
            self.var_types.insert(name.clone(), value_ty.clone());
            if let Some(record_type) = self.record_value_types.get(&value_id) {
                self.var_record_types
                    .insert(name.clone(), record_type.clone());
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

fn is_heap_managed_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::String
            | Type::Record(_)
            | Type::AnonRecord(_)
            | Type::Result(_, _)
            | Type::Function(_)
            | Type::Opaque { .. }
    ) || matches!(ty, Type::Sum(sum_ty) if sum_uses_pointer_only_runtime_representation(sum_ty))
}

fn sum_uses_pointer_only_runtime_representation(sum_ty: &SumType) -> bool {
    !sum_ty.variants.is_empty() && sum_ty.variants.iter().all(|(_, fields)| !fields.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use kea_ast::{
        Argument, DeclKind, ExprKind, Lit, RecordDef, Spanned, TypeAnnotation, TypeDef,
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
                field_annotations: vec![],
                derives: vec![],
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
                derives: vec![],
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
        assert_eq!(option.variants.len(), 2);
        assert_eq!(option.variants[0].name, "Some");
        assert_eq!(option.variants[0].tag, 0);
        assert_eq!(option.variants[1].name, "None");
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
            variants: vec![
                ("Some".to_string(), vec![Type::Int]),
                ("None".to_string(), vec![]),
            ],
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
            variants: vec![
                ("Just".to_string(), vec![Type::Int]),
                ("Nothing".to_string(), vec![]),
            ],
        });
        let maybe_maybe_ty = Type::Sum(SumType {
            name: "Maybe".to_string(),
            type_args: vec![maybe_int_ty.clone()],
            variants: vec![
                ("Just".to_string(), vec![maybe_int_ty.clone()]),
                ("Nothing".to_string(), vec![]),
            ],
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
                                Type::Option(Box::new(Type::IntN(
                                    kea_types::IntWidth::I8,
                                    kea_types::Signedness::Signed,
                                ))),
                            )),
                            span: kea_ast::Span::synthetic(),
                        }),
                        args: vec![HirExpr {
                            kind: HirExprKind::Lit(kea_ast::Lit::Int(42)),
                            ty: Type::Int,
                            span: kea_ast::Span::synthetic(),
                        }],
                    },
                    ty: Type::Option(Box::new(Type::IntN(
                        kea_types::IntWidth::I8,
                        kea_types::Signedness::Signed,
                    ))),
                    span: kea_ast::Span::synthetic(),
                },
                ty: Type::Function(FunctionType::pure(
                    vec![],
                    Type::Option(Box::new(Type::IntN(
                        kea_types::IntWidth::I8,
                        kea_types::Signedness::Signed,
                    ))),
                )),
                effects: EffectRow::pure(),
                span: kea_ast::Span::synthetic(),
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
                    } if sum_type == "Option" && variant == "Some" && *tag == 0
                )),
            "expected Some construction in try_from lowering"
        );
    }

    #[test]
    fn lower_hir_module_widens_signed_fixed_width_input_before_try_from_checks() {
        let option_int8 = Type::Option(Box::new(Type::IntN(
            kea_types::IntWidth::I8,
            kea_types::Signedness::Signed,
        )));
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
                            ty: Type::IntN(
                                kea_types::IntWidth::I8,
                                kea_types::Signedness::Signed,
                            ),
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
            row: RowType::closed(vec![
                (Label::new("age"), Type::Int),
                (Label::new("name"), Type::String),
            ]),
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
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks[0].instructions.len(), 1);
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
    }

    #[test]
    fn lower_hir_module_lowers_record_literal_expression() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
            row: RowType::closed(vec![
                (Label::new("age"), Type::Int),
                (Label::new("name"), Type::String),
            ]),
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
            row: RowType::closed(vec![
                (Label::new("age"), Type::Int),
                (Label::new("score"), Type::Int),
            ]),
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
            row: RowType::closed(vec![
                (Label::new("age"), Type::Int),
                (Label::new("score"), Type::Int),
            ]),
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
            derives: vec![],
        }));
        let option_ty = Type::Sum(kea_types::SumType {
            name: "Option".to_string(),
            type_args: vec![Type::Int],
            variants: vec![
                ("Some".to_string(), vec![Type::Int]),
                ("None".to_string(), vec![]),
            ],
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
            variants: vec![
                ("Some".to_string(), vec![Type::Int]),
                ("None".to_string(), vec![]),
            ],
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
            variants: vec![
                ("Some".to_string(), vec![Type::Int]),
                ("None".to_string(), vec![]),
            ],
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
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert_eq!(function.blocks[0].instructions.len(), 1);
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
    }

    #[test]
    fn lower_hir_module_resolves_record_field_load_for_let_bound_record_var() {
        let user_ty = Type::Record(RecordType {
            name: "User".to_string(),
            params: vec![],
            row: RowType::closed(vec![(Label::new("age"), Type::Int)]),
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
                    field_annotations: vec![],
                    derives: vec![],
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
        let hir = HirModule {
            declarations: vec![HirDecl::Function(HirFunction {
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
    fn lower_hir_module_retains_heap_var_aliases_before_binding() {
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
            })],
        };

        let mir = lower_hir_module(&hir);
        let function = &mir.functions[0];
        assert!(
            function.blocks[0]
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Retain { .. })),
            "heap alias let-binding should emit Retain before rebinding"
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
            })],
        };

        let mir = lower_hir_module(&hir);
        let instructions = &mir.functions[0].blocks[0].instructions;
        let int_const_idx = instructions
            .iter()
            .position(|inst| matches!(inst, MirInst::Const { literal: MirLiteral::Int(1), .. }))
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
            row: RowType::closed(vec![(Label::new("age"), Type::Int)]),
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
                    field_annotations: vec![],
                    derives: vec![],
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
            variants: vec![
                ("Ok".to_string(), vec![Type::Int]),
                ("Err".to_string(), vec![Type::Int]),
            ],
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
}

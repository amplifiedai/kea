//! Backend-neutral mid-level IR (MIR) for Kea.
//!
//! This crate defines explicit control-flow + memory/effect operations that are
//! independent of any specific backend API (Cranelift, LLVM, etc.).

use std::collections::{BTreeMap, BTreeSet};

use kea_ast::{BinOp, DeclKind, ExprKind as AstExprKind, UnaryOp};
use kea_hir::{HirDecl, HirExpr, HirExprKind, HirFunction, HirModule, HirPattern};
use kea_types::{EffectRow, Type};

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
        cc_manifest_id: String,
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
    In,
    NotIn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirUnaryOp {
    Neg,
    Not,
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
                | MirInst::SumTagLoad { .. }
                | MirInst::SumPayloadLoad { .. }
                | MirInst::RecordFieldLoad { .. }
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
    let mut layouts = MirLayoutCatalog::default();
    for decl in &module.declarations {
        if let HirDecl::Raw(raw_decl) = decl {
            collect_layout_metadata(raw_decl, &mut layouts);
        }
    }
    let functions = module
        .declarations
        .iter()
        .filter_map(|decl| match decl {
            HirDecl::Function(function) => {
                Some(lower_hir_function(function, &layouts, &known_functions))
            }
            HirDecl::Raw(_) => None,
        })
        .collect();

    MirModule { functions, layouts }
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

fn lower_hir_function(
    function: &HirFunction,
    layouts: &MirLayoutCatalog,
    known_functions: &BTreeSet<String>,
) -> MirFunction {
    let (params, ret) = match &function.ty {
        Type::Function(ft) => (ft.params.clone(), ft.ret.as_ref().clone()),
        _ => (
            function.params.iter().map(|_| Type::Dynamic).collect(),
            Type::Dynamic,
        ),
    };

    let mut ctx = FunctionLoweringCtx::new(&function.name, params.len(), layouts, known_functions);
    for (index, param) in function.params.iter().enumerate() {
        if let Some(name) = &param.name {
            ctx.vars.insert(name.clone(), MirValueId(index as u32));
            if let Some(param_ty) = params.get(index) {
                ctx.var_types.insert(name.clone(), param_ty.clone());
            }
            if let Some(Type::Record(record_ty)) = params.get(index) {
                ctx.var_record_types
                    .insert(name.clone(), record_ty.name.clone());
            }
        }
        if let Some(Type::Sum(sum_ty)) = params.get(index) {
            ctx.sum_value_types
                .insert(MirValueId(index as u32), sum_ty.name.clone());
        }
    }
    let return_value = ctx.lower_expr(&function.body);
    let blocks = ctx.finish(return_value, &ret);

    MirFunction {
        name: function.name.clone(),
        signature: MirFunctionSignature {
            params,
            ret,
            effects: function.effects.clone(),
        },
        entry: MirBlockId(0),
        blocks,
    }
}

#[derive(Debug, Clone)]
struct PendingBlock {
    id: MirBlockId,
    params: Vec<MirBlockParam>,
    instructions: Vec<MirInst>,
    terminator: Option<MirTerminator>,
}

struct FunctionLoweringCtx {
    blocks: Vec<PendingBlock>,
    current_block: MirBlockId,
    vars: BTreeMap<String, MirValueId>,
    var_types: BTreeMap<String, Type>,
    known_functions: BTreeSet<String>,
    var_record_types: BTreeMap<String, String>,
    sum_value_types: BTreeMap<MirValueId, String>,
    sum_ctor_candidates: BTreeMap<String, Vec<SumCtorCandidate>>,
    next_value_id: u32,
}

#[derive(Debug, Clone)]
struct SumCtorCandidate {
    sum_type: String,
    tag: u32,
    arity: usize,
}

impl FunctionLoweringCtx {
    fn new(
        _function_name: &str,
        param_count: usize,
        layouts: &MirLayoutCatalog,
        known_functions: &BTreeSet<String>,
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

        Self {
            blocks: vec![PendingBlock {
                id: MirBlockId(0),
                params: Vec::new(),
                instructions: Vec::new(),
                terminator: None,
            }],
            current_block: MirBlockId(0),
            vars: BTreeMap::new(),
            var_types: BTreeMap::new(),
            known_functions: known_functions.clone(),
            var_record_types: BTreeMap::new(),
            sum_value_types: BTreeMap::new(),
            sum_ctor_candidates,
            next_value_id: param_count as u32,
        }
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
                    let dest = self.new_value();
                    self.emit_inst(MirInst::FunctionRef {
                        dest: dest.clone(),
                        function: name.clone(),
                    });
                    return Some(dest);
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
                Some(dest)
            }
            HirExprKind::RecordUpdate {
                record_type,
                base,
                fields,
            } => {
                let target = self.lower_expr(base)?;
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

                let mut updates = Vec::with_capacity(fields.len());
                for (field_name, field_expr) in fields {
                    let value = self.lower_expr(field_expr)?;
                    updates.push(MirFieldUpdate {
                        field: field_name.clone(),
                        value,
                    });
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
                    _ => match &base.kind {
                        HirExprKind::Var(name) => self.var_record_types.get(name).cloned(),
                        _ => None,
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
                Some(dest)
            }
            HirExprKind::Call { func, args } => {
                if let HirExprKind::Var(name) = &func.kind
                    && name == "Fail::fail"
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
                let callee_fail_result_abi = match &func.kind {
                    HirExprKind::Var(name) => self
                        .var_types
                        .get(name)
                        .map_or_else(|| uses_fail_result_abi_from_type(&func.ty), uses_fail_result_abi_from_type),
                    _ => uses_fail_result_abi_from_type(&func.ty),
                };

                let callee = match &func.kind {
                    HirExprKind::Var(name) if name.contains("::") => {
                        MirCallee::External(name.clone())
                    }
                    HirExprKind::Var(name) if self.vars.contains_key(name) => {
                        let callee_value = self.lower_expr(func)?;
                        MirCallee::Value(callee_value)
                    }
                    HirExprKind::Var(name) => MirCallee::Local(name.clone()),
                    _ => {
                        let callee_value = self.lower_expr(func)?;
                        MirCallee::Value(callee_value)
                    }
                };

                let mut lowered_args = Vec::with_capacity(args.len());
                let mut arg_types = Vec::with_capacity(args.len());
                for arg in args {
                    arg_types.push(arg.ty.clone());
                    lowered_args.push(self.lower_expr(arg)?);
                }

                let result = if expr.ty == Type::Unit {
                    None
                } else {
                    Some(self.new_value())
                };

                self.emit_inst(MirInst::Call {
                    callee,
                    args: lowered_args,
                    arg_types,
                    result: result.clone(),
                    ret_type: expr.ty.clone(),
                    callee_fail_result_abi,
                    cc_manifest_id: "default".to_string(),
                });
                if let (Some(dest), Type::Sum(sum_ty)) = (&result, &expr.ty) {
                    self.sum_value_types
                        .insert(dest.clone(), sum_ty.name.clone());
                }
                result
            }
            HirExprKind::Let { pattern, value } => {
                let value_id = self.lower_expr(value)?;
                self.bind_pattern(pattern, value_id.clone(), &value.ty);
                Some(value_id)
            }
            HirExprKind::Block(exprs) => {
                let mut last = None;
                for expr in exprs {
                    last = self.lower_expr(expr);
                    if self.current_block().terminator.is_some() {
                        break;
                    }
                }
                last
            }
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => self.lower_if(expr, condition, then_branch, else_branch.as_deref()),
            HirExprKind::Tuple(_) | HirExprKind::Lambda { .. } | HirExprKind::Raw(_) => {
                match &expr.kind {
                    HirExprKind::Raw(raw_expr) => self.lower_raw_ast_expr(raw_expr),
                    _ => None,
                }
            }
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

    fn lower_if(
        &mut self,
        expr: &HirExpr,
        condition: &HirExpr,
        then_branch: &HirExpr,
        else_branch: Option<&HirExpr>,
    ) -> Option<MirValueId> {
        let condition_value = self.lower_expr(condition)?;
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
        if then_terminated && else_terminated {
            self.set_terminator(MirTerminator::Unreachable);
            return None;
        }
        result_value
    }

    fn bind_pattern(&mut self, pattern: &HirPattern, value_id: MirValueId, value_ty: &Type) {
        if let HirPattern::Var(name) = pattern {
            self.vars.insert(name.clone(), value_id);
            self.var_types.insert(name.clone(), value_ty.clone());
            if let Type::Record(record_ty) = value_ty {
                self.var_record_types
                    .insert(name.clone(), record_ty.name.clone());
            }
        }
    }

    fn lower_short_circuit_binary(
        &mut self,
        op: BinOp,
        left: &HirExpr,
        right: &HirExpr,
    ) -> Option<MirValueId> {
        let left_value = self.lower_expr(left)?;
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
        let rhs_value = self.lower_expr(right)?;
        self.ensure_jump_to(join_block.clone(), vec![rhs_value]);

        self.switch_to(short_block);
        let short_const = self.new_value();
        self.emit_inst(MirInst::Const {
            dest: short_const.clone(),
            literal: MirLiteral::Bool(short_value),
        });
        self.ensure_jump_to(join_block.clone(), vec![short_const]);

        self.switch_to(join_block);
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

#[cfg(test)]
mod tests {
    use super::*;
    use kea_ast::{
        Argument, DeclKind, ExprKind, RecordDef, Spanned, TypeAnnotation, TypeDef, TypeVariant,
        VariantField,
    };
    use kea_hir::{HirExpr, HirExprKind, HirFunction, HirParam};
    use kea_types::{FunctionType, Label, RecordType, RowType, SumType};

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
        assert_eq!(mir.layouts.sums.len(), 1);
        let option = &mir.layouts.sums[0];
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
        assert!(function.blocks[0]
            .instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::Retain { .. })));
        assert!(function.blocks[0]
            .instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::TryClaim { .. })));
        assert!(function.blocks[0]
            .instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::Freeze { .. })));
        assert!(function.blocks[0]
            .instructions
            .iter()
            .any(|inst| matches!(
                inst,
                MirInst::CowUpdate {
                    record_type,
                    updates,
                    ..
                } if record_type == "User" && updates.len() == 1 && updates[0].field == "age"
            )));
        assert!(function.blocks[0]
            .instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::Release { .. })));
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
        assert!(function.blocks[0]
            .instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::Binary { op: MirBinaryOp::Add, .. })));
        assert!(function.blocks[0]
            .instructions
            .iter()
            .any(|inst| matches!(
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
                            kind: HirExprKind::Var("Fail::fail".to_string()),
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
            caller.blocks[0].instructions.first(),
            Some(MirInst::FunctionRef { function, .. }) if function == "inc"
        ));
        assert!(matches!(
            caller.blocks[0].instructions.get(1),
            Some(MirInst::Call {
                callee: MirCallee::Local(name),
                ..
            }) if name == "apply"
        ));
    }
}

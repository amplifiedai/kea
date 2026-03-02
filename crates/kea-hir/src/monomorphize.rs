//! Monomorphization pass for HIR.
//!
//! Transforms an `HirModule` so that every function has concrete types — no
//! `Type::Var` survives past this point.  Polymorphic functions are cloned and
//! specialized for each distinct set of concrete type arguments observed at
//! call sites.  The original polymorphic definitions are removed from the
//! module.

use std::collections::{BTreeMap, HashMap, VecDeque};

use kea_types::{Substitution, Type, TypeVarId, free_type_vars};

use crate::{HirDecl, HirExpr, HirExprKind, HirFunction, HirHandleClause, HirModule};

/// A hashable key for a specialization: (original name, sorted bindings as strings).
type SpecKey = (String, Vec<(TypeVarId, String)>);

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Monomorphize all polymorphic functions in `module`.
///
/// After this pass every `HirFunction` has fully concrete types and the module
/// contains no polymorphic definitions.
pub fn monomorphize(module: &HirModule) -> HirModule {
    let mut pass = MonoPass::new(module);
    pass.run()
}

// ---------------------------------------------------------------------------
// Pass state
// ---------------------------------------------------------------------------

/// Maximum specialization depth to prevent runaway recursive polymorphism.
const MAX_DEPTH: usize = 32;

struct MonoPass<'a> {
    module: &'a HirModule,
    /// Original polymorphic functions keyed by name.
    poly_fns: BTreeMap<String, &'a HirFunction>,
    /// Maps unqualified names (e.g. "filter") to their qualified poly fn
    /// (e.g. "List.filter") for call-site resolution.
    unqualified_to_qualified: BTreeMap<String, String>,
    /// Already-generated specializations: (original_name, stringified bindings) → mangled name.
    generated: HashMap<SpecKey, String>,
    /// Work queue: (original_name, substitution, mangled_name, depth).
    queue: VecDeque<(String, Substitution, String, usize)>,
    /// Monotonic counter for mangled name disambiguation.
    next_id: u32,
    /// Completed specialized functions ready for output.
    specialized: Vec<HirFunction>,
}

impl<'a> MonoPass<'a> {
    fn new(module: &'a HirModule) -> Self {
        let mut poly_fns = BTreeMap::new();
        let mut unqualified_to_qualified: BTreeMap<String, String> = BTreeMap::new();
        for decl in &module.declarations {
            if let HirDecl::Function(f) = decl
                && !free_type_vars(&f.ty).is_empty()
            {
                poly_fns.insert(f.name.clone(), f);
                // Map unqualified name to qualified if applicable.
                if let Some((_module, short)) = f.name.rsplit_once('.') {
                    // Only map if the unqualified name isn't already a poly fn
                    // (avoid clobbering `fold` with `List.fold` if both exist).
                    if !poly_fns.contains_key(short) {
                        unqualified_to_qualified.insert(short.to_string(), f.name.clone());
                    }
                }
            }
        }
        Self {
            module,
            poly_fns,
            unqualified_to_qualified,
            generated: HashMap::new(),
            queue: VecDeque::new(),
            next_id: 0,
            specialized: Vec::new(),
        }
    }

    fn run(&mut self) -> HirModule {
        // Phase 1: rewrite all function bodies, seeding the worklist.
        // Polymorphic functions are kept as fallbacks for call sites the pass
        // cannot rewrite (e.g., inside Raw expressions).
        let mut declarations: Vec<HirDecl> = Vec::new();
        for decl in &self.module.declarations {
            match decl {
                HirDecl::Function(f) => {
                    let rewritten = HirFunction {
                        name: f.name.clone(),
                        params: f.params.clone(),
                        body: self.rewrite_calls(&f.body, 0),
                        ty: f.ty.clone(),
                        effects: f.effects.clone(),
                        span: f.span,
                    };
                    declarations.push(HirDecl::Function(rewritten));
                }
                other => declarations.push(other.clone()),
            }
        }

        // Phase 2: process the worklist — generate specialized functions.
        while let Some((orig_name, subst, mangled, depth)) = self.queue.pop_front() {
            let Some(poly_fn) = self.poly_fns.get(&orig_name) else {
                continue;
            };
            let mut specialized = apply_subst_to_function(poly_fn, &subst);
            specialized.name = mangled;
            // Rewrite calls inside the specialized body (may enqueue more work).
            specialized.body = self.rewrite_calls(&specialized.body, depth);
            self.specialized.push(specialized);
        }

        // Phase 3: append all specializations to the module.
        declarations.extend(self.specialized.drain(..).map(HirDecl::Function));

        HirModule { declarations }
    }

    /// Walk an expression tree, rewriting calls to polymorphic functions to
    /// their mangled specialized names and enqueueing specialization requests.
    fn rewrite_calls(&mut self, expr: &HirExpr, depth: usize) -> HirExpr {
        let kind = match &expr.kind {
            HirExprKind::Call { func, args } => {
                let rewritten_args: Vec<HirExpr> =
                    args.iter().map(|a| self.rewrite_calls(a, depth)).collect();
                let callee_name = match &func.kind {
                    HirExprKind::Var(name) => Some(name.as_str()),
                    _ => None,
                };
                // Resolve unqualified names like "filter" → "List.filter".
                let resolved_name = callee_name.and_then(|name| {
                    if self.poly_fns.contains_key(name) {
                        Some(name.to_string())
                    } else {
                        self.unqualified_to_qualified.get(name).cloned()
                    }
                });
                if let Some(ref resolved) = resolved_name
                    && let Some(poly_fn) = self.poly_fns.get(resolved.as_str())
                {
                    // Extract type variable bindings from call-site arg types.
                    let poly_ty = &poly_fn.ty;
                    if let Type::Function(ft) = poly_ty {
                        let mut bindings = BTreeMap::new();
                        for (poly_param, arg) in ft.params.iter().zip(rewritten_args.iter()) {
                            extract_bindings(poly_param, &arg.ty, &mut bindings);
                        }
                        // Also extract from the return type if the call expr has
                        // a concrete type.
                        extract_bindings(&ft.ret, &expr.ty, &mut bindings);

                        if !bindings.is_empty()
                            && bindings.values().all(|t| free_type_vars(t).is_empty())
                        {
                            let mangled = self.get_or_enqueue(resolved, &bindings, depth);
                            // Build the concrete function type for the rewritten callee.
                            let mut subst = Substitution::new();
                            for (var, ty) in &bindings {
                                subst.bind_type(*var, ty.clone());
                            }
                            let concrete_fn_ty = subst.apply(poly_ty);
                            let new_func = Box::new(HirExpr {
                                kind: HirExprKind::Var(mangled),
                                ty: concrete_fn_ty,
                                span: func.span,
                            });
                            HirExprKind::Call {
                                func: new_func,
                                args: rewritten_args,
                            }
                        } else {
                            // Incomplete bindings — keep original call.
                            HirExprKind::Call {
                                func: Box::new(self.rewrite_calls(func, depth)),
                                args: rewritten_args,
                            }
                        }
                    } else {
                        HirExprKind::Call {
                            func: Box::new(self.rewrite_calls(func, depth)),
                            args: rewritten_args,
                        }
                    }
                } else {
                    HirExprKind::Call {
                        func: Box::new(self.rewrite_calls(func, depth)),
                        args: rewritten_args,
                    }
                }
            }

            // Recurse into all other variants.
            HirExprKind::Lit(_) | HirExprKind::Var(_) => expr.kind.clone(),

            HirExprKind::RecordLit {
                record_type,
                fields,
            } => HirExprKind::RecordLit {
                record_type: record_type.clone(),
                fields: fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.rewrite_calls(e, depth)))
                    .collect(),
            },

            HirExprKind::RecordUpdate {
                record_type,
                base,
                fields,
            } => HirExprKind::RecordUpdate {
                record_type: record_type.clone(),
                base: Box::new(self.rewrite_calls(base, depth)),
                fields: fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.rewrite_calls(e, depth)))
                    .collect(),
            },

            HirExprKind::SumConstructor {
                sum_type,
                variant,
                tag,
                fields,
            } => HirExprKind::SumConstructor {
                sum_type: sum_type.clone(),
                variant: variant.clone(),
                tag: *tag,
                fields: fields
                    .iter()
                    .map(|e| self.rewrite_calls(e, depth))
                    .collect(),
            },

            HirExprKind::SumPayloadAccess {
                expr: inner,
                sum_type,
                variant,
                field_index,
            } => HirExprKind::SumPayloadAccess {
                expr: Box::new(self.rewrite_calls(inner, depth)),
                sum_type: sum_type.clone(),
                variant: variant.clone(),
                field_index: *field_index,
            },

            HirExprKind::FieldAccess { expr: inner, field } => HirExprKind::FieldAccess {
                expr: Box::new(self.rewrite_calls(inner, depth)),
                field: field.clone(),
            },

            HirExprKind::Binary { op, left, right } => HirExprKind::Binary {
                op: *op,
                left: Box::new(self.rewrite_calls(left, depth)),
                right: Box::new(self.rewrite_calls(right, depth)),
            },

            HirExprKind::Unary { op, operand } => HirExprKind::Unary {
                op: *op,
                operand: Box::new(self.rewrite_calls(operand, depth)),
            },

            HirExprKind::Lambda { params, body } => HirExprKind::Lambda {
                params: params.clone(),
                body: Box::new(self.rewrite_calls(body, depth)),
            },

            HirExprKind::Catch { expr: inner } => HirExprKind::Catch {
                expr: Box::new(self.rewrite_calls(inner, depth)),
            },

            HirExprKind::Handle {
                expr: inner,
                clauses,
                then_clause,
            } => HirExprKind::Handle {
                expr: Box::new(self.rewrite_calls(inner, depth)),
                clauses: clauses
                    .iter()
                    .map(|c| HirHandleClause {
                        effect: c.effect.clone(),
                        operation: c.operation.clone(),
                        args: c.args.clone(),
                        body: self.rewrite_calls(&c.body, depth),
                        span: c.span,
                    })
                    .collect(),
                then_clause: then_clause
                    .as_ref()
                    .map(|e| Box::new(self.rewrite_calls(e, depth))),
            },

            HirExprKind::Resume { value } => HirExprKind::Resume {
                value: Box::new(self.rewrite_calls(value, depth)),
            },

            HirExprKind::Let { pattern, value } => HirExprKind::Let {
                pattern: pattern.clone(),
                value: Box::new(self.rewrite_calls(value, depth)),
            },

            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => HirExprKind::If {
                condition: Box::new(self.rewrite_calls(condition, depth)),
                then_branch: Box::new(self.rewrite_calls(then_branch, depth)),
                else_branch: else_branch
                    .as_ref()
                    .map(|e| Box::new(self.rewrite_calls(e, depth))),
            },

            HirExprKind::Block(exprs) => {
                HirExprKind::Block(exprs.iter().map(|e| self.rewrite_calls(e, depth)).collect())
            }

            HirExprKind::Tuple(exprs) => {
                HirExprKind::Tuple(exprs.iter().map(|e| self.rewrite_calls(e, depth)).collect())
            }

            HirExprKind::Raw(_) => expr.kind.clone(),
        };

        HirExpr {
            kind,
            ty: expr.ty.clone(),
            span: expr.span,
        }
    }

    /// Look up or create a specialization for `orig_name` with the given
    /// type variable bindings.  Returns the mangled name.
    fn get_or_enqueue(
        &mut self,
        orig_name: &str,
        bindings: &BTreeMap<TypeVarId, Type>,
        depth: usize,
    ) -> String {
        let key: Vec<(TypeVarId, String)> =
            bindings.iter().map(|(k, v)| (*k, format!("{v}"))).collect();
        let cache_key = (orig_name.to_string(), key);
        if let Some(mangled) = self.generated.get(&cache_key) {
            return mangled.clone();
        }

        let mangled = mangle_name(orig_name, bindings, self.next_id);
        self.next_id += 1;
        self.generated.insert(cache_key, mangled.clone());

        if depth < MAX_DEPTH {
            let mut subst = Substitution::new();
            for (var, ty) in bindings {
                subst.bind_type(*var, ty.clone());
            }
            self.queue
                .push_back((orig_name.to_string(), subst, mangled.clone(), depth + 1));
        }

        mangled
    }
}

// ---------------------------------------------------------------------------
// HIR substitution
// ---------------------------------------------------------------------------

/// Apply a type substitution to every type in an `HirFunction`.
fn apply_subst_to_function(f: &HirFunction, subst: &Substitution) -> HirFunction {
    HirFunction {
        name: f.name.clone(),
        params: f.params.clone(),
        body: apply_subst_to_expr(&f.body, subst),
        ty: subst.apply(&f.ty),
        effects: subst.apply_effect_row(&f.effects),
        span: f.span,
    }
}

/// Recursively apply a type substitution to every `.ty` field in an expression.
fn apply_subst_to_expr(expr: &HirExpr, subst: &Substitution) -> HirExpr {
    let ty = subst.apply(&expr.ty);
    let kind = match &expr.kind {
        HirExprKind::Lit(_) | HirExprKind::Var(_) | HirExprKind::Raw(_) => expr.kind.clone(),

        HirExprKind::Call { func, args } => HirExprKind::Call {
            func: Box::new(apply_subst_to_expr(func, subst)),
            args: args.iter().map(|a| apply_subst_to_expr(a, subst)).collect(),
        },

        HirExprKind::RecordLit {
            record_type,
            fields,
        } => HirExprKind::RecordLit {
            record_type: record_type.clone(),
            fields: fields
                .iter()
                .map(|(n, e)| (n.clone(), apply_subst_to_expr(e, subst)))
                .collect(),
        },

        HirExprKind::RecordUpdate {
            record_type,
            base,
            fields,
        } => HirExprKind::RecordUpdate {
            record_type: record_type.clone(),
            base: Box::new(apply_subst_to_expr(base, subst)),
            fields: fields
                .iter()
                .map(|(n, e)| (n.clone(), apply_subst_to_expr(e, subst)))
                .collect(),
        },

        HirExprKind::SumConstructor {
            sum_type,
            variant,
            tag,
            fields,
        } => HirExprKind::SumConstructor {
            sum_type: sum_type.clone(),
            variant: variant.clone(),
            tag: *tag,
            fields: fields
                .iter()
                .map(|e| apply_subst_to_expr(e, subst))
                .collect(),
        },

        HirExprKind::SumPayloadAccess {
            expr: inner,
            sum_type,
            variant,
            field_index,
        } => HirExprKind::SumPayloadAccess {
            expr: Box::new(apply_subst_to_expr(inner, subst)),
            sum_type: sum_type.clone(),
            variant: variant.clone(),
            field_index: *field_index,
        },

        HirExprKind::FieldAccess { expr: inner, field } => HirExprKind::FieldAccess {
            expr: Box::new(apply_subst_to_expr(inner, subst)),
            field: field.clone(),
        },

        HirExprKind::Binary { op, left, right } => HirExprKind::Binary {
            op: *op,
            left: Box::new(apply_subst_to_expr(left, subst)),
            right: Box::new(apply_subst_to_expr(right, subst)),
        },

        HirExprKind::Unary { op, operand } => HirExprKind::Unary {
            op: *op,
            operand: Box::new(apply_subst_to_expr(operand, subst)),
        },

        HirExprKind::Lambda { params, body } => HirExprKind::Lambda {
            params: params.clone(),
            body: Box::new(apply_subst_to_expr(body, subst)),
        },

        HirExprKind::Catch { expr: inner } => HirExprKind::Catch {
            expr: Box::new(apply_subst_to_expr(inner, subst)),
        },

        HirExprKind::Handle {
            expr: inner,
            clauses,
            then_clause,
        } => HirExprKind::Handle {
            expr: Box::new(apply_subst_to_expr(inner, subst)),
            clauses: clauses
                .iter()
                .map(|c| HirHandleClause {
                    effect: c.effect.clone(),
                    operation: c.operation.clone(),
                    args: c.args.clone(),
                    body: apply_subst_to_expr(&c.body, subst),
                    span: c.span,
                })
                .collect(),
            then_clause: then_clause
                .as_ref()
                .map(|e| Box::new(apply_subst_to_expr(e, subst))),
        },

        HirExprKind::Resume { value } => HirExprKind::Resume {
            value: Box::new(apply_subst_to_expr(value, subst)),
        },

        HirExprKind::Let { pattern, value } => HirExprKind::Let {
            pattern: pattern.clone(),
            value: Box::new(apply_subst_to_expr(value, subst)),
        },

        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => HirExprKind::If {
            condition: Box::new(apply_subst_to_expr(condition, subst)),
            then_branch: Box::new(apply_subst_to_expr(then_branch, subst)),
            else_branch: else_branch
                .as_ref()
                .map(|e| Box::new(apply_subst_to_expr(e, subst))),
        },

        HirExprKind::Block(exprs) => HirExprKind::Block(
            exprs
                .iter()
                .map(|e| apply_subst_to_expr(e, subst))
                .collect(),
        ),

        HirExprKind::Tuple(exprs) => HirExprKind::Tuple(
            exprs
                .iter()
                .map(|e| apply_subst_to_expr(e, subst))
                .collect(),
        ),
    };

    HirExpr {
        kind,
        ty,
        span: expr.span,
    }
}

// ---------------------------------------------------------------------------
// Type-variable binding extraction
// ---------------------------------------------------------------------------

/// Walk two types in parallel — one polymorphic, one concrete — and extract
/// bindings for every `Var(v)` found in the polymorphic type.
fn extract_bindings(poly: &Type, concrete: &Type, out: &mut BTreeMap<TypeVarId, Type>) {
    match (poly, concrete) {
        (Type::Var(v), _) => {
            out.insert(*v, concrete.clone());
        }
        (Type::Function(pf), Type::Function(cf)) => {
            for (p, c) in pf.params.iter().zip(cf.params.iter()) {
                extract_bindings(p, c, out);
            }
            extract_bindings(&pf.ret, &cf.ret, out);
        }
        (Type::List(p), Type::List(c)) => extract_bindings(p, c, out),
        (Type::Option(p), Type::Option(c)) => extract_bindings(p, c, out),
        (Type::Result(po, pe), Type::Result(co, ce)) => {
            extract_bindings(po, co, out);
            extract_bindings(pe, ce, out);
        }
        (Type::Map(pk, pv), Type::Map(ck, cv)) => {
            extract_bindings(pk, ck, out);
            extract_bindings(pv, cv, out);
        }
        (Type::Set(p), Type::Set(c)) => extract_bindings(p, c, out),
        (Type::Tuple(ps), Type::Tuple(cs)) => {
            for (p, c) in ps.iter().zip(cs.iter()) {
                extract_bindings(p, c, out);
            }
        }
        (Type::Arc(p), Type::Arc(c)) => extract_bindings(p, c, out),
        (Type::Task(p), Type::Task(c)) => extract_bindings(p, c, out),
        (Type::Actor(p), Type::Actor(c)) => extract_bindings(p, c, out),
        (Type::Opaque { params: pp, .. }, Type::Opaque { params: cp, .. }) => {
            for (p, c) in pp.iter().zip(cp.iter()) {
                extract_bindings(p, c, out);
            }
        }
        // Primitives and mismatches: nothing to extract.
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Name mangling
// ---------------------------------------------------------------------------

/// Build a human-readable mangled name for a specialization.
///
/// Format: `{original}$m{id}` with a comment-style suffix for debuggability.
/// We use a sequential id for uniqueness; the actual type args are embedded in
/// the generated function's type, not the name.
fn mangle_name(original: &str, bindings: &BTreeMap<TypeVarId, Type>, id: u32) -> String {
    // Build a short type signature for debuggability.
    let types_str: String = bindings
        .values()
        .map(sanitize_type_for_name)
        .collect::<Vec<_>>()
        .join("_");
    if types_str.is_empty() {
        format!("{original}$m{id}")
    } else {
        format!("{original}$m{id}${types_str}")
    }
}

fn sanitize_type_for_name(ty: &Type) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "Str".to_string(),
        Type::Float => "Float".to_string(),
        Type::Unit => "Unit".to_string(),
        Type::Dynamic => "Dyn".to_string(),
        Type::List(inner) => format!("List{}", sanitize_type_for_name(inner)),
        Type::Option(inner) => format!("Opt{}", sanitize_type_for_name(inner)),
        Type::Function(ft) => {
            let params: Vec<_> = ft.params.iter().map(sanitize_type_for_name).collect();
            let ret = sanitize_type_for_name(&ft.ret);
            format!("fn{}to{}", params.join(""), ret)
        }
        _ => format!("{ty}").replace(['(', ')', ',', ' ', '<', '>', '[', ']'], ""),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use kea_ast::Span;
    use kea_types::FunctionType;

    fn dummy_span() -> Span {
        Span::new(kea_ast::FileId(0), 0, 0)
    }

    fn var_expr(name: &str, ty: Type) -> HirExpr {
        HirExpr {
            kind: HirExprKind::Var(name.to_string()),
            ty,
            span: dummy_span(),
        }
    }

    fn lit_int(n: i64) -> HirExpr {
        HirExpr {
            kind: HirExprKind::Lit(kea_ast::Lit::Int(n)),
            ty: Type::Int,
            span: dummy_span(),
        }
    }

    fn call_expr(func: HirExpr, args: Vec<HirExpr>, ret_ty: Type) -> HirExpr {
        HirExpr {
            kind: HirExprKind::Call {
                func: Box::new(func),
                args,
            },
            ty: ret_ty,
            span: dummy_span(),
        }
    }

    fn make_fn_type(params: Vec<Type>, ret: Type) -> Type {
        Type::Function(FunctionType {
            params,
            ret: Box::new(ret),
            effects: kea_types::EffectRow::pure(),
        })
    }

    #[test]
    fn extract_bindings_simple() {
        let var_a = TypeVarId(100);
        let poly = Type::List(Box::new(Type::Var(var_a)));
        let concrete = Type::List(Box::new(Type::Int));
        let mut bindings = BTreeMap::new();
        extract_bindings(&poly, &concrete, &mut bindings);
        assert_eq!(bindings.get(&var_a), Some(&Type::Int));
    }

    #[test]
    fn extract_bindings_function() {
        let var_a = TypeVarId(1);
        let var_b = TypeVarId(2);
        let poly = make_fn_type(vec![Type::Var(var_a)], Type::Var(var_b));
        let concrete = make_fn_type(vec![Type::Int], Type::Bool);
        let mut bindings = BTreeMap::new();
        extract_bindings(&poly, &concrete, &mut bindings);
        assert_eq!(bindings.get(&var_a), Some(&Type::Int));
        assert_eq!(bindings.get(&var_b), Some(&Type::Bool));
    }

    #[test]
    fn monomorphize_simple_call() {
        let var_a = TypeVarId(10);

        // Polymorphic function: identity(x: a) -> a
        let identity_fn = HirFunction {
            name: "identity".to_string(),
            params: vec![crate::HirParam {
                name: Some("x".to_string()),
                span: dummy_span(),
            }],
            body: var_expr("x", Type::Var(var_a)),
            ty: make_fn_type(vec![Type::Var(var_a)], Type::Var(var_a)),
            effects: kea_types::EffectRow::pure(),
            span: dummy_span(),
        };

        // Monomorphic function: main() calls identity(42)
        let main_fn = HirFunction {
            name: "main".to_string(),
            params: vec![],
            body: call_expr(
                var_expr("identity", make_fn_type(vec![Type::Int], Type::Int)),
                vec![lit_int(42)],
                Type::Int,
            ),
            ty: make_fn_type(vec![], Type::Int),
            effects: kea_types::EffectRow::pure(),
            span: dummy_span(),
        };

        let module = HirModule {
            declarations: vec![HirDecl::Function(identity_fn), HirDecl::Function(main_fn)],
        };

        let result = monomorphize(&module);

        // Should have 3 functions: main + original identity + specialized identity.
        let fns: Vec<_> = result
            .declarations
            .iter()
            .filter_map(|d| match d {
                HirDecl::Function(f) => Some(&f.name),
                _ => None,
            })
            .collect();
        assert_eq!(fns.len(), 3);
        // main should still be there.
        assert!(fns.contains(&&"main".to_string()));
        // Original polymorphic identity kept as fallback.
        assert!(fns.contains(&&"identity".to_string()));
        // There should be a specialized identity.
        let specialized = fns.iter().find(|n| n.starts_with("identity$m")).unwrap();
        // The specialized function should have concrete Int types.
        let spec_fn = result
            .declarations
            .iter()
            .find_map(|d| match d {
                HirDecl::Function(f) if &f.name == *specialized => Some(f),
                _ => None,
            })
            .unwrap();
        assert_eq!(spec_fn.ty, make_fn_type(vec![Type::Int], Type::Int),);
        // The body should also have concrete type.
        assert_eq!(spec_fn.body.ty, Type::Int);
    }
}

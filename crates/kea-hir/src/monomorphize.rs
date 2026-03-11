//! Monomorphization pass for HIR.
//!
//! Transforms an `HirModule` so that every function has concrete types — no
//! `Type::Var` survives past this point.  Polymorphic functions are cloned and
//! specialized for each distinct set of concrete type arguments observed at
//! call sites.  The original polymorphic definitions are removed from the
//! module.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use kea_types::{Substitution, SumType, Type, TypeVarId, free_type_vars};

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
    /// Maps unqualified short names (e.g. "filter") to all qualified poly fns
    /// that have that name (e.g. ["List.filter"]).  When there is exactly one
    /// candidate the lookup is unambiguous.  When there are multiple candidates
    /// (e.g. "zip" in both List and Option), type-based resolution is used to
    /// pick the one whose parameter types match the call site.
    short_to_qualified: BTreeMap<String, Vec<String>>,
    /// Bare (unqualified) names that are merge artifacts — they have at least
    /// one qualified counterpart in the module.  These must not be emitted in
    /// the output module; emitting them causes conflicting external-call
    /// signatures (e.g. bare `to_int` calling `__kea_char_to_int` with Dynamic
    /// I64 args while `Char.to_int` calls it with Char I32 args).
    overlay_names: BTreeSet<String>,
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
        let mut short_to_qualified: BTreeMap<String, Vec<String>> = BTreeMap::new();
        // Track unqualified names that have a concrete monomorphic definition so
        // we can prevent the routing table from accidentally sending those calls
        // to a polymorphic qualified variant (e.g. Result.unwrap_or) when a
        // user-defined monomorphic function with the same bare name exists.
        let mut mono_names: BTreeSet<String> = BTreeSet::new();

        // Pre-scan: collect the set of short names that have at least one
        // qualified counterpart (e.g., "eq" has "Int.eq", "Char.eq", …).
        // Bare functions whose short name appears here are merge artifacts
        // created by merge_modules_for_codegen and should be ignored —
        // regardless of whether their type is all-Dynamic or concrete.
        let qualified_short_names: BTreeSet<String> = module
            .declarations
            .iter()
            .filter_map(|d| {
                if let HirDecl::Function(f) = d {
                    f.name.rsplit_once('.').map(|(_, short)| short.to_string())
                } else {
                    None
                }
            })
            .collect();

        // Pre-scan: collect bare (unqualified) MONOMORPHIC function names.
        // Used below to guard mono_names short-name insertion: only short names
        // that have a bare MONOMORPHIC definition in this module should block the
        // polymorphic routing table.  Without this guard, qualified trait-dispatch
        // functions like `HasItem.fold` add `"fold"` to mono_names (because the
        // stdlib's bare `fold` is in bare_fn_names), incorrectly removing the
        // `fold → List.fold` routing and breaking recursive stdlib calls.
        // The stdlib's bare `fold` is POLYMORPHIC, so it is excluded here.
        let bare_mono_fn_names: BTreeSet<String> = module
            .declarations
            .iter()
            .filter_map(|d| {
                if let HirDecl::Function(f) = d {
                    if !f.name.contains('.') && free_type_vars(&f.ty).is_empty() {
                        Some(f.name.clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        for decl in &module.declarations {
            if let HirDecl::Function(f) = decl {
                // Skip bare overlay functions: any bare (unqualified) name
                // whose short form has qualified counterparts in the module
                // is a merge artifact, not a real definition.  Skipping it
                // preserves the short_to_qualified routing table for all callers.
                if !f.name.contains('.') && qualified_short_names.contains(&f.name) {
                    continue;
                }
                if !free_type_vars(&f.ty).is_empty() {
                    poly_fns.insert(f.name.clone(), f);
                    // Collect qualified name under its short name for call-site
                    // resolution.  We allow multiple qualified names per short
                    // name — ambiguity is resolved by type at the call site.
                    if let Some((_module, short)) = f.name.rsplit_once('.')
                        && !poly_fns.contains_key(short)
                    {
                        short_to_qualified
                            .entry(short.to_string())
                            .or_default()
                            .push(f.name.clone());
                    }
                } else {
                    // Monomorphic function: record its unqualified name so we can
                    // remove it from the routing table after the scan.
                    mono_names.insert(f.name.clone());
                    // Only add the short name when a bare function with that name
                    // actually exists in the module.  Without this guard, qualified
                    // trait-dispatch functions (e.g., `HasItem.fold`,
                    // `HasItem.NumberList.fold`) would add their short name `fold`
                    // to mono_names even when no bare `fold` is defined, causing
                    // the stdlib's `fold → List.fold` routing to be incorrectly
                    // removed and breaking recursive stdlib calls.
                    if let Some((_, short)) = f.name.rsplit_once('.')
                        && bare_mono_fn_names.contains(short)
                    {
                        mono_names.insert(short.to_string());
                    }
                }
            }
        }
        // If a concrete monomorphic function exists for a short name, remove
        // any qualified-poly mapping for that name.  Without this, a call to
        // `unwrap_or` in user code (resolved to the monomorphic definition
        // during merge) would be incorrectly re-routed to `Result.unwrap_or`
        // and then monomorphised under the wrong sum-type layout.
        short_to_qualified.retain(|short, _| !mono_names.contains(short));
        Self {
            module,
            poly_fns,
            short_to_qualified,
            overlay_names: qualified_short_names,
            generated: HashMap::new(),
            queue: VecDeque::new(),
            next_id: 0,
            specialized: Vec::new(),
        }
    }

    /// Resolve a bare call name (e.g. "zip") to the qualified polymorphic
    /// function that best matches the call site.
    ///
    /// Resolution order:
    ///
    /// 1. If `name` is already a fully-qualified key in `poly_fns`, return it.
    /// 2. If there is exactly one candidate, return it unambiguously.
    /// 3. Try type-based resolution: the candidate whose free type variables
    ///    are all covered by `extract_bindings` on the call-site arg types.
    /// 4. Same-module preference: if `caller_module` is provided, prefer the
    ///    candidate whose module prefix matches (handles recursive calls such
    ///    as `zip(rest, ys)` inside `List.zip` when `Option.zip` also exists).
    /// 5. Fallback: return the first candidate.
    fn resolve_poly_name(
        &self,
        name: &str,
        args: &[HirExpr],
        ret_ty: &Type,
        caller_module: Option<&str>,
    ) -> Option<String> {
        // Step 1: the name is already in poly_fns.
        //
        // If the caller is inside a named module and a qualified version of
        // this name exists for that module, prefer it.  This prevents bare
        // "zip" (which may be shadowed by Option.zip after module merging)
        // from being returned when the call is inside List.zip's body.
        if self.poly_fns.contains_key(name) {
            if let Some(module) = caller_module {
                let qualified = format!("{module}.{name}");
                if self.poly_fns.contains_key(qualified.as_str()) {
                    return Some(qualified);
                }
            }
            return Some(name.to_string());
        }
        let candidates = self.short_to_qualified.get(name)?;
        // Step 2: unambiguous.
        if candidates.len() == 1 {
            return Some(candidates[0].clone());
        }
        // Step 3: type-based resolution — pick the candidate whose free type
        // vars are all covered by bindings extracted from the call-site types.
        for candidate in candidates {
            if let Some(poly_fn) = self.poly_fns.get(candidate.as_str()) {
                let poly_free = free_type_vars(&poly_fn.ty);
                if poly_free.is_empty() {
                    continue;
                }
                if let Type::Function(ft) = &poly_fn.ty {
                    let mut bindings = BTreeMap::new();
                    for (poly_param, arg) in ft.params.iter().zip(args.iter()) {
                        extract_bindings(poly_param, &arg.ty, &mut bindings);
                    }
                    extract_bindings(&ft.ret, ret_ty, &mut bindings);
                    if poly_free.iter().all(|v| bindings.contains_key(v)) {
                        return Some(candidate.clone());
                    }
                }
            }
        }
        // Step 4: same-module preference.  Unqualified recursive calls inside
        // `List.zip` should prefer `List.zip` over `Option.zip` even when HIR
        // expression types are Dynamic (which prevents type-based resolution).
        if let Some(module) = caller_module {
            let prefix = format!("{module}.");
            if let Some(same_module) = candidates.iter().find(|c| c.starts_with(&prefix)) {
                return Some(same_module.clone());
            }
        }
        // Step 5: fallback.
        candidates.first().cloned()
    }

    fn run(&mut self) -> HirModule {
        // Phase 1: rewrite all function bodies, seeding the worklist.
        // Polymorphic functions are kept as fallbacks for call sites the pass
        // cannot rewrite (e.g., inside Raw expressions).
        let mut declarations: Vec<HirDecl> = Vec::new();
        for decl in &self.module.declarations {
            match decl {
                HirDecl::Function(f) => {
                    // Drop bare overlay functions with all-Dynamic types — they
                    // are merge artifacts whose env binding was lost and must
                    // not appear in the output module.  Emitting them produces
                    // conflicting external-call signatures (e.g. bare `to_int`
                    // calling `__kea_char_to_int` with I64 while `Char.to_int`
                    // calls it with I32).  Concrete-typed bare functions (e.g.
                    // `main`) are preserved.
                    if !f.name.contains('.')
                        && self.overlay_names.contains(&f.name)
                        && is_all_dynamic_overlay(f)
                    {
                        continue;
                    }
                    let name = f.name.clone();
                    let param_var_types = param_var_types(&f.params);
                    let rewritten = HirFunction {
                        name: name.clone(),
                        params: f.params.clone(),
                        body: self.rewrite_calls(&f.body, 0, &name, &param_var_types),
                        ty: f.ty.clone(),
                        effects: f.effects.clone(),
                        span: f.span,
                        is_fip: f.is_fip,
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
            specialized.name = mangled.clone();
            // Rewrite calls inside the specialized body (may enqueue more work).
            // Pass orig_name as the caller context so same-module preference
            // applies even within specializations (e.g., List.zip__0 should
            // still prefer List.* for its recursive calls).
            let spec_var_types = param_var_types(&specialized.params);
            specialized.body = self.rewrite_calls(&specialized.body, depth, &orig_name, &spec_var_types);
            self.specialized.push(specialized);
        }

        // Phase 3: append all specializations to the module.
        declarations.extend(self.specialized.drain(..).map(HirDecl::Function));

        HirModule { declarations }
    }

    /// Walk an expression tree, rewriting calls to polymorphic functions to
    /// their mangled specialized names and enqueueing specialization requests.
    ///
    /// `current_fn` is the fully-qualified name of the function whose body is
    /// being traversed.  It is used to extract the caller's module prefix for
    /// same-module name resolution (see `resolve_poly_name` step 4).
    ///
    /// `local_var_types` tracks names that are locally bound (function params,
    /// `let` binders, lambda params, case-pattern binders) at the current
    /// position in the expression tree, along with their concrete types when
    /// known (or `Type::Dynamic` when not).  A bare call whose name is locally
    /// bound must not be renamed to a qualified module path — that local
    /// binding shadows any global function with the same short name.
    ///
    /// Tracking types (not just names) enables the pass to resolve `Dynamic`
    /// argument types at call sites: e.g. when `xs` is bound as `List Int`
    /// from a `let xs = [1,2,3]`, a call `Foldable.count(xs)` where `xs.ty`
    /// is `Dynamic` in the HIR can still be specialised correctly.
    fn rewrite_calls(
        &mut self,
        expr: &HirExpr,
        depth: usize,
        current_fn: &str,
        local_var_types: &BTreeMap<String, Type>,
    ) -> HirExpr {
        let caller_module = current_fn.rsplit_once('.').map(|(module, _)| module);
        let kind = match &expr.kind {
            HirExprKind::Call { func, args } => {
                let rewritten_args: Vec<HirExpr> = args
                    .iter()
                    .map(|a| self.rewrite_calls(a, depth, current_fn, local_var_types))
                    .collect();
                let callee_name = match &func.kind {
                    HirExprKind::Var(name) => Some(name.as_str()),
                    _ => None,
                };
                // Resolve unqualified names like "filter" → "List.filter".
                // When multiple modules define the same short name (e.g. "zip"
                // in both List and Option), same-module preference picks the
                // candidate from the caller's module when types are ambiguous.
                let resolved_name = callee_name
                    .and_then(|name| self.resolve_poly_name(name, &rewritten_args, &expr.ty, caller_module));
                if let Some(ref resolved) = resolved_name
                    && let Some(poly_fn) = self.poly_fns.get(resolved.as_str())
                {
                    // Extract type variable bindings from call-site arg types.
                    let poly_ty = &poly_fn.ty;
                    if let Type::Function(ft) = poly_ty {
                        let mut bindings = BTreeMap::new();
                        for (poly_param, arg) in ft.params.iter().zip(rewritten_args.iter()) {
                            // When the HIR argument type is Dynamic but we have
                            // tracked a concrete type for the variable in
                            // local_var_types, use that concrete type for binding
                            // extraction.  This allows specialising calls like
                            // `Foldable.count(xs)` where `xs.ty = Dynamic` in
                            // the HIR but `xs` was bound as `List Int` in the
                            // enclosing block.
                            // When the arg type is Dynamic, try to recover a concrete
                            // type from the call site. Two sources:
                            // 1. Variable: look up its type in local_var_types.
                            // 2. Inline sum constructor (e.g. list literal `[1,2,3]`):
                            //    use the SumConstructor's sum_type name.  We don't
                            //    know element types here, but the sum name alone is
                            //    enough to specialize Foldable/Iterator dispatch.
                            let resolved_ty: Option<Type> = if matches!(arg.ty, Type::Dynamic) {
                                match &arg.kind {
                                    HirExprKind::Var(var_name) => {
                                        local_var_types.get(var_name.as_str()).cloned()
                                    }
                                    HirExprKind::SumConstructor { sum_type, .. } => {
                                        Some(Type::Sum(SumType {
                                            name: sum_type.clone(),
                                            type_args: vec![],
                                        }))
                                    }
                                    _ => None,
                                }
                            } else {
                                None
                            };
                            let effective_ty = resolved_ty.as_ref().unwrap_or(&arg.ty);
                            extract_bindings(poly_param, effective_ty, &mut bindings);
                        }
                        // Also extract from the return type if the call expr has
                        // a concrete type.
                        extract_bindings(&ft.ret, &expr.ty, &mut bindings);

                        // When the bare callee name is locally bound (lambda
                        // param, let-binder, case-pattern binder), the local
                        // value shadows the global function.  Skip renaming
                        // and specialization — just recurse on the original
                        // callee expression.
                        let bare_name_is_local =
                            callee_name.is_some_and(|n| local_var_types.contains_key(n));
                        if !bindings.is_empty()
                            && bindings.values().all(|t| free_type_vars(t).is_empty())
                            && !bare_name_is_local
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
                            // Incomplete bindings — cannot specialise.  Still
                            // rewrite the callee to the resolved qualified name
                            // so that bare-name collisions (e.g. "zip" resolved
                            // to "List.zip") do not dispatch to the wrong
                            // module's implementation at JIT link time.
                            //
                            // Exception: handled above — bare_name_is_local
                            // prevents renaming when the local value shadows
                            // the global function.
                            let callee_is_bare =
                                callee_name.is_some_and(|n| n != resolved.as_str());
                            let new_func = if callee_is_bare && !bare_name_is_local {
                                Box::new(HirExpr {
                                    kind: HirExprKind::Var(resolved.clone()),
                                    ty: func.ty.clone(),
                                    span: func.span,
                                })
                            } else {
                                Box::new(self.rewrite_calls(func, depth, current_fn, local_var_types))
                            };
                            HirExprKind::Call {
                                func: new_func,
                                args: rewritten_args,
                            }
                        }
                    } else {
                        HirExprKind::Call {
                            func: Box::new(self.rewrite_calls(func, depth, current_fn, local_var_types)),
                            args: rewritten_args,
                        }
                    }
                } else {
                    HirExprKind::Call {
                        func: Box::new(self.rewrite_calls(func, depth, current_fn, local_var_types)),
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
                    .map(|(n, e)| (n.clone(), self.rewrite_calls(e, depth, current_fn, local_var_types)))
                    .collect(),
            },

            HirExprKind::RecordUpdate {
                record_type,
                base,
                fields,
            } => HirExprKind::RecordUpdate {
                record_type: record_type.clone(),
                base: Box::new(self.rewrite_calls(base, depth, current_fn, local_var_types)),
                fields: fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.rewrite_calls(e, depth, current_fn, local_var_types)))
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
                    .map(|e| self.rewrite_calls(e, depth, current_fn, local_var_types))
                    .collect(),
            },

            HirExprKind::SumPayloadAccess {
                expr: inner,
                sum_type,
                variant,
                field_index,
            } => HirExprKind::SumPayloadAccess {
                expr: Box::new(self.rewrite_calls(inner, depth, current_fn, local_var_types)),
                sum_type: sum_type.clone(),
                variant: variant.clone(),
                field_index: *field_index,
            },

            HirExprKind::FieldAccess { expr: inner, field } => HirExprKind::FieldAccess {
                expr: Box::new(self.rewrite_calls(inner, depth, current_fn, local_var_types)),
                field: field.clone(),
            },

            HirExprKind::Binary { op, left, right } => HirExprKind::Binary {
                op: *op,
                left: Box::new(self.rewrite_calls(left, depth, current_fn, local_var_types)),
                right: Box::new(self.rewrite_calls(right, depth, current_fn, local_var_types)),
            },

            HirExprKind::Unary { op, operand } => HirExprKind::Unary {
                op: *op,
                operand: Box::new(self.rewrite_calls(operand, depth, current_fn, local_var_types)),
            },

            HirExprKind::Lambda { params, body } => {
                // Lambda params shadow any outer bindings with the same name.
                // We don't know the concrete types of lambda params here, so
                // insert them with Dynamic as a placeholder (they will still
                // mark the name as locally bound, preventing accidental
                // routing to a global function with the same short name).
                let mut lambda_var_types = local_var_types.clone();
                for p in params {
                    if let Some(name) = &p.name {
                        lambda_var_types.entry(name.clone()).or_insert(Type::Dynamic);
                    }
                }
                HirExprKind::Lambda {
                    params: params.clone(),
                    body: Box::new(self.rewrite_calls(body, depth, current_fn, &lambda_var_types)),
                }
            }

            HirExprKind::Catch { expr: inner } => HirExprKind::Catch {
                expr: Box::new(self.rewrite_calls(inner, depth, current_fn, local_var_types)),
            },

            HirExprKind::Handle {
                expr: inner,
                clauses,
                then_clause,
            } => HirExprKind::Handle {
                expr: Box::new(self.rewrite_calls(inner, depth, current_fn, local_var_types)),
                clauses: clauses
                    .iter()
                    .map(|c| {
                        // Handler clause args are locally bound within the clause body.
                        // We don't have concrete types for handler-clause pattern
                        // bindings here, so insert them as Dynamic.
                        let mut clause_var_types = local_var_types.clone();
                        for arg in &c.args {
                            collect_pattern_names_with_dynamic(arg, &mut clause_var_types);
                        }
                        HirHandleClause {
                            effect: c.effect.clone(),
                            operation: c.operation.clone(),
                            args: c.args.clone(),
                            arg_types: c.arg_types.clone(),
                            return_type: c.return_type.clone(),
                            continuation: c.continuation.clone(),
                            body: self.rewrite_calls(&c.body, depth, current_fn, &clause_var_types),
                            span: c.span,
                        }
                    })
                    .collect(),
                then_clause: then_clause
                    .as_ref()
                    .map(|e| Box::new(self.rewrite_calls(e, depth, current_fn, local_var_types))),
            },

            HirExprKind::Resume { value } => HirExprKind::Resume {
                value: Box::new(self.rewrite_calls(value, depth, current_fn, local_var_types)),
            },

            HirExprKind::Let { pattern, value } => HirExprKind::Let {
                pattern: pattern.clone(),
                value: Box::new(self.rewrite_calls(value, depth, current_fn, local_var_types)),
            },

            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => HirExprKind::If {
                condition: Box::new(self.rewrite_calls(condition, depth, current_fn, local_var_types)),
                then_branch: Box::new(self.rewrite_calls(then_branch, depth, current_fn, local_var_types)),
                else_branch: else_branch
                    .as_ref()
                    .map(|e| Box::new(self.rewrite_calls(e, depth, current_fn, local_var_types))),
            },

            // In a Block, Let binders from earlier items are in scope for
            // later items.  Walk items in order, extending local_var_types
            // after each Let.  We use the *rewritten* value type so that
            // concrete types (e.g. `List Int` from a list literal) propagate
            // to later uses, enabling the monomorphization of calls like
            // `Foldable.count(xs)` where `xs` was bound in the same block.
            HirExprKind::Block(exprs) => {
                let mut block_var_types = local_var_types.clone();
                let mut new_exprs = Vec::with_capacity(exprs.len());
                for e in exprs {
                    let rewritten = self.rewrite_calls(e, depth, current_fn, &block_var_types);
                    // After rewriting this item, add any names it binds so
                    // that subsequent items in the block see them as local.
                    // Use the rewritten value's concrete type when available.
                    if let HirExprKind::Let { pattern, value } = &rewritten.kind {
                        collect_let_binding_types(pattern, value.ty.clone(), &mut block_var_types);
                    }
                    new_exprs.push(rewritten);
                }
                HirExprKind::Block(new_exprs)
            }

            HirExprKind::Tuple(exprs) => HirExprKind::Tuple(
                exprs
                    .iter()
                    .map(|e| self.rewrite_calls(e, depth, current_fn, local_var_types))
                    .collect(),
            ),

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
// Helpers
// ---------------------------------------------------------------------------

/// Collect all variable names bound by a pattern into `out` (as a `BTreeSet`).
/// Used internally by `collect_let_binding_types` for complex patterns.
fn collect_pattern_names(pattern: &crate::HirPattern, out: &mut BTreeSet<String>) {
    match pattern {
        crate::HirPattern::Var(name) => {
            out.insert(name.clone());
        }
        crate::HirPattern::Raw(pat) => {
            let mut names = std::collections::HashSet::new();
            kea_ast::collect_pattern_bindings_pub(pat, &mut names);
            out.extend(names);
        }
    }
}

/// Collect all variable names bound by a pattern into a `BTreeMap<String,
/// Type>`, using `Type::Dynamic` for every name.  Used when we know a name
/// is locally bound but cannot determine its concrete type (e.g. lambda
/// params, handler-clause pattern bindings).
fn collect_pattern_names_with_dynamic(
    pattern: &crate::HirPattern,
    out: &mut BTreeMap<String, Type>,
) {
    let mut names = BTreeSet::new();
    collect_pattern_names(pattern, &mut names);
    for name in names {
        out.entry(name).or_insert(Type::Dynamic);
    }
}

/// Record let-binding types into `out`.
///
/// For a simple `Var` pattern the concrete value type is used directly,
/// which is the key enabler for specialising subsequent calls whose
/// argument types are `Dynamic` in the HIR (e.g. `let xs = [1,2,3]` gives
/// `xs → List Int`, so `Foldable.count(xs)` can be specialised to
/// `Foldable.count$m0$ListInt`).
///
/// For complex patterns (tuple destructuring, constructor patterns, etc.)
/// the pattern-bound names are inserted with `Type::Dynamic` — they are at
/// least marked as locally bound, preventing accidental routing to a global
/// function with the same short name.
fn collect_let_binding_types(
    pattern: &crate::HirPattern,
    value_ty: Type,
    out: &mut BTreeMap<String, Type>,
) {
    match pattern {
        crate::HirPattern::Var(name) => {
            out.insert(name.clone(), value_ty);
        }
        _ => {
            // Complex pattern: record all bound names as Dynamic.
            let mut names = BTreeSet::new();
            collect_pattern_names(pattern, &mut names);
            for name in names {
                out.entry(name).or_insert(Type::Dynamic);
            }
        }
    }
}

/// Extract parameter names (with `Type::Dynamic` placeholders) from a slice
/// of HIR function parameters.  The Dynamic placeholder marks each name as
/// locally bound; the Block handler will upgrade individual `let`-bound names
/// to concrete types as it encounters them during the traversal.
fn param_var_types(params: &[crate::HirParam]) -> BTreeMap<String, Type> {
    params
        .iter()
        .filter_map(|p| p.name.clone().map(|name| (name, Type::Dynamic)))
        .collect()
}

/// Returns true when a function's type is the all-Dynamic signature that HIR
/// lowering produces for bare overlay functions whose env binding was lost
/// after module scope cleanup.
///
/// Used in Phase 1 of `run()` to drop bare overlays that would produce
/// conflicting external-call signatures: e.g. a bare `to_int` with type
/// `fn(Dynamic) -> Dynamic` calling `__kea_char_to_int` with an I64 arg,
/// while `Char.to_int` calls it with an I32 arg.
///
/// Note: concrete-typed bare functions (e.g. `main`) must NOT be dropped —
/// this check intentionally excludes them by requiring all parameters and
/// the return type to be Dynamic.
fn is_all_dynamic_overlay(f: &HirFunction) -> bool {
    let Type::Function(ft) = &f.ty else {
        return false;
    };
    !ft.params.is_empty()
        && ft.params.iter().all(|p| matches!(p, Type::Dynamic))
        && matches!(ft.ret.as_ref(), Type::Dynamic)
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
        is_fip: f.is_fip,
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
                    arg_types: c.arg_types.iter().map(|t| subst.apply(t)).collect(),
                    return_type: subst.apply(&c.return_type),
                    continuation: c.continuation.clone(),
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
        (Type::Opaque { params: pp, .. }, Type::Opaque { params: cp, .. }) => {
            for (p, c) in pp.iter().zip(cp.iter()) {
                extract_bindings(p, c, out);
            }
        }
        (Type::Sum(ps), Type::Sum(cs)) => {
            for (p, c) in ps.type_args.iter().zip(cs.type_args.iter()) {
                extract_bindings(p, c, out);
            }
        }
        (Type::Record(pr), Type::Record(cr)) => {
            for (p, c) in pr.params.iter().zip(cr.params.iter()) {
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
        let poly = Type::list(Type::Var(var_a));
        let concrete = Type::list(Type::Int);
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
            is_fip: false,
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
            is_fip: false,
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

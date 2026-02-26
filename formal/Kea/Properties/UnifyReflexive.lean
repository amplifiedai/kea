/-
  Kea.Properties.UnifyReflexive — Unification reflexivity.

  Maps to Rust proptests:
    - `unify_reflexive_ground` (prop_tests.rs:180)
    - `unify_reflexive_row` (prop_tests.rs:188)

  Property: unify(t, t) always succeeds for any type.

  Key dependency: BEq reflexivity for mutual inductives (beqTy, beqRow,
  beqTyList, beqRowFields). Since `deriving BEq` doesn't work for mutual
  inductives, the manual BEq is defined in Ty.lean and reflexivity must
  be proved explicitly by structural induction.
-/

import Kea.Unify

private theorem beqIntWidth_refl (w : IntWidth) : (w == w) = true := by
  cases w <;> rfl

private theorem beqFloatWidth_refl (w : FloatWidth) : (w == w) = true := by
  cases w <;> rfl

private theorem beqSignedness_refl (s : Signedness) : (s == s) = true := by
  cases s <;> rfl

private theorem beqIntWidth_sound {w1 w2 : IntWidth} (h : (w1 == w2) = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> cases h <;> rfl

private theorem beqFloatWidth_sound {w1 w2 : FloatWidth} (h : (w1 == w2) = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> cases h <;> rfl

private theorem beqSignedness_sound {s1 s2 : Signedness} (h : (s1 == s2) = true) : s1 = s2 := by
  cases s1 <;> cases s2 <;> cases h <;> rfl

private theorem beqDim_refl_local (d : Dim) : (d == d) = true := by
  cases d with
  | const n =>
      simp [BEq.beq]
  | var v =>
      simp [BEq.beq]

private theorem beqDim_sound_local {d1 d2 : Dim} (h : (d1 == d2) = true) : d1 = d2 := by
  cases d1 with
  | const n =>
      cases d2 with
      | const m =>
          simp [BEq.beq] at h
          exact congrArg Dim.const h
      | var m =>
          simp [BEq.beq] at h
  | var n =>
      cases d2 with
      | const m =>
          simp [BEq.beq] at h
      | var m =>
          simp [BEq.beq] at h
          exact congrArg Dim.var h

private theorem beqDimList_refl_local : (ds : List Dim) → (ds == ds) = true
  | [] => by simp
  | d :: rest => by simp [beqDim_refl_local d, beqDimList_refl_local rest]

private theorem beqDimList_sound_local {ds1 ds2 : List Dim} (h : (ds1 == ds2) = true) : ds1 = ds2 := by
  induction ds1 generalizing ds2 with
  | nil =>
      cases ds2 <;> simp at h <;> rfl
  | cons d rest ih =>
      cases ds2 with
      | nil =>
          simp at h
      | cons d2 rest2 =>
          simp at h
          have hd := beqDim_sound_local h.1
          have hr := ih h.2
          subst hd
          subst hr
          rfl

-- =========================================================================
-- BEq reflexivity for mutual types
-- =========================================================================

-- BEq is reflexive for all four mutual type families.
-- Proved by structural induction following the beqTy/beqRow/etc definitions.
mutual
  theorem beqTy_refl : (t : Ty) → beqTy t t = true
    | .int => by simp [beqTy]
    | .intN w s => by
      simp [beqTy, beqIntWidth_refl w, beqSignedness_refl s]
    | .float => by simp [beqTy]
    | .floatN w => by
      simp [beqTy, beqFloatWidth_refl w]
    | .decimal p sc => by
      simp [beqTy, beqDim_refl_local p, beqDim_refl_local sc]
    | .bool => by simp [beqTy]
    | .string => by simp [beqTy]
    | .html => by simp [beqTy]
    | .markdown => by simp [beqTy]
    | .atom => by simp [beqTy]
    | .date => by simp [beqTy]
    | .dateTime => by simp [beqTy]
    | .unit => by simp [beqTy]
    | .dynamic => by simp [beqTy]
    | .var _ => by simp [beqTy]
    | .list inner => by simp [beqTy, beqTy_refl inner]
    | .set inner => by simp [beqTy, beqTy_refl inner]
    | .option inner => by simp [beqTy, beqTy_refl inner]
    | .existential bounds assoc => by simp [beqTy, beqTyList_refl assoc]
    | .fixedSizeList inner d => by
      simp [beqTy, beqTy_refl inner, beqDim_refl_local d]
    | .tensor inner shape => by
      simp [beqTy, beqTy_refl inner, beqDimList_refl_local shape]
    | .sum n args => by
      simp [beqTy, beqTyList_refl args]
    | .opaque n params => by
      simp [beqTy, beqTyList_refl params]
    | .dataframe inner => by simp [beqTy, beqTy_refl inner]
    | .column inner => by simp [beqTy, beqTy_refl inner]
    | .stream inner => by simp [beqTy, beqTy_refl inner]
    | .task inner => by simp [beqTy, beqTy_refl inner]
    | .actor inner => by simp [beqTy, beqTy_refl inner]
    | .arc inner => by simp [beqTy, beqTy_refl inner]
    | .map k v => by simp [beqTy, beqTy_refl k, beqTy_refl v]
    | .result ok err => by simp [beqTy, beqTy_refl ok, beqTy_refl err]
    | .record _ r => by simp [beqTy, beqRow_refl r]
    | .anonRecord r => by simp [beqTy, beqRow_refl r]
    | .row r => by simp [beqTy, beqRow_refl r]
    | .groupedFrame inner keys => by simp [beqTy, beqTy_refl inner]
    | .tagged inner tags => by simp [beqTy, beqTy_refl inner]
    | .function params ret => by simp [beqTy, beqTyList_refl params, beqTy_refl ret]
    | .forall vars body => by simp [beqTy, beqTy_refl body]
    | .app ctor args => by simp [beqTy, beqTy_refl ctor, beqTyList_refl args]
    | .constructor _ fixedArgs arity => by simp [beqTy, beqTyList_refl fixedArgs]
    | .tuple elems => by simp [beqTy, beqTyList_refl elems]

  theorem beqRow_refl : (r : Row) → beqRow r r = true
    | .mk fields rest => by simp [beqRow, beqRowFields_refl fields]

  theorem beqTyList_refl : (tl : TyList) → beqTyList tl tl = true
    | .nil => by simp [beqTyList]
    | .cons t rest => by simp [beqTyList, beqTy_refl t, beqTyList_refl rest]

  theorem beqRowFields_refl : (rf : RowFields) → beqRowFields rf rf = true
    | .nil => by simp [beqRowFields]
    | .cons l ty rest => by simp [beqRowFields, beqTy_refl ty, beqRowFields_refl rest]
end

-- =========================================================================
-- BEq soundness for mutual types — beqTy a b = true → a = b
-- =========================================================================

-- BEq is sound: if two types compare equal, they are propositionally equal.
-- This is the converse of beqTy_refl. Required for unifyConsistent (when
-- the BEq shortcut fires, we need propositional equality, not just Bool).
set_option maxHeartbeats 500000 in
mutual
  theorem beqTy_sound : (a b : Ty) → beqTy a b = true → a = b
    | .int, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .intN w1 s1, b, h => by
      cases b with
      | intN w2 s2 =>
        simp [beqTy] at h
        have hw := beqIntWidth_sound h.1
        have hs := beqSignedness_sound h.2
        subst hw; subst hs; rfl
      | _ => simp [beqTy] at h
    | .float, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .floatN w1, b, h => by
      cases b with
      | floatN w2 =>
        simp [beqTy] at h
        have hw := beqFloatWidth_sound h
        subst hw; rfl
      | _ => simp [beqTy] at h
    | .decimal p1 s1, b, h => by
      cases b with
      | decimal p2 s2 =>
        simp [beqTy] at h
        have hp := beqDim_sound_local h.1
        have hs := beqDim_sound_local h.2
        subst hp; subst hs; rfl
      | _ => simp [beqTy] at h
    | .bool, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .string, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .html, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .markdown, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .atom, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .date, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .dateTime, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .unit, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .dynamic, b, h => by
      cases b <;> simp [beqTy] at h <;> rfl
    | .list a, b, h => by
      cases b with
      | list b =>
        simp [beqTy] at h
        exact congrArg Ty.list (beqTy_sound a b h)
      | _ => simp [beqTy] at h
    | .map k1 v1, b, h => by
      cases b with
      | map k2 v2 =>
        simp [beqTy] at h
        have hk := beqTy_sound k1 k2 h.1
        have hv := beqTy_sound v1 v2 h.2
        subst hk; subst hv; rfl
      | _ => simp [beqTy] at h
    | .set a, b, h => by
      cases b with
      | set b =>
        simp [beqTy] at h
        exact congrArg Ty.set (beqTy_sound a b h)
      | _ => simp [beqTy] at h
    | .option a, b, h => by
      cases b with
      | option b =>
        simp [beqTy] at h
        exact congrArg Ty.option (beqTy_sound a b h)
      | _ => simp [beqTy] at h
    | .result ok1 err1, b, h => by
      cases b with
      | result ok2 err2 =>
        simp [beqTy] at h
        have hok := beqTy_sound ok1 ok2 h.1
        have herr := beqTy_sound err1 err2 h.2
        subst hok; subst herr; rfl
      | _ => simp [beqTy] at h
    | .existential bounds1 assoc1, b, h => by
      cases b with
      | existential bounds2 assoc2 =>
        simp [beqTy] at h
        have hb : bounds1 = bounds2 := h.1
        have ha := beqTyList_sound assoc1 assoc2 h.2
        subst hb; subst ha; rfl
      | _ => simp [beqTy] at h
    | .fixedSizeList inner1 d1, b, h => by
      cases b with
      | fixedSizeList inner2 d2 =>
        simp [beqTy] at h
        have hi := beqTy_sound inner1 inner2 h.1
        have hd := beqDim_sound_local h.2
        subst hi; subst hd; rfl
      | _ => simp [beqTy] at h
    | .tensor inner1 sh1, b, h => by
      cases b with
      | tensor inner2 sh2 =>
        simp [beqTy] at h
        have hi := beqTy_sound inner1 inner2 h.1
        have hs := beqDimList_sound_local h.2
        subst hi; subst hs; rfl
      | _ => simp [beqTy] at h
    | .sum n1 args1, b, h => by
      cases b with
      | sum n2 args2 =>
        simp [beqTy] at h
        have hn : n1 = n2 := h.1
        have ha := beqTyList_sound args1 args2 h.2
        subst hn; subst ha; rfl
      | _ => simp [beqTy] at h
    | .opaque n1 params1, b, h => by
      cases b with
      | «opaque» n2 params2 =>
        simp [beqTy] at h
        have hn : n1 = n2 := h.1
        have hp := beqTyList_sound params1 params2 h.2
        subst hn; subst hp; rfl
      | _ => simp [beqTy] at h
    | .record n1 r1, b, h => by
      cases b with
      | record n2 r2 =>
        simp [beqTy] at h
        have hn : n1 = n2 := h.1
        have hr := beqRow_sound r1 r2 h.2
        subst hn; subst hr; rfl
      | _ => simp [beqTy] at h
    | .anonRecord r1, b, h => by
      cases b with
      | anonRecord r2 =>
        simp [beqTy] at h
        exact congrArg Ty.anonRecord (beqRow_sound r1 r2 h)
      | _ => simp [beqTy] at h
    | .dataframe a, b, h => by
      cases b with
      | dataframe b =>
        simp [beqTy] at h
        exact congrArg Ty.dataframe (beqTy_sound a b h)
      | _ => simp [beqTy] at h
    | .column a, b, h => by
      cases b with
      | column b =>
        simp [beqTy] at h
        exact congrArg Ty.column (beqTy_sound a b h)
      | _ => simp [beqTy] at h
    | .stream a, b, h => by
      cases b with
      | stream b =>
        simp [beqTy] at h
        exact congrArg Ty.stream (beqTy_sound a b h)
      | _ => simp [beqTy] at h
    | .task a, b, h => by
      cases b with
      | task b =>
        simp [beqTy] at h
        exact congrArg Ty.task (beqTy_sound a b h)
      | _ => simp [beqTy] at h
    | .actor a, b, h => by
      cases b with
      | actor b =>
        simp [beqTy] at h
        exact congrArg Ty.actor (beqTy_sound a b h)
      | _ => simp [beqTy] at h
    | .arc a, b, h => by
      cases b with
      | arc b =>
        simp [beqTy] at h
        exact congrArg Ty.arc (beqTy_sound a b h)
      | _ => simp [beqTy] at h
    | .function p1 r1, b, h => by
      cases b with
      | function p2 r2 =>
        simp [beqTy] at h
        have hp := beqTyList_sound p1 p2 h.1
        have hr := beqTy_sound r1 r2 h.2
        subst hp; subst hr; rfl
      | _ => simp [beqTy] at h
    | .forall vars1 body1, b, h => by
      cases b with
      | «forall» vars2 body2 =>
        simp [beqTy] at h
        have hv : vars1 = vars2 := h.1
        have hb := beqTy_sound body1 body2 h.2
        subst hv; subst hb; rfl
      | _ => simp [beqTy] at h
    | .app f1 args1, b, h => by
      cases b with
      | app f2 args2 =>
        simp [beqTy] at h
        have hf := beqTy_sound f1 f2 h.1
        have ha := beqTyList_sound args1 args2 h.2
        subst hf; subst ha; rfl
      | _ => simp [beqTy] at h
    | .constructor n1 fixed1 arity1, b, h => by
      cases b with
      | constructor n2 fixed2 arity2 =>
        simp [beqTy] at h
        have hn : n1 = n2 := h.1.1
        have hf := beqTyList_sound fixed1 fixed2 h.1.2
        have ha : arity1 = arity2 := h.2
        subst hn; subst hf; subst ha; rfl
      | _ => simp [beqTy] at h
    | .var v1, b, h => by
      cases b with
      | var v2 =>
        simp [beqTy] at h
        exact congrArg Ty.var h
      | _ => simp [beqTy] at h
    | .row r1, b, h => by
      cases b with
      | row r2 =>
        simp [beqTy] at h
        exact congrArg Ty.row (beqRow_sound r1 r2 h)
      | _ => simp [beqTy] at h
    | .groupedFrame inner1 keys1, b, h => by
      cases b with
      | groupedFrame inner2 keys2 =>
        simp [beqTy] at h
        have hi := beqTy_sound inner1 inner2 h.1
        have hk : keys1 = keys2 := h.2
        subst hi; subst hk; rfl
      | _ => simp [beqTy] at h
    | .tagged inner1 tags1, b, h => by
      cases b with
      | tagged inner2 tags2 =>
        simp [beqTy] at h
        have hi := beqTy_sound inner1 inner2 h.1
        have ht : tags1 = tags2 := h.2
        subst hi; subst ht; rfl
      | _ => simp [beqTy] at h
    | .tuple e1, b, h => by
      cases b with
      | tuple e2 =>
        simp [beqTy] at h
        exact congrArg Ty.tuple (beqTyList_sound e1 e2 h)
      | _ => simp [beqTy] at h

  theorem beqRow_sound : (a b : Row) → beqRow a b = true → a = b
    | .mk f1 r1, .mk f2 r2, h => by
      simp [beqRow] at h
      have hf := beqRowFields_sound f1 f2 h.1
      have hr : r1 = r2 := by
        match r1, r2, h.2 with
        | none, none, _ => rfl
        | some v1, some v2, heq => simp_all
      subst hf; subst hr; rfl

  theorem beqTyList_sound : (a b : TyList) → beqTyList a b = true → a = b
    | .nil, .nil, _ => rfl
    | .cons t1 r1, .cons t2 r2, h => by
      simp [beqTyList] at h
      have ht := beqTy_sound t1 t2 h.1
      have hr := beqTyList_sound r1 r2 h.2
      subst ht; subst hr; rfl
    | .nil, .cons _ _, h => by simp [beqTyList] at h
    | .cons _ _, .nil, h => by simp [beqTyList] at h

  theorem beqRowFields_sound : (a b : RowFields) → beqRowFields a b = true → a = b
    | .nil, .nil, _ => rfl
    | .cons l1 t1 r1, .cons l2 t2 r2, h => by
      simp [beqRowFields] at h
      -- beqRowFields is (l1 == l2 && beqTy t1 t2) && beqRowFields r1 r2
      -- so h is ((l1 = l2 ∧ beqTy t1 t2 = true) ∧ beqRowFields r1 r2 = true)
      have hl : l1 = l2 := h.1.1
      have ht := beqTy_sound t1 t2 h.1.2
      have hr := beqRowFields_sound r1 r2 h.2
      subst hl; subst ht; subst hr; rfl
    | .nil, .cons _ _ _, h => by simp [beqRowFields] at h
    | .cons _ _ _, .nil, h => by simp [beqRowFields] at h
end

-- =========================================================================
-- Unification reflexivity
-- =========================================================================

/-- Unifying any type with itself succeeds, returning the same state.
    The proof is immediate: unify applies the substitution to both sides
    (producing identical results), the BEq check succeeds, and .ok st
    is returned without any state changes. -/
theorem unifyReflexive (st : UnifyState) (fuel : Nat) (ty : Ty) :
    ∃ st', unify st (fuel + 1) ty ty = .ok st' := by
  refine ⟨st, ?_⟩
  simp only [unify]
  -- The if condition uses == (BEq.beq), bridge to beqTy
  have h : (applySubst st.subst fuel ty == applySubst st.subst fuel ty) = true := by
    show beqTy _ _ = true
    exact beqTy_refl _
  simp [h]

/-- Non-existential form: unifying any type with itself returns the same state.
    Useful as a rewriting lemma (not just an existence claim). -/
theorem unifyReflexive' (st : UnifyState) (fuel : Nat) (ty : Ty) :
    unify st (fuel + 1) ty ty = .ok st := by
  simp only [unify]
  have h : (applySubst st.subst fuel ty == applySubst st.subst fuel ty) = true := by
    show beqTy _ _ = true
    exact beqTy_refl _
  simp [h]

-- =========================================================================
-- Helper: applySubstRowFields preserves field count
-- =========================================================================

/-- Applying a substitution to row fields preserves the number of fields.
    Each field's type may change, but no fields are added or removed. -/
theorem applySubstRowFields_preserves_length (s : Subst) (fuel : Nat) (rf : RowFields) :
    RowFields.length (applySubstRowFields s fuel rf) = RowFields.length rf := by
  match fuel with
  | 0 => rfl
  | fuel + 1 =>
    match rf with
    | .nil => rfl
    | .cons _ _ rest =>
      simp only [applySubstRowFields, RowFields.length]
      have ih := applySubstRowFields_preserves_length s fuel rest
      omega

-- unifyRowsReflexive: see DecomposeFields.lean (co-located with
-- unifyRowsReflexive' to avoid circular imports).

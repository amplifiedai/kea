import Kea.Typing

/-
  Kea.Eval — Minimal evaluator spike.

  This is a deliberately small semantics module used as a first step toward
  evaluator-side metatheory (progress/preservation) outside unification proofs.
-/

/-- Runtime values for a minimal core evaluator fragment. -/
inductive Value : Type where
  | int : Int → Value
  | bool : Bool → Value
  | string : String → Value
  | record : List (Label × Value) → Value

/-- Runtime field payload for anonymous records. -/
abbrev ValueFields := List (Label × Value)

mutual
  /-- Runtime value typing relation for evaluator-side preservation lemmas. -/
  inductive ValueHasType : Value → Ty → Prop where
    | int (n : Int) : ValueHasType (.int n) .int
    | bool (b : Bool) : ValueHasType (.bool b) .bool
    | string (s : String) : ValueHasType (.string s) .string
    | record (fields : ValueFields) (rowFields : RowFields)
        (h_fields : ValueFieldsHasType fields rowFields) :
        ValueHasType (.record fields) (.anonRecord (.mk rowFields none))

  /-- Runtime field payload typing for record literals. -/
  inductive ValueFieldsHasType : ValueFields → RowFields → Prop where
    | nil : ValueFieldsHasType [] .nil
    | cons (label : Label) (v : Value) (rest : ValueFields) (ty : Ty) (restFields : RowFields)
        (h_head : ValueHasType v ty)
        (h_rest : ValueFieldsHasType rest restFields) :
        ValueFieldsHasType ((label, v) :: rest) (.cons label ty restFields)
end

namespace ValueFields

/-- Lookup a field value by label (first match wins). -/
def get (fields : ValueFields) (label : Label) : Option Value :=
  match fields with
  | [] => none
  | (l, v) :: rest => if l == label then some v else get rest label

end ValueFields

/-- Runtime environment for evaluation. -/
abbrev ValueEnv := List (String × Value)

namespace ValueEnv

/-- Lookup a runtime binding by name (first binding wins). -/
def lookup (env : ValueEnv) (name : String) : Option Value :=
  match env with
  | [] => none
  | (n, v) :: rest => if n == name then some v else lookup rest name

end ValueEnv

mutual
  /-- Minimal evaluator for literals, vars, let, records, and projection. -/
  def eval (env : ValueEnv) : CoreExpr → Option Value
    | .intLit n => some (.int n)
    | .boolLit b => some (.bool b)
    | .stringLit s => some (.string s)
    | .var name => ValueEnv.lookup env name
    | .letE name value body =>
      match eval env value with
      | none => none
      | some v => eval ((name, v) :: env) body
    | .record fs =>
      match evalFields env fs with
      | none => none
      | some vfs => some (.record vfs)
    | .proj recv label =>
      match eval env recv with
      | some (.record vfs) => ValueFields.get vfs label
      | _ => none
    -- The evaluator spike keeps lambdas non-values, but executes direct beta app-lam.
    | .lam _ _ _ => none
    | .app (.lam param _ body) arg =>
      match eval env arg with
      | none => none
      | some v => eval ((param, v) :: env) body
    | .app _ _ => none

  /-- Field evaluator for record literals. -/
  def evalFields (env : ValueEnv) : CoreFields → Option ValueFields
    | .nil => some []
    | .cons label e rest =>
      match eval env e, evalFields env rest with
      | some v, some vrest => some ((label, v) :: vrest)
      | _, _ => none
end

/-- Evaluator is deterministic by definition on expressions. -/
theorem eval_deterministic
    (env : ValueEnv) (e : CoreExpr) {v1 v2 : Value}
    (h1 : eval env e = some v1) (h2 : eval env e = some v2) :
    v1 = v2 := by
  rw [h1] at h2
  cases h2
  rfl

/-- Field evaluator is deterministic by definition on field lists. -/
theorem evalFields_deterministic
    (env : ValueEnv) (fs : CoreFields) {vfs1 vfs2 : ValueFields}
    (h1 : evalFields env fs = some vfs1)
    (h2 : evalFields env fs = some vfs2) :
    vfs1 = vfs2 := by
  rw [h1] at h2
  cases h2
  rfl

/-- Record/projection round-trip: projection from a directly evaluated record
    agrees with field lookup on the evaluated field payload. -/
theorem eval_proj_of_record
    (env : ValueEnv) (fs : CoreFields) (label : Label) (vfs : ValueFields) (v : Value)
    (h_fields : evalFields env fs = some vfs)
    (h_get : ValueFields.get vfs label = some v) :
    eval env (.proj (.record fs) label) = some v := by
  simp [eval, h_fields, h_get]

/-- Evaluator progress on literals (timeboxed first progress theorem). -/
theorem eval_progress_lit (env : ValueEnv) (n : Int) :
    ∃ v, eval env (.intLit n) = some v := by
  exact ⟨.int n, by simp [eval]⟩

/-- Evaluator progress on boolean literals. -/
theorem eval_progress_bool (env : ValueEnv) (b : Bool) :
    ∃ v, eval env (.boolLit b) = some v := by
  exact ⟨.bool b, by simp [eval]⟩

/-- Evaluator progress on string literals. -/
theorem eval_progress_string (env : ValueEnv) (s : String) :
    ∃ v, eval env (.stringLit s) = some v := by
  exact ⟨.string s, by simp [eval]⟩

/-- Runtime environment coverage assumption for variable progress. -/
def EnvCovers (tenv : TermEnv) (venv : ValueEnv) : Prop :=
  ∀ name ty, TermEnv.lookup tenv name = some ty →
    ∃ v, ValueEnv.lookup venv name = some v

/-- Runtime environment typing assumption for evaluator preservation lemmas. -/
def EnvTyped (tenv : TermEnv) (venv : ValueEnv) : Prop :=
  ∀ name ty, TermEnv.lookup tenv name = some ty →
    ∃ v, ValueEnv.lookup venv name = some v ∧ ValueHasType v ty

/-- Runtime environment is type-aligned with the term environment. -/
abbrev EnvWellTyped := EnvTyped

/-- A typed runtime environment always covers term-environment lookups. -/
theorem envCovers_of_envTyped
    {tenv : TermEnv} {venv : ValueEnv}
    (h_typed : EnvTyped tenv venv) :
    EnvCovers tenv venv := by
  intro name ty h_lookup
  rcases h_typed name ty h_lookup with ⟨v, h_vlookup, _h_vty⟩
  exact ⟨v, h_vlookup⟩

/-- Typed variable progress under runtime environment coverage. -/
theorem eval_progress_var_of_envCovers
    {tenv : TermEnv} {venv : ValueEnv} {name : String} {ty : Ty}
    (h_cover : EnvCovers tenv venv)
    (h_ty : HasType tenv (.var name) ty) :
    ∃ v, eval venv (.var name) = some v := by
  cases h_ty with
  | var _ _ _ h_lookup =>
    rcases h_cover name ty h_lookup with ⟨v, h_v⟩
    exact ⟨v, by simpa [eval] using h_v⟩

/-- Preservation on variables under typed runtime environment assumptions. -/
theorem eval_preserves_var_of_envTyped
    {tenv : TermEnv} {venv : ValueEnv} {name : String} {ty : Ty} {v : Value}
    (h_env : EnvTyped tenv venv)
    (h_ty : HasType tenv (.var name) ty)
    (h_eval : eval venv (.var name) = some v) :
    ValueHasType v ty := by
  cases h_ty with
  | var _ _ _ h_lookup =>
    rcases h_env name ty h_lookup with ⟨v', h_vlookup, h_vty⟩
    simp [eval, h_vlookup] at h_eval
    rcases h_eval with rfl
    exact h_vty

/-- Variable progress under the `EnvWellTyped` alias. -/
theorem eval_progress_var_of_envWellTyped
    {tenv : TermEnv} {venv : ValueEnv} {name : String} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv (.var name) ty) :
    ∃ v, eval venv (.var name) = some v := by
  exact eval_progress_var_of_envCovers (envCovers_of_envTyped h_env) h_ty

/-- Let-step compatibility with evaluator composition. -/
theorem eval_let_of_eval_steps
    (env : ValueEnv) (name : String) (value body : CoreExpr) (vv vb : Value)
    (h_value : eval env value = some vv)
    (h_body : eval ((name, vv) :: env) body = some vb) :
    eval env (.letE name value body) = some vb := by
  simp [eval, h_value, h_body]

/-- Record-step compatibility with field evaluator composition. -/
theorem eval_record_of_evalFields
    (env : ValueEnv) (fs : CoreFields) (vfs : ValueFields)
    (h_fields : evalFields env fs = some vfs) :
    eval env (.record fs) = some (.record vfs) := by
  simp [eval, h_fields]

/-- Atomic evaluator fragment (literals + vars). -/
inductive EvalAtomicExpr : CoreExpr → Prop where
  | intLit (n : Int) : EvalAtomicExpr (.intLit n)
  | boolLit (b : Bool) : EvalAtomicExpr (.boolLit b)
  | stringLit (s : String) : EvalAtomicExpr (.stringLit s)
  | var (name : String) : EvalAtomicExpr (.var name)

mutual
  /-- Expressions evaluable by `eval` in the current fragment (`lam`/`app` excluded). -/
  inductive EvalFragmentExpr : CoreExpr → Prop where
    | intLit (n : Int) : EvalFragmentExpr (.intLit n)
    | boolLit (b : Bool) : EvalFragmentExpr (.boolLit b)
    | stringLit (s : String) : EvalFragmentExpr (.stringLit s)
    | var (name : String) : EvalFragmentExpr (.var name)
    | letE (name : String) (value body : CoreExpr)
        (h_value : EvalFragmentExpr value)
        (h_body : EvalFragmentExpr body) :
        EvalFragmentExpr (.letE name value body)
    | record (fs : CoreFields) (h_fs : EvalFragmentFields fs) :
        EvalFragmentExpr (.record fs)
    | proj (recv : CoreExpr) (label : Label)
        (h_recv : EvalFragmentExpr recv) :
        EvalFragmentExpr (.proj recv label)

  /-- Field-level evaluator fragment predicate. -/
  inductive EvalFragmentFields : CoreFields → Prop where
    | nil : EvalFragmentFields .nil
    | cons (label : Label) (e : CoreExpr) (rest : CoreFields)
        (h_e : EvalFragmentExpr e)
        (h_rest : EvalFragmentFields rest) :
        EvalFragmentFields (.cons label e rest)
end

/-- Atomic fragment embeds into the evaluator fragment. -/
theorem evalAtomicExpr_implies_evalFragment {e : CoreExpr}
    (h_atomic : EvalAtomicExpr e) : EvalFragmentExpr e := by
  cases h_atomic with
  | intLit n => exact EvalFragmentExpr.intLit n
  | boolLit b => exact EvalFragmentExpr.boolLit b
  | stringLit s => exact EvalFragmentExpr.stringLit s
  | var name => exact EvalFragmentExpr.var name

/-- Field-typing lookup compatibility between runtime records and row fields. -/
theorem valueFieldsHasType_get
    {fields : ValueFields} {rowFields : RowFields} {label : Label} {ty : Ty}
    (h_fields : ValueFieldsHasType fields rowFields)
    (h_get : RowFields.get rowFields label = some ty) :
    ∃ v, ValueFields.get fields label = some v ∧ ValueHasType v ty := by
  induction fields generalizing rowFields ty with
  | nil =>
    cases h_fields
    simp [RowFields.get] at h_get
  | cons head rest ih =>
    cases head with
    | mk l v =>
      cases h_fields with
      | cons _ _ _ _ _ h_head h_rest =>
        by_cases h_eq : l = label
        · subst h_eq
          simp [RowFields.get] at h_get
          cases h_get
          exact ⟨v, by simp [ValueFields.get], h_head⟩
        · simp [RowFields.get, h_eq] at h_get
          rcases ih h_rest h_get with ⟨v', h_lookup, h_vty⟩
          exact ⟨v', by simp [ValueFields.get, h_eq, h_lookup], h_vty⟩

/-- Extend typed environment alignment with one fresh head binding. -/
theorem envWellTyped_cons
    {tenv : TermEnv} {venv : ValueEnv}
    {name : String} {ty : Ty} {v : Value}
    (h_env : EnvWellTyped tenv venv)
    (h_head : ValueHasType v ty) :
    EnvWellTyped ((name, ty) :: tenv) ((name, v) :: venv) := by
  intro name' ty' h_lookup
  by_cases h_name : name = name'
  · subst h_name
    simp [TermEnv.lookup] at h_lookup
    cases h_lookup
    exact ⟨v, by simp [ValueEnv.lookup, h_head]⟩
  · simp [TermEnv.lookup, h_name] at h_lookup
    rcases h_env name' ty' h_lookup with ⟨v', h_vlookup, h_vty⟩
    exact ⟨v', by simp [ValueEnv.lookup, h_name, h_vlookup, h_vty]⟩

mutual
  /--
  Executable soundness for the evaluator fragment (`lam`/`app` excluded):
  if an expression is well-typed and in the fragment, evaluation produces a
  runtime value with the same type.
  -/
  theorem eval_sound_evalFragment
      {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
      (h_env : EnvWellTyped tenv venv)
      (h_ty : HasType tenv e ty)
      (h_frag : EvalFragmentExpr e) :
      ∃ v, eval venv e = some v ∧ ValueHasType v ty := by
    exact EvalFragmentExpr.rec
      (motive_1 := fun e _ =>
        ∀ {tenv : TermEnv} {venv : ValueEnv} {ty : Ty},
          EnvWellTyped tenv venv →
          HasType tenv e ty →
          ∃ v, eval venv e = some v ∧ ValueHasType v ty)
      (motive_2 := fun fs _ =>
        ∀ {tenv : TermEnv} {venv : ValueEnv} {rowFields : RowFields},
          EnvWellTyped tenv venv →
          HasFieldsType tenv fs rowFields →
          ∃ vfs, evalFields venv fs = some vfs ∧ ValueFieldsHasType vfs rowFields)
      (intLit := by
        intro n tenv venv ty _h_env h_ty
        cases h_ty with
        | int =>
          exact ⟨.int n, by simp [eval, ValueHasType.int]⟩)
      (boolLit := by
        intro b tenv venv ty _h_env h_ty
        cases h_ty with
        | bool =>
          exact ⟨.bool b, by simp [eval, ValueHasType.bool]⟩)
      (stringLit := by
        intro s tenv venv ty _h_env h_ty
        cases h_ty with
        | string =>
          exact ⟨.string s, by simp [eval, ValueHasType.string]⟩)
      (var := by
        intro name tenv venv ty h_env h_ty
        cases h_ty with
        | var _ _ _ h_lookup =>
          rcases h_env name ty h_lookup with ⟨v, h_vlookup, h_vty⟩
          exact ⟨v, by simp [eval, h_vlookup, h_vty]⟩)
      (letE := by
        intro name value body h_value h_body ih_value ih_body tenv venv ty h_env h_ty
        cases h_ty with
        | letE _ _ _ _ valueTy _ h_value_ty h_body_ty =>
          rcases ih_value h_env h_value_ty with ⟨vv, h_eval_value, h_vv_ty⟩
          have h_env' : EnvWellTyped ((name, valueTy) :: tenv) ((name, vv) :: venv) :=
            envWellTyped_cons h_env h_vv_ty
          rcases ih_body h_env' h_body_ty with ⟨vb, h_eval_body, h_vb_ty⟩
          exact ⟨vb, by simpa [eval, h_eval_value] using h_eval_body, h_vb_ty⟩)
      (record := by
        intro fs h_fs ih_fs tenv venv ty h_env h_ty
        cases h_ty with
        | record _ _ rowFields h_fields_ty =>
          rcases ih_fs h_env h_fields_ty with ⟨vfs, h_eval_fields, h_vfs_ty⟩
          exact ⟨.record vfs, by simp [eval, h_eval_fields, ValueHasType.record, h_vfs_ty]⟩)
      (proj := by
        intro recv label h_recv ih_recv tenv venv ty h_env h_ty
        cases h_ty with
        | proj _ _ rowFields _ _ h_recv_ty h_get =>
          rcases ih_recv h_env h_recv_ty with ⟨vrecv, h_eval_recv, h_vrecv_ty⟩
          cases h_vrecv_ty with
          | record vfs rowFields' h_vfs =>
            rcases valueFieldsHasType_get h_vfs (by simpa using h_get) with
              ⟨v, h_field_lookup, h_vty⟩
            exact ⟨v, by simp [eval, h_eval_recv, h_field_lookup], h_vty⟩)
      (nil := by
        intro tenv venv rowFields _h_env h_ty
        cases h_ty with
        | nil =>
          exact ⟨[], by simp [evalFields, ValueFieldsHasType.nil]⟩)
      (cons := by
        intro label e rest h_e h_rest ih_e ih_rest tenv venv rowFields h_env h_ty
        cases h_ty with
        | cons _ _ _ _ ty restFields h_head h_tail =>
          rcases ih_e h_env h_head with ⟨v, h_eval_head, h_vty⟩
          rcases ih_rest h_env h_tail with ⟨vrest, h_eval_rest, h_rest_ty⟩
          exact ⟨(label, v) :: vrest, by
            simp [evalFields, h_eval_head, h_eval_rest, ValueFieldsHasType.cons, h_vty, h_rest_ty]⟩)
      h_frag h_env h_ty

  /-- Field-level executable soundness for the evaluator fragment. -/
  theorem evalFields_sound_evalFragment
      {tenv : TermEnv} {venv : ValueEnv} {fs : CoreFields} {rowFields : RowFields}
      (h_env : EnvWellTyped tenv venv)
      (h_ty : HasFieldsType tenv fs rowFields)
      (h_frag : EvalFragmentFields fs) :
      ∃ vfs, evalFields venv fs = some vfs ∧ ValueFieldsHasType vfs rowFields := by
    exact EvalFragmentFields.rec
      (motive_1 := fun e _ =>
        ∀ {tenv : TermEnv} {venv : ValueEnv} {ty : Ty},
          EnvWellTyped tenv venv →
          HasType tenv e ty →
          ∃ v, eval venv e = some v ∧ ValueHasType v ty)
      (motive_2 := fun fs _ =>
        ∀ {tenv : TermEnv} {venv : ValueEnv} {rowFields : RowFields},
          EnvWellTyped tenv venv →
          HasFieldsType tenv fs rowFields →
          ∃ vfs, evalFields venv fs = some vfs ∧ ValueFieldsHasType vfs rowFields)
      (intLit := by
        intro n tenv venv ty _h_env h_ty
        cases h_ty with
        | int =>
          exact ⟨.int n, by simp [eval, ValueHasType.int]⟩)
      (boolLit := by
        intro b tenv venv ty _h_env h_ty
        cases h_ty with
        | bool =>
          exact ⟨.bool b, by simp [eval, ValueHasType.bool]⟩)
      (stringLit := by
        intro s tenv venv ty _h_env h_ty
        cases h_ty with
        | string =>
          exact ⟨.string s, by simp [eval, ValueHasType.string]⟩)
      (var := by
        intro name tenv venv ty h_env h_ty
        cases h_ty with
        | var _ _ _ h_lookup =>
          rcases h_env name ty h_lookup with ⟨v, h_vlookup, h_vty⟩
          exact ⟨v, by simp [eval, h_vlookup, h_vty]⟩)
      (letE := by
        intro name value body h_value h_body ih_value ih_body tenv venv ty h_env h_ty
        cases h_ty with
        | letE _ _ _ _ valueTy _ h_value_ty h_body_ty =>
          rcases ih_value h_env h_value_ty with ⟨vv, h_eval_value, h_vv_ty⟩
          have h_env' : EnvWellTyped ((name, valueTy) :: tenv) ((name, vv) :: venv) :=
            envWellTyped_cons h_env h_vv_ty
          rcases ih_body h_env' h_body_ty with ⟨vb, h_eval_body, h_vb_ty⟩
          exact ⟨vb, by simpa [eval, h_eval_value] using h_eval_body, h_vb_ty⟩)
      (record := by
        intro fs h_fs ih_fs tenv venv ty h_env h_ty
        cases h_ty with
        | record _ _ rowFields h_fields_ty =>
          rcases ih_fs h_env h_fields_ty with ⟨vfs, h_eval_fields, h_vfs_ty⟩
          exact ⟨.record vfs, by simp [eval, h_eval_fields, ValueHasType.record, h_vfs_ty]⟩)
      (proj := by
        intro recv label h_recv ih_recv tenv venv ty h_env h_ty
        cases h_ty with
        | proj _ _ rowFields _ _ h_recv_ty h_get =>
          rcases ih_recv h_env h_recv_ty with ⟨vrecv, h_eval_recv, h_vrecv_ty⟩
          cases h_vrecv_ty with
          | record vfs rowFields' h_vfs =>
            rcases valueFieldsHasType_get h_vfs (by simpa using h_get) with
              ⟨v, h_field_lookup, h_vty⟩
            exact ⟨v, by simp [eval, h_eval_recv, h_field_lookup], h_vty⟩)
      (nil := by
        intro tenv venv rowFields _h_env h_ty
        cases h_ty with
        | nil =>
          exact ⟨[], by simp [evalFields, ValueFieldsHasType.nil]⟩)
      (cons := by
        intro label e rest h_e h_rest ih_e ih_rest tenv venv rowFields h_env h_ty
        cases h_ty with
        | cons _ _ _ _ ty restFields h_head h_tail =>
          rcases ih_e h_env h_head with ⟨v, h_eval_head, h_vty⟩
          rcases ih_rest h_env h_tail with ⟨vrest, h_eval_rest, h_rest_ty⟩
          exact ⟨(label, v) :: vrest, by
            simp [evalFields, h_eval_head, h_eval_rest, ValueFieldsHasType.cons, h_vty, h_rest_ty]⟩)
      h_frag h_env h_ty
end

/--
End-to-end executable soundness slice for the current evaluator fragment.
-/
theorem inferEval_sound_evalFragment
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_infer : inferExpr tenv e = some ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentExpr e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty := by
  have h_ty : HasType tenv e ty := inferExpr_sound tenv e ty h_infer
  exact eval_sound_evalFragment h_env h_ty h_frag

/-- Beta-step compatibility for direct app-lam evaluation. -/
theorem eval_app_lam_of_eval_arg
    (env : ValueEnv) (param : String) (paramTy : Ty) (body arg : CoreExpr) (vArg out : Value)
    (h_arg : eval env arg = some vArg)
    (h_body : eval ((param, vArg) :: env) body = some out) :
    eval env (.app (.lam param paramTy body) arg) = some out := by
  simp [eval, h_arg, h_body]

mutual
  /-- Executable fragment with beta-style app-lam and no first-class functions. -/
  inductive EvalFragmentFull : CoreExpr → Prop where
    | intLit (n : Int) : EvalFragmentFull (.intLit n)
    | boolLit (b : Bool) : EvalFragmentFull (.boolLit b)
    | stringLit (s : String) : EvalFragmentFull (.stringLit s)
    | var (name : String) : EvalFragmentFull (.var name)
    | appLam (param : String) (paramTy : Ty) (body arg : CoreExpr)
        (h_body : EvalFragmentFull body)
        (h_arg : EvalFragmentFull arg) :
        EvalFragmentFull (.app (.lam param paramTy body) arg)
    | letE (name : String) (value body : CoreExpr)
        (h_value : EvalFragmentFull value)
        (h_body : EvalFragmentFull body) :
        EvalFragmentFull (.letE name value body)
    | record (fs : CoreFields) (h_fs : EvalFragmentFullFields fs) :
        EvalFragmentFull (.record fs)
    | proj (recv : CoreExpr) (label : Label)
        (h_recv : EvalFragmentFull recv) :
        EvalFragmentFull (.proj recv label)

  /-- Field-level companion for `EvalFragmentFull`. -/
  inductive EvalFragmentFullFields : CoreFields → Prop where
    | nil : EvalFragmentFullFields .nil
    | cons (label : Label) (e : CoreExpr) (rest : CoreFields)
        (h_e : EvalFragmentFull e)
        (h_rest : EvalFragmentFullFields rest) :
        EvalFragmentFullFields (.cons label e rest)
end

mutual
  /-- Executable soundness for `EvalFragmentFull`. -/
  theorem eval_sound_evalFragmentFull
      {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
      (h_env : EnvWellTyped tenv venv)
      (h_ty : HasType tenv e ty)
      (h_frag : EvalFragmentFull e) :
      ∃ v, eval venv e = some v ∧ ValueHasType v ty := by
    exact EvalFragmentFull.rec
      (motive_1 := fun e _ =>
        ∀ {tenv : TermEnv} {venv : ValueEnv} {ty : Ty},
          EnvWellTyped tenv venv →
          HasType tenv e ty →
          ∃ v, eval venv e = some v ∧ ValueHasType v ty)
      (motive_2 := fun fs _ =>
        ∀ {tenv : TermEnv} {venv : ValueEnv} {rowFields : RowFields},
          EnvWellTyped tenv venv →
          HasFieldsType tenv fs rowFields →
          ∃ vfs, evalFields venv fs = some vfs ∧ ValueFieldsHasType vfs rowFields)
      (intLit := by
        intro n tenv venv ty _h_env h_ty
        cases h_ty with
        | int =>
          exact ⟨.int n, by simp [eval, ValueHasType.int]⟩)
      (boolLit := by
        intro b tenv venv ty _h_env h_ty
        cases h_ty with
        | bool =>
          exact ⟨.bool b, by simp [eval, ValueHasType.bool]⟩)
      (stringLit := by
        intro s tenv venv ty _h_env h_ty
        cases h_ty with
        | string =>
          exact ⟨.string s, by simp [eval, ValueHasType.string]⟩)
      (var := by
        intro name tenv venv ty h_env h_ty
        cases h_ty with
        | var _ _ _ h_lookup =>
          rcases h_env name ty h_lookup with ⟨v, h_vlookup, h_vty⟩
          exact ⟨v, by simp [eval, h_vlookup], h_vty⟩)
      (appLam := by
        intro param paramTy body arg h_body h_arg ih_body ih_arg tenv venv ty h_env h_ty
        cases h_ty with
        | app _ _ _ paramTy' retTy h_fn_ty h_arg_ty =>
          cases h_fn_ty with
          | lam _ _ _ _ _ h_body_ty =>
            rcases ih_arg h_env h_arg_ty with ⟨vArg, h_eval_arg, h_varg_ty⟩
            have h_env' : EnvWellTyped ((param, paramTy) :: tenv) ((param, vArg) :: venv) :=
              envWellTyped_cons h_env h_varg_ty
            rcases ih_body h_env' h_body_ty with ⟨out, h_eval_body, h_out_ty⟩
            exact ⟨out, eval_app_lam_of_eval_arg venv param paramTy body arg vArg out h_eval_arg h_eval_body, h_out_ty⟩)
      (letE := by
        intro name value body h_value h_body ih_value ih_body tenv venv ty h_env h_ty
        cases h_ty with
        | letE _ _ _ _ valueTy _ h_value_ty h_body_ty =>
          rcases ih_value h_env h_value_ty with ⟨vv, h_eval_value, h_vv_ty⟩
          have h_env' : EnvWellTyped ((name, valueTy) :: tenv) ((name, vv) :: venv) :=
            envWellTyped_cons h_env h_vv_ty
          rcases ih_body h_env' h_body_ty with ⟨vb, h_eval_body, h_vb_ty⟩
          exact ⟨vb, by simpa [eval, h_eval_value] using h_eval_body, h_vb_ty⟩)
      (record := by
        intro fs h_fs ih_fs tenv venv ty h_env h_ty
        cases h_ty with
        | record _ _ rowFields h_fields_ty =>
          rcases ih_fs h_env h_fields_ty with ⟨vfs, h_eval_fields, h_vfs_ty⟩
          exact ⟨.record vfs, by simp [eval, h_eval_fields, ValueHasType.record, h_vfs_ty]⟩)
      (proj := by
        intro recv label h_recv ih_recv tenv venv ty h_env h_ty
        cases h_ty with
        | proj _ _ rowFields _ _ h_recv_ty h_get =>
          rcases ih_recv h_env h_recv_ty with ⟨vrecv, h_eval_recv, h_vrecv_ty⟩
          cases h_vrecv_ty with
          | record vfs rowFields' h_vfs =>
            rcases valueFieldsHasType_get h_vfs (by simpa using h_get) with
              ⟨v, h_field_lookup, h_vty⟩
            exact ⟨v, by simp [eval, h_eval_recv, h_field_lookup], h_vty⟩)
      (nil := by
        intro tenv venv rowFields _h_env h_ty
        cases h_ty with
        | nil =>
          exact ⟨[], by simp [evalFields, ValueFieldsHasType.nil]⟩)
      (cons := by
        intro label e rest h_e h_rest ih_e ih_rest tenv venv rowFields h_env h_ty
        cases h_ty with
        | cons _ _ _ _ ty restFields h_head h_tail =>
          rcases ih_e h_env h_head with ⟨v, h_eval_head, h_vty⟩
          rcases ih_rest h_env h_tail with ⟨vrest, h_eval_rest, h_rest_ty⟩
          exact ⟨(label, v) :: vrest, by
            simp [evalFields, h_eval_head, h_eval_rest, ValueFieldsHasType.cons, h_vty, h_rest_ty]⟩)
      h_frag h_env h_ty

  /-- Field-level executable soundness for `EvalFragmentFull`. -/
  theorem evalFields_sound_evalFragmentFull
      {tenv : TermEnv} {venv : ValueEnv} {fs : CoreFields} {rowFields : RowFields}
      (h_env : EnvWellTyped tenv venv)
      (h_ty : HasFieldsType tenv fs rowFields)
      (h_frag : EvalFragmentFullFields fs) :
      ∃ vfs, evalFields venv fs = some vfs ∧ ValueFieldsHasType vfs rowFields := by
    exact EvalFragmentFullFields.rec
      (motive_1 := fun e _ =>
        ∀ {tenv : TermEnv} {venv : ValueEnv} {ty : Ty},
          EnvWellTyped tenv venv →
          HasType tenv e ty →
          ∃ v, eval venv e = some v ∧ ValueHasType v ty)
      (motive_2 := fun fs _ =>
        ∀ {tenv : TermEnv} {venv : ValueEnv} {rowFields : RowFields},
          EnvWellTyped tenv venv →
          HasFieldsType tenv fs rowFields →
          ∃ vfs, evalFields venv fs = some vfs ∧ ValueFieldsHasType vfs rowFields)
      (intLit := by
        intro n tenv venv ty _h_env h_ty
        cases h_ty with
        | int =>
          exact ⟨.int n, by simp [eval, ValueHasType.int]⟩)
      (boolLit := by
        intro b tenv venv ty _h_env h_ty
        cases h_ty with
        | bool =>
          exact ⟨.bool b, by simp [eval, ValueHasType.bool]⟩)
      (stringLit := by
        intro s tenv venv ty _h_env h_ty
        cases h_ty with
        | string =>
          exact ⟨.string s, by simp [eval, ValueHasType.string]⟩)
      (var := by
        intro name tenv venv ty h_env h_ty
        cases h_ty with
        | var _ _ _ h_lookup =>
          rcases h_env name ty h_lookup with ⟨v, h_vlookup, h_vty⟩
          exact ⟨v, by simp [eval, h_vlookup], h_vty⟩)
      (appLam := by
        intro param paramTy body arg h_body h_arg ih_body ih_arg tenv venv ty h_env h_ty
        cases h_ty with
        | app _ _ _ paramTy' retTy h_fn_ty h_arg_ty =>
          cases h_fn_ty with
          | lam _ _ _ _ _ h_body_ty =>
            rcases ih_arg h_env h_arg_ty with ⟨vArg, h_eval_arg, h_varg_ty⟩
            have h_env' : EnvWellTyped ((param, paramTy) :: tenv) ((param, vArg) :: venv) :=
              envWellTyped_cons h_env h_varg_ty
            rcases ih_body h_env' h_body_ty with ⟨out, h_eval_body, h_out_ty⟩
            exact ⟨out, eval_app_lam_of_eval_arg venv param paramTy body arg vArg out h_eval_arg h_eval_body, h_out_ty⟩)
      (letE := by
        intro name value body h_value h_body ih_value ih_body tenv venv ty h_env h_ty
        cases h_ty with
        | letE _ _ _ _ valueTy _ h_value_ty h_body_ty =>
          rcases ih_value h_env h_value_ty with ⟨vv, h_eval_value, h_vv_ty⟩
          have h_env' : EnvWellTyped ((name, valueTy) :: tenv) ((name, vv) :: venv) :=
            envWellTyped_cons h_env h_vv_ty
          rcases ih_body h_env' h_body_ty with ⟨vb, h_eval_body, h_vb_ty⟩
          exact ⟨vb, by simpa [eval, h_eval_value] using h_eval_body, h_vb_ty⟩)
      (record := by
        intro fs h_fs ih_fs tenv venv ty h_env h_ty
        cases h_ty with
        | record _ _ rowFields h_fields_ty =>
          rcases ih_fs h_env h_fields_ty with ⟨vfs, h_eval_fields, h_vfs_ty⟩
          exact ⟨.record vfs, by simp [eval, h_eval_fields, ValueHasType.record, h_vfs_ty]⟩)
      (proj := by
        intro recv label h_recv ih_recv tenv venv ty h_env h_ty
        cases h_ty with
        | proj _ _ rowFields _ _ h_recv_ty h_get =>
          rcases ih_recv h_env h_recv_ty with ⟨vrecv, h_eval_recv, h_vrecv_ty⟩
          cases h_vrecv_ty with
          | record vfs rowFields' h_vfs =>
            rcases valueFieldsHasType_get h_vfs (by simpa using h_get) with
              ⟨v, h_field_lookup, h_vty⟩
            exact ⟨v, by simp [eval, h_eval_recv, h_field_lookup], h_vty⟩)
      (nil := by
        intro tenv venv rowFields _h_env h_ty
        cases h_ty with
        | nil =>
          exact ⟨[], by simp [evalFields, ValueFieldsHasType.nil]⟩)
      (cons := by
        intro label e rest h_e h_rest ih_e ih_rest tenv venv rowFields h_env h_ty
        cases h_ty with
        | cons _ _ _ _ ty restFields h_head h_tail =>
          rcases ih_e h_env h_head with ⟨v, h_eval_head, h_vty⟩
          rcases ih_rest h_env h_tail with ⟨vrest, h_eval_rest, h_rest_ty⟩
          exact ⟨(label, v) :: vrest, by
            simp [evalFields, h_eval_head, h_eval_rest, ValueFieldsHasType.cons, h_vty, h_rest_ty]⟩)
      h_frag h_env h_ty
end

/-- End-to-end executable soundness slice on `EvalFragmentFull`. -/
theorem inferEval_sound_evalFragmentFull
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty := by
  have h_ty : HasType tenv e ty := inferExpr_sound tenv e ty h_infer
  exact eval_sound_evalFragmentFull h_env h_ty h_frag

/--
Packaged theorem surface for the reduced executable vertical slice.
This is the citation anchor for the evaluator-side end-to-end fragment.
-/
def VerticalEvalSlice : Prop :=
  (∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    HasType tenv e ty →
    EvalFragmentFull e →
    ∃ v, eval venv e = some v ∧ ValueHasType v ty) ∧
  (∀ {tenv : TermEnv} {venv : ValueEnv} {fs : CoreFields} {rowFields : RowFields},
    EnvWellTyped tenv venv →
    HasFieldsType tenv fs rowFields →
    EvalFragmentFullFields fs →
    ∃ vfs, evalFields venv fs = some vfs ∧ ValueFieldsHasType vfs rowFields) ∧
  (∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    inferExpr tenv e = some ty →
    EvalFragmentFull e →
    ∃ v, eval venv e = some v ∧ ValueHasType v ty)

/-- The reduced executable vertical slice is fully proved. -/
theorem verticalEvalSlice_proved : VerticalEvalSlice := by
  refine ⟨?_, ?_, ?_⟩
  · intro tenv venv e ty h_env h_ty h_frag
    exact eval_sound_evalFragmentFull h_env h_ty h_frag
  · intro tenv venv fs rowFields h_env h_ty h_frag
    exact evalFields_sound_evalFragmentFull h_env h_ty h_frag
  · intro tenv venv e ty h_env h_infer h_frag
    exact inferEval_sound_evalFragmentFull h_env h_infer h_frag

/--
Executable soundness for the atomic evaluator fragment:
well-typed atomic expressions evaluate to runtime values of the same type.
-/
theorem eval_sound_atomic
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalAtomicExpr e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty := by
  cases h_frag with
  | intLit n =>
    cases h_ty with
    | int =>
      exact ⟨.int n, by simp [eval, ValueHasType.int]⟩
  | boolLit b =>
    cases h_ty with
    | bool =>
      exact ⟨.bool b, by simp [eval, ValueHasType.bool]⟩
  | stringLit s =>
    cases h_ty with
    | string =>
      exact ⟨.string s, by simp [eval, ValueHasType.string]⟩
  | var name =>
    cases h_ty with
    | var _ _ _ h_lookup =>
      rcases h_env name ty h_lookup with ⟨v, h_vlookup, h_vty⟩
      exact ⟨v, by simp [eval, h_vlookup, h_vty]⟩

/--
End-to-end executable soundness slice (atomic case):
if algorithmic inference succeeds and runtime env is well-typed, atomic
expressions evaluate to runtime values that preserve the inferred type.
-/
theorem inferEval_sound_atomic
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_infer : inferExpr tenv e = some ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalAtomicExpr e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty := by
  have h_ty : HasType tenv e ty := inferExpr_sound tenv e ty h_infer
  exact eval_sound_atomic h_env h_ty h_frag

/-- Field-evaluator progress on empty field lists. -/
theorem evalFields_progress_nil (env : ValueEnv) :
    ∃ vfs, evalFields env .nil = some vfs := by
  exact ⟨[], by simp [evalFields]⟩

/-- Field-evaluator progress step for non-empty field lists. -/
theorem evalFields_progress_cons_of_steps
    (env : ValueEnv) (label : Label) (e : CoreExpr) (rest : CoreFields)
    (v : Value) (vrest : ValueFields)
    (h_head : eval env e = some v)
    (h_rest : evalFields env rest = some vrest) :
    ∃ vfs, evalFields env (.cons label e rest) = some vfs := by
  exact ⟨(label, v) :: vrest, by simp [evalFields, h_head, h_rest]⟩

/-- Expression-level progress for records from field-evaluator progress. -/
theorem eval_progress_record_of_evalFields
    (env : ValueEnv) (fs : CoreFields)
    (h_fields : ∃ vfs, evalFields env fs = some vfs) :
    ∃ v, eval env (.record fs) = some v := by
  rcases h_fields with ⟨vfs, h_vfs⟩
  exact ⟨.record vfs, by simp [eval, h_vfs]⟩

/-- Expression-level projection progress from a known record-evaluation step. -/
theorem eval_progress_proj_of_record_eval
    (env : ValueEnv) (recv : CoreExpr) (label : Label)
    (vfs : ValueFields) (v : Value)
    (h_recv : eval env recv = some (.record vfs))
    (h_get : ValueFields.get vfs label = some v) :
    ∃ out, eval env (.proj recv label) = some out := by
  exact ⟨v, by simp [eval, h_recv, h_get]⟩

/-- Preservation on integer literals for the evaluator fragment. -/
theorem eval_preserves_int_lit
    (env : ValueEnv) (n : Int) (v : Value)
    (h_eval : eval env (.intLit n) = some v) :
    ValueHasType v .int := by
  simp [eval] at h_eval
  rcases h_eval with rfl
  exact ValueHasType.int n

/-- Preservation on boolean literals for the evaluator fragment. -/
theorem eval_preserves_bool_lit
    (env : ValueEnv) (b : Bool) (v : Value)
    (h_eval : eval env (.boolLit b) = some v) :
    ValueHasType v .bool := by
  simp [eval] at h_eval
  rcases h_eval with rfl
  exact ValueHasType.bool b

/-- Preservation on string literals for the evaluator fragment. -/
theorem eval_preserves_string_lit
    (env : ValueEnv) (s : String) (v : Value)
    (h_eval : eval env (.stringLit s) = some v) :
    ValueHasType v .string := by
  simp [eval] at h_eval
  rcases h_eval with rfl
  exact ValueHasType.string s

import Kea.Typing
import Kea.Properties.HandlerTypingContracts
import Kea.Properties.TailResumptiveClassification
import Kea.Properties.TailCapabilityComposition

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
Progress wrapper for the executable full fragment:
well-typed fragment expressions evaluate to some runtime value.
-/
theorem eval_progress_evalFragmentFull
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v := by
  rcases eval_sound_evalFragmentFull h_env h_ty h_frag with ⟨v, h_eval, _h_vty⟩
  exact ⟨v, h_eval⟩

/--
Preservation wrapper for the executable full fragment:
if a well-typed fragment expression evaluates, the result value has the same type.
-/
theorem eval_preservation_evalFragmentFull
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty} {v : Value}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e)
    (h_eval : eval venv e = some v) :
    ValueHasType v ty := by
  rcases eval_sound_evalFragmentFull h_env h_ty h_frag with ⟨v', h_eval', h_vty'⟩
  have h_eq : v = v' := eval_deterministic venv e h_eval h_eval'
  exact h_eq ▸ h_vty'

/--
Named type-soundness wrapper for the executable full fragment.
-/
theorem type_soundness_evalFragmentFull
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty := by
  exact eval_sound_evalFragmentFull h_env h_ty h_frag

/--
Canonical core-fragment soundness shape:
- progress (`eval` produces a value)
- preservation (`eval` results preserve the typing judgment)
-/
def CoreProgressPreservationEvalFragmentFull
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty) : Prop :=
  (∃ v, eval venv e = some v) ∧
    (∀ v, eval venv e = some v → ValueHasType v ty)

/-- Progress+preservation pair from declarative typing on `EvalFragmentFull`. -/
theorem coreProgressPreservationEvalFragmentFull_of_hasType
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    CoreProgressPreservationEvalFragmentFull tenv venv e ty := by
  constructor
  · exact eval_progress_evalFragmentFull h_env h_ty h_frag
  · intro v h_eval
    exact eval_preservation_evalFragmentFull h_env h_ty h_frag h_eval

/-- Progress+preservation pair from successful inference on `EvalFragmentFull`. -/
theorem coreProgressPreservationEvalFragmentFull_of_infer
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    CoreProgressPreservationEvalFragmentFull tenv venv e ty := by
  have h_ty : HasType tenv e ty := inferExpr_sound tenv e ty h_infer
  exact coreProgressPreservationEvalFragmentFull_of_hasType h_env h_ty h_frag

/--
Packaged core type-soundness surface for the executable full fragment under
declarative typing.
-/
structure CoreTypeSoundnessEvalBundle
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty) : Prop where
  soundness :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty
  progress :
    ∃ v, eval venv e = some v
  preservation :
    ∀ v, eval venv e = some v → ValueHasType v ty

/-- Explicit component alias for `CoreTypeSoundnessEvalBundle`. -/
abbrev CoreTypeSoundnessEvalBundleComponents
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty) : Prop :=
  (∃ v, eval venv e = some v ∧ ValueHasType v ty) ∧
    (∃ v, eval venv e = some v) ∧
      (∀ v, eval venv e = some v → ValueHasType v ty)

theorem coreTypeSoundnessEvalBundle_iff_components
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty} :
    CoreTypeSoundnessEvalBundle tenv venv e ty ↔
      CoreTypeSoundnessEvalBundleComponents tenv venv e ty := by
  constructor
  · intro h
    exact ⟨h.soundness, h.progress, h.preservation⟩
  · intro h
    exact { soundness := h.1, progress := h.2.1, preservation := h.2.2 }

theorem coreTypeSoundnessEvalBundle_of_components
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_comp : CoreTypeSoundnessEvalBundleComponents tenv venv e ty) :
    CoreTypeSoundnessEvalBundle tenv venv e ty :=
  (coreTypeSoundnessEvalBundle_iff_components).2 h_comp

theorem coreTypeSoundnessEvalBundle_as_components
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_bundle : CoreTypeSoundnessEvalBundle tenv venv e ty) :
    CoreTypeSoundnessEvalBundleComponents tenv venv e ty :=
  (coreTypeSoundnessEvalBundle_iff_components).1 h_bundle

theorem coreTypeSoundnessEvalBundle_as_components_of_components
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_comp : CoreTypeSoundnessEvalBundleComponents tenv venv e ty) :
    CoreTypeSoundnessEvalBundleComponents tenv venv e ty :=
  (coreTypeSoundnessEvalBundle_iff_components).1
    ((coreTypeSoundnessEvalBundle_iff_components).2 h_comp)

theorem coreTypeSoundnessEvalBundle_soundness
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_bundle : CoreTypeSoundnessEvalBundle tenv venv e ty) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  h_bundle.soundness

theorem coreTypeSoundnessEvalBundle_progress
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_bundle : CoreTypeSoundnessEvalBundle tenv venv e ty) :
    ∃ v, eval venv e = some v :=
  h_bundle.progress

theorem coreTypeSoundnessEvalBundle_preservation
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_bundle : CoreTypeSoundnessEvalBundle tenv venv e ty) :
    ∀ v, eval venv e = some v → ValueHasType v ty :=
  h_bundle.preservation

theorem coreTypeSoundnessEvalBundle_of_hasType
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundle tenv venv e ty := by
  refine {
    soundness := type_soundness_evalFragmentFull h_env h_ty h_frag
    progress := eval_progress_evalFragmentFull h_env h_ty h_frag
    preservation := ?_
  }
  intro v h_eval
  exact eval_preservation_evalFragmentFull h_env h_ty h_frag h_eval

theorem coreTypeSoundnessEvalBundle_of_infer
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundle tenv venv e ty := by
  have h_ty : HasType tenv e ty := inferExpr_sound tenv e ty h_infer
  exact coreTypeSoundnessEvalBundle_of_hasType h_env h_ty h_frag

theorem coreTypeSoundnessEvalBundle_as_components_of_hasType
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundleComponents tenv venv e ty :=
  coreTypeSoundnessEvalBundle_as_components
    (coreTypeSoundnessEvalBundle_of_hasType h_env h_ty h_frag)

theorem coreTypeSoundnessEvalBundle_as_components_of_infer
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundleComponents tenv venv e ty :=
  coreTypeSoundnessEvalBundle_as_components
    (coreTypeSoundnessEvalBundle_of_infer h_env h_infer h_frag)

theorem coreTypeSoundnessEvalBundle_iff_soundness_and_coreProgressPreservation
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty} :
    CoreTypeSoundnessEvalBundle tenv venv e ty ↔
      (∃ v, eval venv e = some v ∧ ValueHasType v ty)
        ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty := by
  constructor
  · intro h_bundle
    exact ⟨h_bundle.soundness, ⟨h_bundle.progress, h_bundle.preservation⟩⟩
  · intro h_pair
    exact {
      soundness := h_pair.1
      progress := h_pair.2.1
      preservation := h_pair.2.2
    }

theorem coreTypeSoundnessEvalBundle_of_soundness_and_coreProgressPreservation
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_pair :
      (∃ v, eval venv e = some v ∧ ValueHasType v ty)
        ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty) :
    CoreTypeSoundnessEvalBundle tenv venv e ty :=
  (coreTypeSoundnessEvalBundle_iff_soundness_and_coreProgressPreservation).2 h_pair

theorem coreTypeSoundnessEvalBundle_as_soundness_and_coreProgressPreservation
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_bundle : CoreTypeSoundnessEvalBundle tenv venv e ty) :
    (∃ v, eval venv e = some v ∧ ValueHasType v ty)
      ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
  (coreTypeSoundnessEvalBundle_iff_soundness_and_coreProgressPreservation).1 h_bundle

/--
Packaged declarative core soundness slice (`HasType` route) over the executable
full fragment.
-/
def CoreTypeSoundnessEvalSlice : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    HasType tenv e ty →
    EvalFragmentFull e →
    CoreTypeSoundnessEvalBundle tenv venv e ty

/-- Explicit component alias for `CoreTypeSoundnessEvalSlice`. -/
abbrev CoreTypeSoundnessEvalSliceComponents : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    HasType tenv e ty →
    EvalFragmentFull e →
    CoreTypeSoundnessEvalBundle tenv venv e ty

theorem coreTypeSoundnessEvalSlice_iff_components :
    CoreTypeSoundnessEvalSlice ↔ CoreTypeSoundnessEvalSliceComponents := Iff.rfl

theorem coreTypeSoundnessEvalSlice_of_components
    (h_comp : CoreTypeSoundnessEvalSliceComponents) :
    CoreTypeSoundnessEvalSlice :=
  (coreTypeSoundnessEvalSlice_iff_components).2 h_comp

theorem coreTypeSoundnessEvalSlice_as_components
    (h_slice : CoreTypeSoundnessEvalSlice) :
    CoreTypeSoundnessEvalSliceComponents :=
  (coreTypeSoundnessEvalSlice_iff_components).1 h_slice

theorem coreTypeSoundnessEvalSlice_as_components_of_components
    (h_comp : CoreTypeSoundnessEvalSliceComponents) :
    CoreTypeSoundnessEvalSliceComponents :=
  (coreTypeSoundnessEvalSlice_iff_components).1
    ((coreTypeSoundnessEvalSlice_iff_components).2 h_comp)

theorem coreTypeSoundnessEvalSlice_proved : CoreTypeSoundnessEvalSlice := by
  intro tenv venv e ty h_env h_ty h_frag
  exact coreTypeSoundnessEvalBundle_of_hasType h_env h_ty h_frag

theorem coreTypeSoundnessEvalSlice_bundle
    (h_slice : CoreTypeSoundnessEvalSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundle tenv venv e ty :=
  h_slice h_env h_ty h_frag

theorem coreTypeSoundnessEvalSlice_soundness
    (h_slice : CoreTypeSoundnessEvalSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  (coreTypeSoundnessEvalSlice_bundle h_slice h_env h_ty h_frag).soundness

theorem coreTypeSoundnessEvalSlice_progress
    (h_slice : CoreTypeSoundnessEvalSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (coreTypeSoundnessEvalSlice_bundle h_slice h_env h_ty h_frag).progress

theorem coreTypeSoundnessEvalSlice_preservation
    (h_slice : CoreTypeSoundnessEvalSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    ∀ v, eval venv e = some v → ValueHasType v ty :=
  (coreTypeSoundnessEvalSlice_bundle h_slice h_env h_ty h_frag).preservation

/--
Packaged declarative core soundness slice (`inferExpr` route) over the
executable full fragment.
-/
def CoreTypeSoundnessEvalInferSlice : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    inferExpr tenv e = some ty →
    EvalFragmentFull e →
    CoreTypeSoundnessEvalBundle tenv venv e ty

/-- Explicit component alias for `CoreTypeSoundnessEvalInferSlice`. -/
abbrev CoreTypeSoundnessEvalInferSliceComponents : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    inferExpr tenv e = some ty →
    EvalFragmentFull e →
    CoreTypeSoundnessEvalBundle tenv venv e ty

theorem coreTypeSoundnessEvalInferSlice_iff_components :
    CoreTypeSoundnessEvalInferSlice ↔ CoreTypeSoundnessEvalInferSliceComponents := Iff.rfl

theorem coreTypeSoundnessEvalInferSlice_of_components
    (h_comp : CoreTypeSoundnessEvalInferSliceComponents) :
    CoreTypeSoundnessEvalInferSlice :=
  (coreTypeSoundnessEvalInferSlice_iff_components).2 h_comp

theorem coreTypeSoundnessEvalInferSlice_as_components
    (h_slice : CoreTypeSoundnessEvalInferSlice) :
    CoreTypeSoundnessEvalInferSliceComponents :=
  (coreTypeSoundnessEvalInferSlice_iff_components).1 h_slice

theorem coreTypeSoundnessEvalInferSlice_as_components_of_components
    (h_comp : CoreTypeSoundnessEvalInferSliceComponents) :
    CoreTypeSoundnessEvalInferSliceComponents :=
  (coreTypeSoundnessEvalInferSlice_iff_components).1
    ((coreTypeSoundnessEvalInferSlice_iff_components).2 h_comp)

theorem coreTypeSoundnessEvalInferSlice_proved : CoreTypeSoundnessEvalInferSlice := by
  intro tenv venv e ty h_env h_infer h_frag
  exact coreTypeSoundnessEvalBundle_of_infer h_env h_infer h_frag

theorem coreTypeSoundnessEvalInferSlice_bundle
    (h_slice : CoreTypeSoundnessEvalInferSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundle tenv venv e ty :=
  h_slice h_env h_infer h_frag

theorem coreTypeSoundnessEvalInferSlice_soundness
    (h_slice : CoreTypeSoundnessEvalInferSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  (coreTypeSoundnessEvalInferSlice_bundle h_slice h_env h_infer h_frag).soundness

theorem coreTypeSoundnessEvalInferSlice_progress
    (h_slice : CoreTypeSoundnessEvalInferSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (coreTypeSoundnessEvalInferSlice_bundle h_slice h_env h_infer h_frag).progress

theorem coreTypeSoundnessEvalInferSlice_preservation
    (h_slice : CoreTypeSoundnessEvalInferSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    ∀ v, eval venv e = some v → ValueHasType v ty :=
  (coreTypeSoundnessEvalInferSlice_bundle h_slice h_env h_infer h_frag).preservation

theorem coreTypeSoundnessEvalInferSlice_of_coreTypeSoundnessEvalSlice
    (h_slice : CoreTypeSoundnessEvalSlice) :
    CoreTypeSoundnessEvalInferSlice := by
  intro tenv venv e ty h_env h_infer h_frag
  exact h_slice h_env (inferExpr_sound tenv e ty h_infer) h_frag

theorem coreTypeSoundnessEvalSlice_of_coreTypeSoundnessEvalInferSlice
    (h_slice : CoreTypeSoundnessEvalInferSlice) :
    CoreTypeSoundnessEvalSlice := by
  intro tenv venv e ty h_env h_ty h_frag
  have h_infer : inferExpr tenv e = some ty :=
    inferExpr_complete tenv e ty h_ty
  exact h_slice h_env h_infer h_frag

theorem coreTypeSoundnessEvalSlice_iff_coreTypeSoundnessEvalInferSlice :
    CoreTypeSoundnessEvalSlice ↔ CoreTypeSoundnessEvalInferSlice := by
  constructor
  · exact coreTypeSoundnessEvalInferSlice_of_coreTypeSoundnessEvalSlice
  · exact coreTypeSoundnessEvalSlice_of_coreTypeSoundnessEvalInferSlice

theorem coreTypeSoundnessEvalSlice_proved_via_inferSlice :
    CoreTypeSoundnessEvalSlice :=
  coreTypeSoundnessEvalSlice_of_coreTypeSoundnessEvalInferSlice
    coreTypeSoundnessEvalInferSlice_proved

theorem coreTypeSoundnessEvalInferSlice_proved_via_hasTypeSlice :
    CoreTypeSoundnessEvalInferSlice :=
  coreTypeSoundnessEvalInferSlice_of_coreTypeSoundnessEvalSlice
    coreTypeSoundnessEvalSlice_proved

theorem coreTypeSoundnessEvalSlice_of_verticalEvalSlice
    (h_vertical : VerticalEvalSlice) :
    CoreTypeSoundnessEvalSlice := by
  intro tenv venv e ty h_env h_ty h_frag
  have h_sound : ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
    h_vertical.1 h_env h_ty h_frag
  refine {
    soundness := h_sound
    progress := ?_
    preservation := ?_
  }
  · rcases h_sound with ⟨v, h_eval, _h_vty⟩
    exact ⟨v, h_eval⟩
  · intro v h_eval
    rcases h_sound with ⟨v', h_eval', h_vty'⟩
    have h_eq : v = v' := eval_deterministic venv e h_eval h_eval'
    exact h_eq ▸ h_vty'

theorem coreTypeSoundnessEvalSlice_proved_via_verticalEvalSlice :
    CoreTypeSoundnessEvalSlice :=
  coreTypeSoundnessEvalSlice_of_verticalEvalSlice verticalEvalSlice_proved

theorem coreTypeSoundnessEvalInferSlice_of_verticalEvalSlice
    (h_vertical : VerticalEvalSlice) :
    CoreTypeSoundnessEvalInferSlice :=
  coreTypeSoundnessEvalInferSlice_of_coreTypeSoundnessEvalSlice
    (coreTypeSoundnessEvalSlice_of_verticalEvalSlice h_vertical)

theorem coreTypeSoundnessEvalInferSlice_proved_via_verticalEvalSlice :
    CoreTypeSoundnessEvalInferSlice :=
  coreTypeSoundnessEvalInferSlice_of_verticalEvalSlice verticalEvalSlice_proved

/--
Unification-threaded entrypoint to the same core progress+preservation pair.

This bridges successful `inferExprUnify` runs (under bundled hook premises)
into evaluator-side core soundness.
-/
theorem coreProgressPreservationEvalFragmentFull_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState) (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreProgressPreservationEvalFragmentFull tenv venv e ty := by
  have h_infer : inferExpr tenv e = some ty :=
    inferExprUnify_inferExpr_agrees_of_success_from_hook_bundle_via_dual_bundle
      h_hooks st fuel tenv e st' ty h_ok
  exact coreProgressPreservationEvalFragmentFull_of_infer h_env h_infer h_frag

/--
Type-soundness wrapper from successful unification-threaded inference on the
full executable fragment.
-/
theorem type_soundness_evalFragmentFull_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState) (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty := by
  exact type_soundness_evalFragmentFull
    h_env
    (inferExprUnify_sound_preconditioned_from_hook_bundle_via_dual_bundle
      h_hooks st fuel tenv e st' ty h_ok)
    h_frag

/--
Progress wrapper from successful unification-threaded inference on the full
executable fragment.
-/
theorem eval_progress_evalFragmentFull_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState) (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v := by
  exact (coreProgressPreservationEvalFragmentFull_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag).1

/--
Preservation wrapper from successful unification-threaded inference on the full
executable fragment.
-/
theorem eval_preservation_evalFragmentFull_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty} {v : Value}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState) (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e)
    (h_eval : eval venv e = some v) :
    ValueHasType v ty := by
  exact (coreProgressPreservationEvalFragmentFull_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag).2 v h_eval

/--
Hook-parameterized variant of
`coreProgressPreservationEvalFragmentFull_of_inferUnify`.
-/
theorem coreProgressPreservationEvalFragmentFull_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState) (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
  coreProgressPreservationEvalFragmentFull_of_inferUnify
    ⟨h_app, h_proj⟩ st st' fuel h_ok h_env h_frag

/--
Hook-parameterized variant of
`type_soundness_evalFragmentFull_of_inferUnify`.
-/
theorem type_soundness_evalFragmentFull_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState) (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  type_soundness_evalFragmentFull_of_inferUnify
    ⟨h_app, h_proj⟩ st st' fuel h_ok h_env h_frag

/--
Hook-parameterized variant of
`eval_progress_evalFragmentFull_of_inferUnify`.
-/
theorem eval_progress_evalFragmentFull_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState) (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  eval_progress_evalFragmentFull_of_inferUnify
    ⟨h_app, h_proj⟩ st st' fuel h_ok h_env h_frag

/--
Hook-parameterized variant of
`eval_preservation_evalFragmentFull_of_inferUnify`.
-/
theorem eval_preservation_evalFragmentFull_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty} {v : Value}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState) (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e)
    (h_eval : eval venv e = some v) :
    ValueHasType v ty :=
  eval_preservation_evalFragmentFull_of_inferUnify
    ⟨h_app, h_proj⟩ st st' fuel h_ok h_env h_frag h_eval

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
Packaged theorem surface bridging unification-threaded success into evaluator
soundness on the full executable fragment.
-/
def VerticalEvalUnifyBridgeSlice : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_hooks : UnifyHookPremises) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    ∃ v, eval venv e = some v ∧ ValueHasType v ty

/-- The unification-bridge evaluator slice is fully proved. -/
theorem verticalEvalUnifyBridgeSlice_proved : VerticalEvalUnifyBridgeSlice := by
  intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
  exact type_soundness_evalFragmentFull_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag

/--
Hook-parameterized packaged theorem surface for unification-threaded evaluator
soundness on the full executable fragment.
-/
def VerticalEvalUnifyBridgeSliceFromHooks : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_app : AppUnifySoundHook) →
    (h_proj : ProjUnifySoundHook) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    ∃ v, eval venv e = some v ∧ ValueHasType v ty

/-- The hook-parameterized unification-bridge evaluator slice is fully proved. -/
theorem verticalEvalUnifyBridgeSliceFromHooks_proved :
    VerticalEvalUnifyBridgeSliceFromHooks := by
  intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
  exact type_soundness_evalFragmentFull_of_inferUnify_from_hooks
    h_app h_proj st st' fuel h_ok h_env h_frag

/--
Packaged theorem surface for unification-threaded progress+preservation on the
full executable fragment.
-/
def CoreProgressPreservationEvalUnifySlice : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_hooks : UnifyHookPremises) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreProgressPreservationEvalFragmentFull tenv venv e ty

/-- The unification-threaded progress+preservation slice is fully proved. -/
theorem coreProgressPreservationEvalUnifySlice_proved :
    CoreProgressPreservationEvalUnifySlice := by
  intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
  exact coreProgressPreservationEvalFragmentFull_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag

/--
Hook-parameterized packaged theorem surface for unification-threaded
progress+preservation on the full executable fragment.
-/
def CoreProgressPreservationEvalUnifySliceFromHooks : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_app : AppUnifySoundHook) →
    (h_proj : ProjUnifySoundHook) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreProgressPreservationEvalFragmentFull tenv venv e ty

/-- The hook-parameterized progress+preservation slice is fully proved. -/
theorem coreProgressPreservationEvalUnifySliceFromHooks_proved :
    CoreProgressPreservationEvalUnifySliceFromHooks := by
  intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
  exact coreProgressPreservationEvalFragmentFull_of_inferUnify_from_hooks
    h_app h_proj st st' fuel h_ok h_env h_frag

/--
Packaged unification-threaded core soundness surface:
- executable soundness witness
- progress witness
- preservation function for all produced values
on the full executable fragment.
-/
structure CoreTypeSoundnessEvalUnifyBundle
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty) : Prop where
  soundness : ∃ v, eval venv e = some v ∧ ValueHasType v ty
  progress : ∃ v, eval venv e = some v
  preservation : ∀ {v : Value}, eval venv e = some v → ValueHasType v ty

/-- Explicit component alias for `CoreTypeSoundnessEvalUnifyBundle`. -/
abbrev CoreTypeSoundnessEvalUnifyBundleComponents
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty) : Prop :=
  (∃ v, eval venv e = some v ∧ ValueHasType v ty) ∧
    (∃ v, eval venv e = some v) ∧
    (∀ {v : Value}, eval venv e = some v → ValueHasType v ty)

/--
`CoreTypeSoundnessEvalUnifyBundle` is equivalent to its explicit component
surface.
-/
theorem coreTypeSoundnessEvalUnifyBundle_iff_components
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty ↔
      CoreTypeSoundnessEvalUnifyBundleComponents tenv venv e ty := by
  constructor
  · intro h_bundle
    exact ⟨h_bundle.soundness, h_bundle.progress, h_bundle.preservation⟩
  · intro h_comp
    exact ⟨h_comp.1, h_comp.2.1, h_comp.2.2⟩

/-- Build `CoreTypeSoundnessEvalUnifyBundle` from explicit components. -/
theorem coreTypeSoundnessEvalUnifyBundle_of_components
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty)
    (h_comp : CoreTypeSoundnessEvalUnifyBundleComponents tenv venv e ty) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  (coreTypeSoundnessEvalUnifyBundle_iff_components tenv venv e ty).2 h_comp

/-- Decompose `CoreTypeSoundnessEvalUnifyBundle` into explicit components. -/
theorem coreTypeSoundnessEvalUnifyBundle_as_components
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty)
    (h_bundle : CoreTypeSoundnessEvalUnifyBundle tenv venv e ty) :
    CoreTypeSoundnessEvalUnifyBundleComponents tenv venv e ty :=
  (coreTypeSoundnessEvalUnifyBundle_iff_components tenv venv e ty).1 h_bundle

/-- Direct components-route decomposition for `CoreTypeSoundnessEvalUnifyBundle`. -/
theorem coreTypeSoundnessEvalUnifyBundle_as_components_of_components
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty)
    (h_comp : CoreTypeSoundnessEvalUnifyBundleComponents tenv venv e ty) :
    CoreTypeSoundnessEvalUnifyBundleComponents tenv venv e ty :=
  (coreTypeSoundnessEvalUnifyBundle_iff_components tenv venv e ty).1
    ((coreTypeSoundnessEvalUnifyBundle_iff_components tenv venv e ty).2 h_comp)

/-- One-hop soundness projection from the packaged core-soundness bundle. -/
theorem coreTypeSoundnessEvalUnifyBundle_soundness
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty)
    (h_bundle : CoreTypeSoundnessEvalUnifyBundle tenv venv e ty) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  h_bundle.soundness

/-- One-hop progress projection from the packaged core-soundness bundle. -/
theorem coreTypeSoundnessEvalUnifyBundle_progress
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty)
    (h_bundle : CoreTypeSoundnessEvalUnifyBundle tenv venv e ty) :
    ∃ v, eval venv e = some v :=
  h_bundle.progress

/-- One-hop preservation projection from the packaged core-soundness bundle. -/
theorem coreTypeSoundnessEvalUnifyBundle_preservation
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty)
    (h_bundle : CoreTypeSoundnessEvalUnifyBundle tenv venv e ty) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  h_bundle.preservation

/--
Interoperability bridge: any unification-threaded core-soundness bundle
instantiates the declarative bundled core-soundness surface.
-/
theorem coreTypeSoundnessEvalBundle_of_coreTypeSoundnessEvalUnifyBundle
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty)
    (h_unify : CoreTypeSoundnessEvalUnifyBundle tenv venv e ty) :
    CoreTypeSoundnessEvalBundle tenv venv e ty := by
  exact {
    soundness := h_unify.soundness
    progress := h_unify.progress
    preservation := by
      intro v h_eval
      exact h_unify.preservation h_eval
  }

theorem coreTypeSoundnessEvalUnifyBundle_of_coreTypeSoundnessEvalBundle
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty)
    (h_decl : CoreTypeSoundnessEvalBundle tenv venv e ty) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty := by
  exact {
    soundness := h_decl.soundness
    progress := h_decl.progress
    preservation := by
      intro v h_eval
      exact h_decl.preservation v h_eval
  }

theorem coreTypeSoundnessEvalBundle_iff_coreTypeSoundnessEvalUnifyBundle
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty) :
    CoreTypeSoundnessEvalBundle tenv venv e ty
      ↔ CoreTypeSoundnessEvalUnifyBundle tenv venv e ty := by
  constructor
  · intro h_decl
    exact coreTypeSoundnessEvalUnifyBundle_of_coreTypeSoundnessEvalBundle
      tenv venv e ty h_decl
  · intro h_unify
    exact coreTypeSoundnessEvalBundle_of_coreTypeSoundnessEvalUnifyBundle
      tenv venv e ty h_unify

/--
Build the packaged core-soundness bundle from unification-threaded inference
success under bundled hooks.
-/
theorem coreTypeSoundnessEvalUnifyBundle_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty := by
  refine
    { soundness := ?_
      progress := ?_
      preservation := ?_ }
  · exact type_soundness_evalFragmentFull_of_inferUnify
      h_hooks st st' fuel h_ok h_env h_frag
  · exact eval_progress_evalFragmentFull_of_inferUnify
      h_hooks st st' fuel h_ok h_env h_frag
  · intro v h_eval
    exact eval_preservation_evalFragmentFull_of_inferUnify
      h_hooks st st' fuel h_ok h_env h_frag h_eval

/--
Constructor-route decomposition wrapper for
`coreTypeSoundnessEvalUnifyBundle_of_inferUnify`.
-/
theorem coreTypeSoundnessEvalUnifyBundle_as_components_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundleComponents tenv venv e ty :=
  coreTypeSoundnessEvalUnifyBundle_as_components
    tenv venv e ty
    (coreTypeSoundnessEvalUnifyBundle_of_inferUnify
      h_hooks st st' fuel h_ok h_env h_frag)

/--
Hook-parameterized constructor variant for
`coreTypeSoundnessEvalUnifyBundle_of_inferUnify`.
-/
theorem coreTypeSoundnessEvalUnifyBundle_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  coreTypeSoundnessEvalUnifyBundle_of_inferUnify
    ⟨h_app, h_proj⟩ st st' fuel h_ok h_env h_frag

/--
Constructor-route decomposition wrapper for
`coreTypeSoundnessEvalUnifyBundle_of_inferUnify_from_hooks`.
-/
theorem coreTypeSoundnessEvalUnifyBundle_as_components_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundleComponents tenv venv e ty :=
  coreTypeSoundnessEvalUnifyBundle_as_components
    tenv venv e ty
    (coreTypeSoundnessEvalUnifyBundle_of_inferUnify_from_hooks
      h_app h_proj st st' fuel h_ok h_env h_frag)

theorem coreTypeSoundnessEvalBundle_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundle tenv venv e ty :=
  coreTypeSoundnessEvalBundle_of_coreTypeSoundnessEvalUnifyBundle
    tenv venv e ty
    (coreTypeSoundnessEvalUnifyBundle_of_inferUnify
      h_hooks st st' fuel h_ok h_env h_frag)

theorem coreTypeSoundnessEvalBundle_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundle tenv venv e ty :=
  coreTypeSoundnessEvalBundle_of_inferUnify
    ⟨h_app, h_proj⟩ st st' fuel h_ok h_env h_frag

theorem coreTypeSoundnessEvalBundle_as_components_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundleComponents tenv venv e ty :=
  coreTypeSoundnessEvalBundle_as_components
    (coreTypeSoundnessEvalBundle_of_inferUnify
      h_hooks st st' fuel h_ok h_env h_frag)

theorem coreTypeSoundnessEvalBundle_as_components_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundleComponents tenv venv e ty :=
  coreTypeSoundnessEvalBundle_as_components
    (coreTypeSoundnessEvalBundle_of_inferUnify_from_hooks
      h_app h_proj st st' fuel h_ok h_env h_frag)

/--
Packaged theorem surface: successful unification-threaded inference yields the
full core-soundness bundle.
-/
def CoreTypeSoundnessEvalUnifySlice : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_hooks : UnifyHookPremises) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty

/-- Explicit component alias for `CoreTypeSoundnessEvalUnifySlice`. -/
abbrev CoreTypeSoundnessEvalUnifySliceComponents : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_hooks : UnifyHookPremises) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty

/-- `CoreTypeSoundnessEvalUnifySlice` is equivalent to explicit components. -/
theorem coreTypeSoundnessEvalUnifySlice_iff_components :
    CoreTypeSoundnessEvalUnifySlice ↔ CoreTypeSoundnessEvalUnifySliceComponents := Iff.rfl

/-- Build `CoreTypeSoundnessEvalUnifySlice` from explicit components. -/
theorem coreTypeSoundnessEvalUnifySlice_of_components
    (h_comp : CoreTypeSoundnessEvalUnifySliceComponents) :
    CoreTypeSoundnessEvalUnifySlice :=
  (coreTypeSoundnessEvalUnifySlice_iff_components).2 h_comp

/-- Decompose `CoreTypeSoundnessEvalUnifySlice` into explicit components. -/
theorem coreTypeSoundnessEvalUnifySlice_as_components
    (h_slice : CoreTypeSoundnessEvalUnifySlice) :
    CoreTypeSoundnessEvalUnifySliceComponents :=
  (coreTypeSoundnessEvalUnifySlice_iff_components).1 h_slice

/-- Direct components-route decomposition for `CoreTypeSoundnessEvalUnifySlice`. -/
theorem coreTypeSoundnessEvalUnifySlice_as_components_of_components
    (h_comp : CoreTypeSoundnessEvalUnifySliceComponents) :
    CoreTypeSoundnessEvalUnifySliceComponents :=
  (coreTypeSoundnessEvalUnifySlice_iff_components).1
    ((coreTypeSoundnessEvalUnifySlice_iff_components).2 h_comp)

/-- The packaged core-soundness unification slice is fully proved. -/
theorem coreTypeSoundnessEvalUnifySlice_proved :
    CoreTypeSoundnessEvalUnifySlice := by
  intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
  exact coreTypeSoundnessEvalUnifyBundle_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag

/--
Hook-parameterized packaged theorem surface for
`CoreTypeSoundnessEvalUnifySlice`.
-/
def CoreTypeSoundnessEvalUnifySliceFromHooks : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_app : AppUnifySoundHook) →
    (h_proj : ProjUnifySoundHook) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty

/--
Explicit component alias for `CoreTypeSoundnessEvalUnifySliceFromHooks`.
-/
abbrev CoreTypeSoundnessEvalUnifySliceFromHooksComponents : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_app : AppUnifySoundHook) →
    (h_proj : ProjUnifySoundHook) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty

/--
`CoreTypeSoundnessEvalUnifySliceFromHooks` is equivalent to explicit
components.
-/
theorem coreTypeSoundnessEvalUnifySliceFromHooks_iff_components :
    CoreTypeSoundnessEvalUnifySliceFromHooks ↔
      CoreTypeSoundnessEvalUnifySliceFromHooksComponents := Iff.rfl

/--
Build `CoreTypeSoundnessEvalUnifySliceFromHooks` from explicit components.
-/
theorem coreTypeSoundnessEvalUnifySliceFromHooks_of_components
    (h_comp : CoreTypeSoundnessEvalUnifySliceFromHooksComponents) :
    CoreTypeSoundnessEvalUnifySliceFromHooks :=
  (coreTypeSoundnessEvalUnifySliceFromHooks_iff_components).2 h_comp

/--
Decompose `CoreTypeSoundnessEvalUnifySliceFromHooks` into explicit components.
-/
theorem coreTypeSoundnessEvalUnifySliceFromHooks_as_components
    (h_slice : CoreTypeSoundnessEvalUnifySliceFromHooks) :
    CoreTypeSoundnessEvalUnifySliceFromHooksComponents :=
  (coreTypeSoundnessEvalUnifySliceFromHooks_iff_components).1 h_slice

/--
Direct components-route decomposition for
`CoreTypeSoundnessEvalUnifySliceFromHooks`.
-/
theorem coreTypeSoundnessEvalUnifySliceFromHooks_as_components_of_components
    (h_comp : CoreTypeSoundnessEvalUnifySliceFromHooksComponents) :
    CoreTypeSoundnessEvalUnifySliceFromHooksComponents :=
  (coreTypeSoundnessEvalUnifySliceFromHooks_iff_components).1
    ((coreTypeSoundnessEvalUnifySliceFromHooks_iff_components).2 h_comp)

/-- The hook-parameterized core-soundness unification slice is fully proved. -/
theorem coreTypeSoundnessEvalUnifySliceFromHooks_proved :
    CoreTypeSoundnessEvalUnifySliceFromHooks := by
  intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
  exact coreTypeSoundnessEvalUnifyBundle_of_inferUnify_from_hooks
    h_app h_proj st st' fuel h_ok h_env h_frag

/--
One-hop soundness consequence on the packaged unification-threaded core
soundness slice.
-/
theorem coreTypeSoundnessEvalUnifySlice_soundness
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  (coreTypeSoundnessEvalUnifyBundle_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag).soundness

/--
One-hop progress consequence on the packaged unification-threaded core
soundness slice.
-/
theorem coreTypeSoundnessEvalUnifySlice_progress
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (coreTypeSoundnessEvalUnifyBundle_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag).progress

/--
One-hop preservation consequence on the packaged unification-threaded core
soundness slice.
-/
theorem coreTypeSoundnessEvalUnifySlice_preservation
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  (coreTypeSoundnessEvalUnifyBundle_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag).preservation

/--
The packaged core-soundness bundle is equivalent to explicit soundness plus
the existing core progress+preservation pair.
-/
theorem coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
    (tenv : TermEnv)
    (venv : ValueEnv)
    (e : CoreExpr)
    (ty : Ty) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty ↔
      (∃ v, eval venv e = some v ∧ ValueHasType v ty)
        ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty := by
  constructor
  · intro h_bundle
    exact ⟨h_bundle.soundness, h_bundle.progress, h_bundle.preservation⟩
  · intro h_pair
    exact
      { soundness := h_pair.1
        progress := h_pair.2.1
        preservation := h_pair.2.2 }

/--
Route bridge: recover the packaged core-soundness bundle by composing the
existing vertical soundness slice with the existing core progress+preservation
slice.
-/
theorem coreTypeSoundnessEvalUnifyBundle_of_existing_slices
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty := by
  have h_sound :
      ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
    verticalEvalUnifyBridgeSlice_proved h_hooks st st' fuel h_ok h_env h_frag
  have h_core :
      CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
    coreProgressPreservationEvalUnifySlice_proved
      h_hooks st st' fuel h_ok h_env h_frag
  exact
    (coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
      tenv venv e ty).2 ⟨h_sound, h_core⟩

/--
Hook-parameterized route bridge variant of
`coreTypeSoundnessEvalUnifyBundle_of_existing_slices`.
-/
theorem coreTypeSoundnessEvalUnifyBundle_of_existing_slices_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty := by
  have h_sound :
      ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
    verticalEvalUnifyBridgeSliceFromHooks_proved
      h_app h_proj st st' fuel h_ok h_env h_frag
  have h_core :
      CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
    coreProgressPreservationEvalUnifySliceFromHooks_proved
      h_app h_proj st st' fuel h_ok h_env h_frag
  exact
    (coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
      tenv venv e ty).2 ⟨h_sound, h_core⟩

/--
One-hop canonical core-calculus consequences from successful unification-threaded
inference (bundled hook route):
- soundness witness
- progress/preservation pair
-/
theorem coreCalculusSoundness_consequences_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    (∃ v, eval venv e = some v ∧ ValueHasType v ty)
      ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty := by
  exact
    (coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
      tenv venv e ty).1
      (coreTypeSoundnessEvalUnifyBundle_of_inferUnify
        h_hooks st st' fuel h_ok h_env h_frag)

/--
One-hop canonical core-calculus consequences from successful unification-threaded
inference (explicit hook route).
-/
theorem coreCalculusSoundness_consequences_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    (∃ v, eval venv e = some v ∧ ValueHasType v ty)
      ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty := by
  exact
    (coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
      tenv venv e ty).1
      (coreTypeSoundnessEvalUnifyBundle_of_inferUnify_from_hooks
        h_app h_proj st st' fuel h_ok h_env h_frag)

/--
Named run-local canonical core-calculus consequence surface:
soundness plus progress/preservation for one inferred run.
-/
abbrev CoreCalculusSoundnessConsequences
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty) : Prop :=
  (∃ v, eval venv e = some v ∧ ValueHasType v ty)
    ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty

theorem coreCalculusSoundnessConsequences_iff_components
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty) :
    CoreCalculusSoundnessConsequences tenv venv e ty
      ↔
      ((∃ v, eval venv e = some v ∧ ValueHasType v ty)
        ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty) := Iff.rfl

theorem coreCalculusSoundnessConsequences_of_components
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty)
    (h_comp :
      (∃ v, eval venv e = some v ∧ ValueHasType v ty)
        ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  (coreCalculusSoundnessConsequences_iff_components tenv venv e ty).2 h_comp

theorem coreCalculusSoundnessConsequences_as_components
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty)
    (h_cons : CoreCalculusSoundnessConsequences tenv venv e ty) :
    (∃ v, eval venv e = some v ∧ ValueHasType v ty)
      ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
  (coreCalculusSoundnessConsequences_iff_components tenv venv e ty).1 h_cons

theorem coreCalculusSoundnessConsequences_as_components_of_components
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty)
    (h_comp :
      (∃ v, eval venv e = some v ∧ ValueHasType v ty)
        ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty) :
    (∃ v, eval venv e = some v ∧ ValueHasType v ty)
      ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
  coreCalculusSoundnessConsequences_as_components tenv venv e ty
    (coreCalculusSoundnessConsequences_of_components tenv venv e ty h_comp)

theorem coreCalculusSoundnessConsequences_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  coreCalculusSoundness_consequences_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessConsequences_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  coreCalculusSoundness_consequences_of_inferUnify_from_hooks
    h_app h_proj st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessConsequences_as_components_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    (∃ v, eval venv e = some v ∧ ValueHasType v ty)
      ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
  coreCalculusSoundnessConsequences_as_components tenv venv e ty
    (coreCalculusSoundnessConsequences_of_inferUnify
      h_hooks st st' fuel h_ok h_env h_frag)

theorem coreCalculusSoundnessConsequences_as_components_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    (∃ v, eval venv e = some v ∧ ValueHasType v ty)
      ∧ CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
  coreCalculusSoundnessConsequences_as_components tenv venv e ty
    (coreCalculusSoundnessConsequences_of_inferUnify_from_hooks
      h_app h_proj st st' fuel h_ok h_env h_frag)

theorem coreCalculusSoundnessConsequences_iff_coreTypeSoundnessEvalUnifyBundle
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty) :
    CoreCalculusSoundnessConsequences tenv venv e ty
      ↔ CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  (coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
    tenv venv e ty).symm

theorem coreCalculusSoundnessConsequences_of_bundle
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty)
    (h_bundle : CoreTypeSoundnessEvalUnifyBundle tenv venv e ty) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  (coreCalculusSoundnessConsequences_iff_coreTypeSoundnessEvalUnifyBundle
    tenv venv e ty).2 h_bundle

theorem coreCalculusSoundnessConsequences_as_bundle
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty)
    (h_cons : CoreCalculusSoundnessConsequences tenv venv e ty) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  (coreCalculusSoundnessConsequences_iff_coreTypeSoundnessEvalUnifyBundle
    tenv venv e ty).1 h_cons

theorem coreCalculusSoundnessConsequences_iff_coreTypeSoundnessEvalBundle
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty) :
    CoreCalculusSoundnessConsequences tenv venv e ty
      ↔ CoreTypeSoundnessEvalBundle tenv venv e ty := by
  constructor
  · intro h_cons
    exact
      (coreTypeSoundnessEvalBundle_iff_soundness_and_coreProgressPreservation).2 h_cons
  · intro h_bundle
    exact
      (coreTypeSoundnessEvalBundle_iff_soundness_and_coreProgressPreservation).1 h_bundle

theorem coreCalculusSoundnessConsequences_of_declarative_bundle
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty)
    (h_bundle : CoreTypeSoundnessEvalBundle tenv venv e ty) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  (coreCalculusSoundnessConsequences_iff_coreTypeSoundnessEvalBundle
    tenv venv e ty).2 h_bundle

theorem coreCalculusSoundnessConsequences_as_declarative_bundle
    (tenv : TermEnv) (venv : ValueEnv) (e : CoreExpr) (ty : Ty)
    (h_cons : CoreCalculusSoundnessConsequences tenv venv e ty) :
    CoreTypeSoundnessEvalBundle tenv venv e ty :=
  (coreCalculusSoundnessConsequences_iff_coreTypeSoundnessEvalBundle
    tenv venv e ty).1 h_cons

theorem coreCalculusSoundnessConsequences_as_bundle_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  coreCalculusSoundnessConsequences_as_bundle tenv venv e ty
    (coreCalculusSoundnessConsequences_of_inferUnify
      h_hooks st st' fuel h_ok h_env h_frag)

theorem coreCalculusSoundnessConsequences_as_bundle_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  coreCalculusSoundnessConsequences_as_bundle tenv venv e ty
    (coreCalculusSoundnessConsequences_of_inferUnify_from_hooks
      h_app h_proj st st' fuel h_ok h_env h_frag)

theorem coreCalculusSoundnessConsequences_as_declarative_bundle_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundle tenv venv e ty :=
  coreCalculusSoundnessConsequences_as_declarative_bundle tenv venv e ty
    (coreCalculusSoundnessConsequences_of_inferUnify
      h_hooks st st' fuel h_ok h_env h_frag)

theorem coreCalculusSoundnessConsequences_as_declarative_bundle_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalBundle tenv venv e ty :=
  coreCalculusSoundnessConsequences_as_declarative_bundle tenv venv e ty
    (coreCalculusSoundnessConsequences_of_inferUnify_from_hooks
      h_app h_proj st st' fuel h_ok h_env h_frag)

theorem coreCalculusSoundnessConsequences_of_coreTypeSoundnessEvalSlice
    (h_slice : CoreTypeSoundnessEvalSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  coreCalculusSoundnessConsequences_of_declarative_bundle tenv venv e ty
    (coreTypeSoundnessEvalSlice_bundle h_slice h_env h_ty h_frag)

theorem coreCalculusSoundnessConsequences_of_coreTypeSoundnessEvalInferSlice
    (h_slice : CoreTypeSoundnessEvalInferSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  coreCalculusSoundnessConsequences_of_declarative_bundle tenv venv e ty
    (coreTypeSoundnessEvalInferSlice_bundle h_slice h_env h_infer h_frag)

theorem coreCalculusSoundnessConsequences_of_coreTypeSoundnessEvalSlice_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  coreCalculusSoundnessConsequences_of_coreTypeSoundnessEvalSlice
    coreTypeSoundnessEvalSlice_proved h_env h_ty h_frag

theorem coreCalculusSoundnessConsequences_of_coreTypeSoundnessEvalInferSlice_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  coreCalculusSoundnessConsequences_of_coreTypeSoundnessEvalInferSlice
    coreTypeSoundnessEvalInferSlice_proved h_env h_infer h_frag

def CoreCalculusSoundnessDeclarativeSlice : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    HasType tenv e ty →
    EvalFragmentFull e →
    CoreCalculusSoundnessConsequences tenv venv e ty

abbrev CoreCalculusSoundnessDeclarativeSliceComponents : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    HasType tenv e ty →
    EvalFragmentFull e →
    CoreCalculusSoundnessConsequences tenv venv e ty

theorem coreCalculusSoundnessDeclarativeSlice_iff_components :
    CoreCalculusSoundnessDeclarativeSlice ↔
      CoreCalculusSoundnessDeclarativeSliceComponents := Iff.rfl

theorem coreCalculusSoundnessDeclarativeSlice_of_components
    (h_comp : CoreCalculusSoundnessDeclarativeSliceComponents) :
    CoreCalculusSoundnessDeclarativeSlice :=
  (coreCalculusSoundnessDeclarativeSlice_iff_components).2 h_comp

theorem coreCalculusSoundnessDeclarativeSlice_as_components
    (h_slice : CoreCalculusSoundnessDeclarativeSlice) :
    CoreCalculusSoundnessDeclarativeSliceComponents :=
  (coreCalculusSoundnessDeclarativeSlice_iff_components).1 h_slice

theorem coreCalculusSoundnessDeclarativeSlice_as_components_of_components
    (h_comp : CoreCalculusSoundnessDeclarativeSliceComponents) :
    CoreCalculusSoundnessDeclarativeSliceComponents :=
  (coreCalculusSoundnessDeclarativeSlice_iff_components).1
    ((coreCalculusSoundnessDeclarativeSlice_iff_components).2 h_comp)

theorem coreCalculusSoundnessDeclarativeSlice_of_coreTypeSoundnessEvalSlice
    (h_slice : CoreTypeSoundnessEvalSlice) :
    CoreCalculusSoundnessDeclarativeSlice :=
  coreCalculusSoundnessConsequences_of_coreTypeSoundnessEvalSlice h_slice

theorem coreTypeSoundnessEvalSlice_of_coreCalculusSoundnessDeclarativeSlice
    (h_slice : CoreCalculusSoundnessDeclarativeSlice) :
    CoreTypeSoundnessEvalSlice := by
  intro tenv venv e ty h_env h_ty h_frag
  exact coreCalculusSoundnessConsequences_as_declarative_bundle tenv venv e ty
    (h_slice h_env h_ty h_frag)

theorem coreCalculusSoundnessDeclarativeSlice_iff_coreTypeSoundnessEvalSlice :
    CoreCalculusSoundnessDeclarativeSlice ↔ CoreTypeSoundnessEvalSlice := by
  constructor
  · exact coreTypeSoundnessEvalSlice_of_coreCalculusSoundnessDeclarativeSlice
  · exact coreCalculusSoundnessDeclarativeSlice_of_coreTypeSoundnessEvalSlice

theorem coreCalculusSoundnessDeclarativeSlice_proved :
    CoreCalculusSoundnessDeclarativeSlice :=
  coreCalculusSoundnessDeclarativeSlice_of_coreTypeSoundnessEvalSlice
    coreTypeSoundnessEvalSlice_proved

theorem coreCalculusSoundnessDeclarativeSlice_consequences
    (h_slice : CoreCalculusSoundnessDeclarativeSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  h_slice h_env h_ty h_frag

theorem coreCalculusSoundnessDeclarativeSlice_soundness
    (h_slice : CoreCalculusSoundnessDeclarativeSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  (coreCalculusSoundnessDeclarativeSlice_consequences
    h_slice h_env h_ty h_frag).1

theorem coreCalculusSoundnessDeclarativeSlice_progress
    (h_slice : CoreCalculusSoundnessDeclarativeSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (coreCalculusSoundnessDeclarativeSlice_consequences
    h_slice h_env h_ty h_frag).2.1

theorem coreCalculusSoundnessDeclarativeSlice_preservation
    (h_slice : CoreCalculusSoundnessDeclarativeSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_ty : HasType tenv e ty)
    (h_frag : EvalFragmentFull e) :
    ∀ v, eval venv e = some v → ValueHasType v ty :=
  (coreCalculusSoundnessDeclarativeSlice_consequences
    h_slice h_env h_ty h_frag).2.2

def CoreCalculusSoundnessDeclarativeInferSlice : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    inferExpr tenv e = some ty →
    EvalFragmentFull e →
    CoreCalculusSoundnessConsequences tenv venv e ty

abbrev CoreCalculusSoundnessDeclarativeInferSliceComponents : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    EnvWellTyped tenv venv →
    inferExpr tenv e = some ty →
    EvalFragmentFull e →
    CoreCalculusSoundnessConsequences tenv venv e ty

theorem coreCalculusSoundnessDeclarativeInferSlice_iff_components :
    CoreCalculusSoundnessDeclarativeInferSlice ↔
      CoreCalculusSoundnessDeclarativeInferSliceComponents := Iff.rfl

theorem coreCalculusSoundnessDeclarativeInferSlice_of_components
    (h_comp : CoreCalculusSoundnessDeclarativeInferSliceComponents) :
    CoreCalculusSoundnessDeclarativeInferSlice :=
  (coreCalculusSoundnessDeclarativeInferSlice_iff_components).2 h_comp

theorem coreCalculusSoundnessDeclarativeInferSlice_as_components
    (h_slice : CoreCalculusSoundnessDeclarativeInferSlice) :
    CoreCalculusSoundnessDeclarativeInferSliceComponents :=
  (coreCalculusSoundnessDeclarativeInferSlice_iff_components).1 h_slice

theorem coreCalculusSoundnessDeclarativeInferSlice_as_components_of_components
    (h_comp : CoreCalculusSoundnessDeclarativeInferSliceComponents) :
    CoreCalculusSoundnessDeclarativeInferSliceComponents :=
  (coreCalculusSoundnessDeclarativeInferSlice_iff_components).1
    ((coreCalculusSoundnessDeclarativeInferSlice_iff_components).2 h_comp)

theorem coreCalculusSoundnessDeclarativeInferSlice_of_coreTypeSoundnessEvalInferSlice
    (h_slice : CoreTypeSoundnessEvalInferSlice) :
    CoreCalculusSoundnessDeclarativeInferSlice :=
  coreCalculusSoundnessConsequences_of_coreTypeSoundnessEvalInferSlice h_slice

theorem coreTypeSoundnessEvalInferSlice_of_coreCalculusSoundnessDeclarativeInferSlice
    (h_slice : CoreCalculusSoundnessDeclarativeInferSlice) :
    CoreTypeSoundnessEvalInferSlice := by
  intro tenv venv e ty h_env h_infer h_frag
  exact coreCalculusSoundnessConsequences_as_declarative_bundle tenv venv e ty
    (h_slice h_env h_infer h_frag)

theorem coreCalculusSoundnessDeclarativeInferSlice_iff_coreTypeSoundnessEvalInferSlice :
    CoreCalculusSoundnessDeclarativeInferSlice ↔ CoreTypeSoundnessEvalInferSlice := by
  constructor
  · exact coreTypeSoundnessEvalInferSlice_of_coreCalculusSoundnessDeclarativeInferSlice
  · exact coreCalculusSoundnessDeclarativeInferSlice_of_coreTypeSoundnessEvalInferSlice

theorem coreCalculusSoundnessDeclarativeInferSlice_proved :
    CoreCalculusSoundnessDeclarativeInferSlice :=
  coreCalculusSoundnessDeclarativeInferSlice_of_coreTypeSoundnessEvalInferSlice
    coreTypeSoundnessEvalInferSlice_proved

theorem coreCalculusSoundnessDeclarativeInferSlice_consequences
    (h_slice : CoreCalculusSoundnessDeclarativeInferSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  h_slice h_env h_infer h_frag

theorem coreCalculusSoundnessDeclarativeInferSlice_soundness
    (h_slice : CoreCalculusSoundnessDeclarativeInferSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  (coreCalculusSoundnessDeclarativeInferSlice_consequences
    h_slice h_env h_infer h_frag).1

theorem coreCalculusSoundnessDeclarativeInferSlice_progress
    (h_slice : CoreCalculusSoundnessDeclarativeInferSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (coreCalculusSoundnessDeclarativeInferSlice_consequences
    h_slice h_env h_infer h_frag).2.1

theorem coreCalculusSoundnessDeclarativeInferSlice_preservation
    (h_slice : CoreCalculusSoundnessDeclarativeInferSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_infer : inferExpr tenv e = some ty)
    (h_frag : EvalFragmentFull e) :
    ∀ v, eval venv e = some v → ValueHasType v ty :=
  (coreCalculusSoundnessDeclarativeInferSlice_consequences
    h_slice h_env h_infer h_frag).2.2

theorem coreCalculusSoundnessDeclarativeInferSlice_of_coreCalculusSoundnessDeclarativeSlice
    (h_slice : CoreCalculusSoundnessDeclarativeSlice) :
    CoreCalculusSoundnessDeclarativeInferSlice := by
  intro tenv venv e ty h_env h_infer h_frag
  exact h_slice h_env (inferExpr_sound tenv e ty h_infer) h_frag

theorem coreCalculusSoundnessDeclarativeSlice_of_coreCalculusSoundnessDeclarativeInferSlice
    (h_slice : CoreCalculusSoundnessDeclarativeInferSlice) :
    CoreCalculusSoundnessDeclarativeSlice := by
  intro tenv venv e ty h_env h_ty h_frag
  exact h_slice h_env (inferExpr_complete tenv e ty h_ty) h_frag

theorem coreCalculusSoundnessDeclarativeSlice_iff_coreCalculusSoundnessDeclarativeInferSlice :
    CoreCalculusSoundnessDeclarativeSlice ↔ CoreCalculusSoundnessDeclarativeInferSlice := by
  constructor
  · exact coreCalculusSoundnessDeclarativeInferSlice_of_coreCalculusSoundnessDeclarativeSlice
  · exact coreCalculusSoundnessDeclarativeSlice_of_coreCalculusSoundnessDeclarativeInferSlice

theorem coreCalculusSoundnessDeclarativeSlice_proved_via_infer :
    CoreCalculusSoundnessDeclarativeSlice :=
  coreCalculusSoundnessDeclarativeSlice_of_coreCalculusSoundnessDeclarativeInferSlice
    coreCalculusSoundnessDeclarativeInferSlice_proved

theorem coreCalculusSoundnessDeclarativeInferSlice_proved_via_hasType :
    CoreCalculusSoundnessDeclarativeInferSlice :=
  coreCalculusSoundnessDeclarativeInferSlice_of_coreCalculusSoundnessDeclarativeSlice
    coreCalculusSoundnessDeclarativeSlice_proved

/--
Master declarative canonical-consequence suite packaging both `HasType` and
`inferExpr` global slices plus their key bridge equivalences.
-/
structure CoreCalculusSoundnessDeclarativeMasterSuite : Prop where
  hasTypeSlice : CoreCalculusSoundnessDeclarativeSlice
  inferSlice : CoreCalculusSoundnessDeclarativeInferSlice
  hasTypeInferIff :
    CoreCalculusSoundnessDeclarativeSlice ↔ CoreCalculusSoundnessDeclarativeInferSlice
  hasTypeEvalIff :
    CoreCalculusSoundnessDeclarativeSlice ↔ CoreTypeSoundnessEvalSlice
  inferEvalIff :
    CoreCalculusSoundnessDeclarativeInferSlice ↔ CoreTypeSoundnessEvalInferSlice

/-- Explicit component alias for `CoreCalculusSoundnessDeclarativeMasterSuite`. -/
abbrev CoreCalculusSoundnessDeclarativeMasterSuiteComponents : Prop :=
  CoreCalculusSoundnessDeclarativeSlice
    ∧ CoreCalculusSoundnessDeclarativeInferSlice
    ∧ (CoreCalculusSoundnessDeclarativeSlice ↔
        CoreCalculusSoundnessDeclarativeInferSlice)
    ∧ (CoreCalculusSoundnessDeclarativeSlice ↔ CoreTypeSoundnessEvalSlice)
    ∧ (CoreCalculusSoundnessDeclarativeInferSlice ↔ CoreTypeSoundnessEvalInferSlice)

theorem coreCalculusSoundnessDeclarativeMasterSuite_iff_components :
    CoreCalculusSoundnessDeclarativeMasterSuite ↔
      CoreCalculusSoundnessDeclarativeMasterSuiteComponents := by
  constructor
  · intro h
    exact ⟨h.hasTypeSlice, h.inferSlice, h.hasTypeInferIff, h.hasTypeEvalIff, h.inferEvalIff⟩
  · intro h
    exact {
      hasTypeSlice := h.1
      inferSlice := h.2.1
      hasTypeInferIff := h.2.2.1
      hasTypeEvalIff := h.2.2.2.1
      inferEvalIff := h.2.2.2.2
    }

theorem coreCalculusSoundnessDeclarativeMasterSuite_of_components
    (h_comp : CoreCalculusSoundnessDeclarativeMasterSuiteComponents) :
    CoreCalculusSoundnessDeclarativeMasterSuite :=
  (coreCalculusSoundnessDeclarativeMasterSuite_iff_components).2 h_comp

theorem coreCalculusSoundnessDeclarativeMasterSuite_as_components
    (h_suite : CoreCalculusSoundnessDeclarativeMasterSuite) :
    CoreCalculusSoundnessDeclarativeMasterSuiteComponents :=
  (coreCalculusSoundnessDeclarativeMasterSuite_iff_components).1 h_suite

theorem coreCalculusSoundnessDeclarativeMasterSuite_as_components_of_components
    (h_comp : CoreCalculusSoundnessDeclarativeMasterSuiteComponents) :
    CoreCalculusSoundnessDeclarativeMasterSuiteComponents :=
  (coreCalculusSoundnessDeclarativeMasterSuite_iff_components).1
    ((coreCalculusSoundnessDeclarativeMasterSuite_iff_components).2 h_comp)

theorem coreCalculusSoundnessDeclarativeMasterSuite_of_hasTypeSlice
    (h_hasType : CoreCalculusSoundnessDeclarativeSlice) :
    CoreCalculusSoundnessDeclarativeMasterSuite := by
  exact {
    hasTypeSlice := h_hasType
    inferSlice :=
      coreCalculusSoundnessDeclarativeInferSlice_of_coreCalculusSoundnessDeclarativeSlice h_hasType
    hasTypeInferIff := coreCalculusSoundnessDeclarativeSlice_iff_coreCalculusSoundnessDeclarativeInferSlice
    hasTypeEvalIff := coreCalculusSoundnessDeclarativeSlice_iff_coreTypeSoundnessEvalSlice
    inferEvalIff := coreCalculusSoundnessDeclarativeInferSlice_iff_coreTypeSoundnessEvalInferSlice
  }

theorem coreCalculusSoundnessDeclarativeMasterSuite_of_inferSlice
    (h_infer : CoreCalculusSoundnessDeclarativeInferSlice) :
    CoreCalculusSoundnessDeclarativeMasterSuite := by
  exact {
    hasTypeSlice :=
      coreCalculusSoundnessDeclarativeSlice_of_coreCalculusSoundnessDeclarativeInferSlice h_infer
    inferSlice := h_infer
    hasTypeInferIff := coreCalculusSoundnessDeclarativeSlice_iff_coreCalculusSoundnessDeclarativeInferSlice
    hasTypeEvalIff := coreCalculusSoundnessDeclarativeSlice_iff_coreTypeSoundnessEvalSlice
    inferEvalIff := coreCalculusSoundnessDeclarativeInferSlice_iff_coreTypeSoundnessEvalInferSlice
  }

theorem coreCalculusSoundnessDeclarativeMasterSuite_proved :
    CoreCalculusSoundnessDeclarativeMasterSuite :=
  coreCalculusSoundnessDeclarativeMasterSuite_of_hasTypeSlice
    coreCalculusSoundnessDeclarativeSlice_proved

theorem coreCalculusSoundnessDeclarativeMasterSuite_hasTypeSlice
    (h_suite : CoreCalculusSoundnessDeclarativeMasterSuite) :
    CoreCalculusSoundnessDeclarativeSlice :=
  h_suite.hasTypeSlice

theorem coreCalculusSoundnessDeclarativeMasterSuite_inferSlice
    (h_suite : CoreCalculusSoundnessDeclarativeMasterSuite) :
    CoreCalculusSoundnessDeclarativeInferSlice :=
  h_suite.inferSlice

theorem coreCalculusSoundnessDeclarativeMasterSuite_hasTypeInferIff
    (h_suite : CoreCalculusSoundnessDeclarativeMasterSuite) :
    CoreCalculusSoundnessDeclarativeSlice ↔ CoreCalculusSoundnessDeclarativeInferSlice :=
  h_suite.hasTypeInferIff

theorem coreCalculusSoundnessDeclarativeMasterSuite_hasTypeEvalIff
    (h_suite : CoreCalculusSoundnessDeclarativeMasterSuite) :
    CoreCalculusSoundnessDeclarativeSlice ↔ CoreTypeSoundnessEvalSlice :=
  h_suite.hasTypeEvalIff

theorem coreCalculusSoundnessDeclarativeMasterSuite_inferEvalIff
    (h_suite : CoreCalculusSoundnessDeclarativeMasterSuite) :
    CoreCalculusSoundnessDeclarativeInferSlice ↔ CoreTypeSoundnessEvalInferSlice :=
  h_suite.inferEvalIff

theorem coreCalculusSoundnessDeclarativeMasterSuite_as_components_of_hasTypeSlice
    (h_hasType : CoreCalculusSoundnessDeclarativeSlice) :
    CoreCalculusSoundnessDeclarativeMasterSuiteComponents :=
  coreCalculusSoundnessDeclarativeMasterSuite_as_components
    (coreCalculusSoundnessDeclarativeMasterSuite_of_hasTypeSlice h_hasType)

theorem coreCalculusSoundnessDeclarativeMasterSuite_as_components_of_inferSlice
    (h_infer : CoreCalculusSoundnessDeclarativeInferSlice) :
    CoreCalculusSoundnessDeclarativeMasterSuiteComponents :=
  coreCalculusSoundnessDeclarativeMasterSuite_as_components
    (coreCalculusSoundnessDeclarativeMasterSuite_of_inferSlice h_infer)

theorem coreCalculusSoundnessDeclarativeMasterSuite_hasTypeSlice_proved :
    CoreCalculusSoundnessDeclarativeSlice :=
  coreCalculusSoundnessDeclarativeMasterSuite_hasTypeSlice
    coreCalculusSoundnessDeclarativeMasterSuite_proved

theorem coreCalculusSoundnessDeclarativeMasterSuite_inferSlice_proved :
    CoreCalculusSoundnessDeclarativeInferSlice :=
  coreCalculusSoundnessDeclarativeMasterSuite_inferSlice
    coreCalculusSoundnessDeclarativeMasterSuite_proved

theorem coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSlice
    (h_core : CoreCalculusSoundnessSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty := by
  exact ⟨h_core.1 h_hooks st st' fuel h_ok h_env h_frag,
    h_core.2 h_hooks st st' fuel h_ok h_env h_frag⟩

theorem coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSliceFromHooks
    (h_core : CoreCalculusSoundnessSliceFromHooks)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty := by
  exact ⟨h_core.1 h_app h_proj st st' fuel h_ok h_env h_frag,
    h_core.2 h_app h_proj st st' fuel h_ok h_env h_frag⟩

theorem coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSlice_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSlice
    coreCalculusSoundnessSlice_proved
    h_hooks st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSliceFromHooks_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreCalculusSoundnessConsequences tenv venv e ty :=
  coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSliceFromHooks
    coreCalculusSoundnessSliceFromHooks_proved
    h_app h_proj st st' fuel h_ok h_env h_frag

/--
Packaged run-local canonical consequence surface from successful unification
inference (bundled hook route).
-/
def CoreCalculusSoundnessConsequencesSlice : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_hooks : UnifyHookPremises) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreCalculusSoundnessConsequences tenv venv e ty

/-- Explicit component alias for `CoreCalculusSoundnessConsequencesSlice`. -/
abbrev CoreCalculusSoundnessConsequencesSliceComponents : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_hooks : UnifyHookPremises) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreCalculusSoundnessConsequences tenv venv e ty

theorem coreCalculusSoundnessConsequencesSlice_iff_components :
    CoreCalculusSoundnessConsequencesSlice ↔
      CoreCalculusSoundnessConsequencesSliceComponents := Iff.rfl

theorem coreCalculusSoundnessConsequencesSlice_of_components
    (h_comp : CoreCalculusSoundnessConsequencesSliceComponents) :
    CoreCalculusSoundnessConsequencesSlice :=
  (coreCalculusSoundnessConsequencesSlice_iff_components).2 h_comp

theorem coreCalculusSoundnessConsequencesSlice_as_components
    (h_slice : CoreCalculusSoundnessConsequencesSlice) :
    CoreCalculusSoundnessConsequencesSliceComponents :=
  (coreCalculusSoundnessConsequencesSlice_iff_components).1 h_slice

theorem coreCalculusSoundnessConsequencesSlice_as_components_of_components
    (h_comp : CoreCalculusSoundnessConsequencesSliceComponents) :
    CoreCalculusSoundnessConsequencesSliceComponents :=
  (coreCalculusSoundnessConsequencesSlice_iff_components).1
    ((coreCalculusSoundnessConsequencesSlice_iff_components).2 h_comp)

theorem coreCalculusSoundnessConsequencesSlice_proved :
    CoreCalculusSoundnessConsequencesSlice := by
  intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
  exact coreCalculusSoundnessConsequences_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag

/--
Packaged run-local canonical consequence surface from successful unification
inference (explicit hook route).
-/
def CoreCalculusSoundnessConsequencesSliceFromHooks : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_app : AppUnifySoundHook) →
    (h_proj : ProjUnifySoundHook) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreCalculusSoundnessConsequences tenv venv e ty

/-- Explicit component alias for `CoreCalculusSoundnessConsequencesSliceFromHooks`. -/
abbrev CoreCalculusSoundnessConsequencesSliceFromHooksComponents : Prop :=
  ∀ {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty},
    (h_app : AppUnifySoundHook) →
    (h_proj : ProjUnifySoundHook) →
    (st st' : UnifyState) →
    (fuel : Nat) →
    inferExprUnify st fuel tenv e = .ok st' ty →
    EnvWellTyped tenv venv →
    EvalFragmentFull e →
    CoreCalculusSoundnessConsequences tenv venv e ty

theorem coreCalculusSoundnessConsequencesSliceFromHooks_iff_components :
    CoreCalculusSoundnessConsequencesSliceFromHooks ↔
      CoreCalculusSoundnessConsequencesSliceFromHooksComponents := Iff.rfl

theorem coreCalculusSoundnessConsequencesSliceFromHooks_of_components
    (h_comp : CoreCalculusSoundnessConsequencesSliceFromHooksComponents) :
    CoreCalculusSoundnessConsequencesSliceFromHooks :=
  (coreCalculusSoundnessConsequencesSliceFromHooks_iff_components).2 h_comp

theorem coreCalculusSoundnessConsequencesSliceFromHooks_as_components
    (h_slice : CoreCalculusSoundnessConsequencesSliceFromHooks) :
    CoreCalculusSoundnessConsequencesSliceFromHooksComponents :=
  (coreCalculusSoundnessConsequencesSliceFromHooks_iff_components).1 h_slice

theorem coreCalculusSoundnessConsequencesSliceFromHooks_as_components_of_components
    (h_comp : CoreCalculusSoundnessConsequencesSliceFromHooksComponents) :
    CoreCalculusSoundnessConsequencesSliceFromHooksComponents :=
  (coreCalculusSoundnessConsequencesSliceFromHooks_iff_components).1
    ((coreCalculusSoundnessConsequencesSliceFromHooks_iff_components).2 h_comp)

theorem coreCalculusSoundnessConsequencesSliceFromHooks_proved :
    CoreCalculusSoundnessConsequencesSliceFromHooks := by
  intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
  exact coreCalculusSoundnessConsequences_of_inferUnify_from_hooks
    h_app h_proj st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessConsequencesSlice_of_coreTypeSoundnessEvalUnifySlice
    (h_slice : CoreTypeSoundnessEvalUnifySlice) :
    CoreCalculusSoundnessConsequencesSlice := by
  intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
  exact coreCalculusSoundnessConsequences_of_bundle tenv venv e ty
    (h_slice h_hooks st st' fuel h_ok h_env h_frag)

theorem coreCalculusSoundnessConsequencesSliceFromHooks_of_coreTypeSoundnessEvalUnifySliceFromHooks
    (h_slice : CoreTypeSoundnessEvalUnifySliceFromHooks) :
    CoreCalculusSoundnessConsequencesSliceFromHooks := by
  intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
  exact coreCalculusSoundnessConsequences_of_bundle tenv venv e ty
    (h_slice h_app h_proj st st' fuel h_ok h_env h_frag)

theorem coreTypeSoundnessEvalUnifySlice_of_coreCalculusSoundnessConsequencesSlice
    (h_slice : CoreCalculusSoundnessConsequencesSlice) :
    CoreTypeSoundnessEvalUnifySlice := by
  intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
  exact coreCalculusSoundnessConsequences_as_bundle tenv venv e ty
    (h_slice h_hooks st st' fuel h_ok h_env h_frag)

theorem coreTypeSoundnessEvalUnifySliceFromHooks_of_coreCalculusSoundnessConsequencesSliceFromHooks
    (h_slice : CoreCalculusSoundnessConsequencesSliceFromHooks) :
    CoreTypeSoundnessEvalUnifySliceFromHooks := by
  intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
  exact coreCalculusSoundnessConsequences_as_bundle tenv venv e ty
    (h_slice h_app h_proj st st' fuel h_ok h_env h_frag)

theorem coreCalculusSoundnessConsequencesSlice_iff_coreTypeSoundnessEvalUnifySlice :
    CoreCalculusSoundnessConsequencesSlice ↔ CoreTypeSoundnessEvalUnifySlice := by
  constructor
  · exact coreTypeSoundnessEvalUnifySlice_of_coreCalculusSoundnessConsequencesSlice
  · exact coreCalculusSoundnessConsequencesSlice_of_coreTypeSoundnessEvalUnifySlice

theorem coreCalculusSoundnessConsequencesSliceFromHooks_iff_coreTypeSoundnessEvalUnifySliceFromHooks :
    CoreCalculusSoundnessConsequencesSliceFromHooks ↔
      CoreTypeSoundnessEvalUnifySliceFromHooks := by
  constructor
  · exact coreTypeSoundnessEvalUnifySliceFromHooks_of_coreCalculusSoundnessConsequencesSliceFromHooks
  · exact coreCalculusSoundnessConsequencesSliceFromHooks_of_coreTypeSoundnessEvalUnifySliceFromHooks

theorem coreCalculusSoundnessConsequencesSlice_of_coreTypeSoundnessEvalUnifySlice_proved :
    CoreCalculusSoundnessConsequencesSlice :=
  coreCalculusSoundnessConsequencesSlice_of_coreTypeSoundnessEvalUnifySlice
    coreTypeSoundnessEvalUnifySlice_proved

theorem coreCalculusSoundnessConsequencesSliceFromHooks_of_coreTypeSoundnessEvalUnifySliceFromHooks_proved :
    CoreCalculusSoundnessConsequencesSliceFromHooks :=
  coreCalculusSoundnessConsequencesSliceFromHooks_of_coreTypeSoundnessEvalUnifySliceFromHooks
    coreTypeSoundnessEvalUnifySliceFromHooks_proved

theorem coreTypeSoundnessEvalUnifySlice_of_coreCalculusSoundnessConsequencesSlice_proved :
    CoreTypeSoundnessEvalUnifySlice :=
  coreTypeSoundnessEvalUnifySlice_of_coreCalculusSoundnessConsequencesSlice
    coreCalculusSoundnessConsequencesSlice_proved

theorem coreTypeSoundnessEvalUnifySliceFromHooks_of_coreCalculusSoundnessConsequencesSliceFromHooks_proved :
    CoreTypeSoundnessEvalUnifySliceFromHooks :=
  coreTypeSoundnessEvalUnifySliceFromHooks_of_coreCalculusSoundnessConsequencesSliceFromHooks
    coreCalculusSoundnessConsequencesSliceFromHooks_proved

theorem coreCalculusSoundnessConsequencesSlice_of_coreCalculusSoundnessSlice
    (h_core : CoreCalculusSoundnessSlice) :
    CoreCalculusSoundnessConsequencesSlice := by
  intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
  exact coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSlice
    h_core h_hooks st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessConsequencesSliceFromHooks_of_coreCalculusSoundnessSliceFromHooks
    (h_core : CoreCalculusSoundnessSliceFromHooks) :
    CoreCalculusSoundnessConsequencesSliceFromHooks := by
  intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
  exact coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSliceFromHooks
    h_core h_app h_proj st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessSlice_of_coreCalculusSoundnessConsequencesSlice
    (h_cons : CoreCalculusSoundnessConsequencesSlice) :
    CoreCalculusSoundnessSlice :=
  coreCalculusSoundnessSlice_of_coreTypeSoundnessEvalUnifySlice
    (coreTypeSoundnessEvalUnifySlice_of_coreCalculusSoundnessConsequencesSlice h_cons)

theorem coreCalculusSoundnessSliceFromHooks_of_coreCalculusSoundnessConsequencesSliceFromHooks
    (h_cons : CoreCalculusSoundnessConsequencesSliceFromHooks) :
    CoreCalculusSoundnessSliceFromHooks :=
  coreCalculusSoundnessSliceFromHooks_of_coreTypeSoundnessEvalUnifySliceFromHooks
    (coreTypeSoundnessEvalUnifySliceFromHooks_of_coreCalculusSoundnessConsequencesSliceFromHooks h_cons)

theorem coreCalculusSoundnessConsequencesSlice_iff_coreCalculusSoundnessSlice :
    CoreCalculusSoundnessConsequencesSlice ↔ CoreCalculusSoundnessSlice := by
  constructor
  · exact coreCalculusSoundnessSlice_of_coreCalculusSoundnessConsequencesSlice
  · exact coreCalculusSoundnessConsequencesSlice_of_coreCalculusSoundnessSlice

theorem coreCalculusSoundnessConsequencesSliceFromHooks_iff_coreCalculusSoundnessSliceFromHooks :
    CoreCalculusSoundnessConsequencesSliceFromHooks ↔ CoreCalculusSoundnessSliceFromHooks := by
  constructor
  · exact coreCalculusSoundnessSliceFromHooks_of_coreCalculusSoundnessConsequencesSliceFromHooks
  · exact coreCalculusSoundnessConsequencesSliceFromHooks_of_coreCalculusSoundnessSliceFromHooks

theorem coreCalculusSoundnessConsequencesSlice_of_coreCalculusSoundnessSlice_proved :
    CoreCalculusSoundnessConsequencesSlice :=
  coreCalculusSoundnessConsequencesSlice_of_coreCalculusSoundnessSlice
    coreCalculusSoundnessSlice_proved

theorem coreCalculusSoundnessConsequencesSliceFromHooks_of_coreCalculusSoundnessSliceFromHooks_proved :
    CoreCalculusSoundnessConsequencesSliceFromHooks :=
  coreCalculusSoundnessConsequencesSliceFromHooks_of_coreCalculusSoundnessSliceFromHooks
    coreCalculusSoundnessSliceFromHooks_proved

theorem coreCalculusSoundnessSlice_of_coreCalculusSoundnessConsequencesSlice_proved :
    CoreCalculusSoundnessSlice :=
  coreCalculusSoundnessSlice_of_coreCalculusSoundnessConsequencesSlice
    coreCalculusSoundnessConsequencesSlice_proved

theorem coreCalculusSoundnessSliceFromHooks_of_coreCalculusSoundnessConsequencesSliceFromHooks_proved :
    CoreCalculusSoundnessSliceFromHooks :=
  coreCalculusSoundnessSliceFromHooks_of_coreCalculusSoundnessConsequencesSliceFromHooks
    coreCalculusSoundnessConsequencesSliceFromHooks_proved

theorem coreCalculusSoundnessConsequencesSlice_soundness
    (h_slice : CoreCalculusSoundnessConsequencesSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  (h_slice h_hooks st st' fuel h_ok h_env h_frag).1

theorem coreCalculusSoundnessConsequencesSlice_progress
    (h_slice : CoreCalculusSoundnessConsequencesSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (h_slice h_hooks st st' fuel h_ok h_env h_frag).2.1

theorem coreCalculusSoundnessConsequencesSlice_preservation
    (h_slice : CoreCalculusSoundnessConsequencesSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  (h_slice h_hooks st st' fuel h_ok h_env h_frag).2.2

theorem coreCalculusSoundnessConsequencesSliceFromHooks_soundness
    (h_slice : CoreCalculusSoundnessConsequencesSliceFromHooks)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  (h_slice h_app h_proj st st' fuel h_ok h_env h_frag).1

theorem coreCalculusSoundnessConsequencesSliceFromHooks_progress
    (h_slice : CoreCalculusSoundnessConsequencesSliceFromHooks)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (h_slice h_app h_proj st st' fuel h_ok h_env h_frag).2.1

theorem coreCalculusSoundnessConsequencesSliceFromHooks_preservation
    (h_slice : CoreCalculusSoundnessConsequencesSliceFromHooks)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  (h_slice h_app h_proj st st' fuel h_ok h_env h_frag).2.2

theorem coreTypeSoundnessEvalUnifyBundle_of_coreCalculusSoundnessSlice
    (h_core : CoreCalculusSoundnessSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  coreCalculusSoundnessConsequences_as_bundle tenv venv e ty
    (coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSlice
      h_core h_hooks st st' fuel h_ok h_env h_frag)

theorem coreTypeSoundnessEvalUnifyBundle_of_coreCalculusSoundnessSliceFromHooks
    (h_core : CoreCalculusSoundnessSliceFromHooks)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  coreCalculusSoundnessConsequences_as_bundle tenv venv e ty
    (coreCalculusSoundnessConsequences_of_coreCalculusSoundnessSliceFromHooks
      h_core h_app h_proj st st' fuel h_ok h_env h_frag)

theorem coreTypeSoundnessEvalUnifyBundle_as_components_of_coreCalculusSoundnessSlice
    (h_core : CoreCalculusSoundnessSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundleComponents tenv venv e ty :=
  coreTypeSoundnessEvalUnifyBundle_as_components tenv venv e ty
    (coreTypeSoundnessEvalUnifyBundle_of_coreCalculusSoundnessSlice
      h_core h_hooks st st' fuel h_ok h_env h_frag)

theorem coreTypeSoundnessEvalUnifyBundle_as_components_of_coreCalculusSoundnessSliceFromHooks
    (h_core : CoreCalculusSoundnessSliceFromHooks)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundleComponents tenv venv e ty :=
  coreTypeSoundnessEvalUnifyBundle_as_components tenv venv e ty
    (coreTypeSoundnessEvalUnifyBundle_of_coreCalculusSoundnessSliceFromHooks
      h_core h_app h_proj st st' fuel h_ok h_env h_frag)

theorem coreTypeSoundnessEvalUnifyBundle_of_coreCalculusSoundnessSlice_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  coreTypeSoundnessEvalUnifyBundle_of_coreCalculusSoundnessSlice
    coreCalculusSoundnessSlice_proved
    h_hooks st st' fuel h_ok h_env h_frag

theorem coreTypeSoundnessEvalUnifyBundle_of_coreCalculusSoundnessSliceFromHooks_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    CoreTypeSoundnessEvalUnifyBundle tenv venv e ty :=
  coreTypeSoundnessEvalUnifyBundle_of_coreCalculusSoundnessSliceFromHooks
    coreCalculusSoundnessSliceFromHooks_proved
    h_app h_proj st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessSlice_soundness
    (h_core : CoreCalculusSoundnessSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  h_core.1 h_hooks st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessSlice_progress
    (h_core : CoreCalculusSoundnessSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (h_core.2 h_hooks st st' fuel h_ok h_env h_frag).1

theorem coreCalculusSoundnessSlice_preservation
    (h_core : CoreCalculusSoundnessSlice)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  (h_core.2 h_hooks st st' fuel h_ok h_env h_frag).2

theorem coreCalculusSoundnessSliceFromHooks_soundness
    (h_core : CoreCalculusSoundnessSliceFromHooks)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  h_core.1 h_app h_proj st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessSliceFromHooks_progress
    (h_core : CoreCalculusSoundnessSliceFromHooks)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (h_core.2 h_app h_proj st st' fuel h_ok h_env h_frag).1

theorem coreCalculusSoundnessSliceFromHooks_preservation
    (h_core : CoreCalculusSoundnessSliceFromHooks)
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  (h_core.2 h_app h_proj st st' fuel h_ok h_env h_frag).2

theorem coreCalculusSoundnessSlice_soundness_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  coreCalculusSoundnessSlice_soundness
    coreCalculusSoundnessSlice_proved
    h_hooks st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessSlice_progress_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  coreCalculusSoundnessSlice_progress
    coreCalculusSoundnessSlice_proved
    h_hooks st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessSlice_preservation_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  coreCalculusSoundnessSlice_preservation
    coreCalculusSoundnessSlice_proved
    h_hooks st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessSliceFromHooks_soundness_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  coreCalculusSoundnessSliceFromHooks_soundness
    coreCalculusSoundnessSliceFromHooks_proved
    h_app h_proj st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessSliceFromHooks_progress_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  coreCalculusSoundnessSliceFromHooks_progress
    coreCalculusSoundnessSliceFromHooks_proved
    h_app h_proj st st' fuel h_ok h_env h_frag

theorem coreCalculusSoundnessSliceFromHooks_preservation_proved
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  coreCalculusSoundnessSliceFromHooks_preservation
    coreCalculusSoundnessSliceFromHooks_proved
    h_app h_proj st st' fuel h_ok h_env h_frag

/--
Canonical soundness consequence from successful unification-threaded inference
(bundled hook route).
-/
theorem coreCalculusSoundness_soundness_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  (coreCalculusSoundness_consequences_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag).1

/--
Canonical progress consequence from successful unification-threaded inference
(bundled hook route).
-/
theorem coreCalculusSoundness_progress_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (coreCalculusSoundness_consequences_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag).2.1

/--
Canonical preservation consequence from successful unification-threaded inference
(bundled hook route).
-/
theorem coreCalculusSoundness_preservation_of_inferUnify
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_hooks : UnifyHookPremises)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  (coreCalculusSoundness_consequences_of_inferUnify
    h_hooks st st' fuel h_ok h_env h_frag).2.2

/--
Canonical soundness consequence from successful unification-threaded inference
(explicit hook route).
-/
theorem coreCalculusSoundness_soundness_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
  (coreCalculusSoundness_consequences_of_inferUnify_from_hooks
    h_app h_proj st st' fuel h_ok h_env h_frag).1

/--
Canonical progress consequence from successful unification-threaded inference
(explicit hook route).
-/
theorem coreCalculusSoundness_progress_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∃ v, eval venv e = some v :=
  (coreCalculusSoundness_consequences_of_inferUnify_from_hooks
    h_app h_proj st st' fuel h_ok h_env h_frag).2.1

/--
Canonical preservation consequence from successful unification-threaded
inference (explicit hook route).
-/
theorem coreCalculusSoundness_preservation_of_inferUnify_from_hooks
    {tenv : TermEnv} {venv : ValueEnv} {e : CoreExpr} {ty : Ty}
    (h_app : AppUnifySoundHook)
    (h_proj : ProjUnifySoundHook)
    (st st' : UnifyState)
    (fuel : Nat)
    (h_ok : inferExprUnify st fuel tenv e = .ok st' ty)
    (h_env : EnvWellTyped tenv venv)
    (h_frag : EvalFragmentFull e) :
    ∀ {v : Value}, eval venv e = some v → ValueHasType v ty :=
  (coreCalculusSoundness_consequences_of_inferUnify_from_hooks
    h_app h_proj st st' fuel h_ok h_env h_frag).2.2

/--
Canonical core-calculus soundness package for unification-threaded runs:
the existing evaluator soundness slice plus the existing progress/preservation
slice.
-/
def CoreCalculusSoundnessSlice : Prop :=
  VerticalEvalUnifyBridgeSlice ∧ CoreProgressPreservationEvalUnifySlice

/-- Explicit component alias for `CoreCalculusSoundnessSlice`. -/
abbrev CoreCalculusSoundnessSliceComponents : Prop :=
  VerticalEvalUnifyBridgeSlice ∧ CoreProgressPreservationEvalUnifySlice

/-- `CoreCalculusSoundnessSlice` is equivalent to explicit components. -/
theorem coreCalculusSoundnessSlice_iff_components :
    CoreCalculusSoundnessSlice ↔ CoreCalculusSoundnessSliceComponents := Iff.rfl

/-- Build `CoreCalculusSoundnessSlice` from explicit components. -/
theorem coreCalculusSoundnessSlice_of_components
    (h_comp : CoreCalculusSoundnessSliceComponents) :
    CoreCalculusSoundnessSlice :=
  (coreCalculusSoundnessSlice_iff_components).2 h_comp

/-- Decompose `CoreCalculusSoundnessSlice` into explicit components. -/
theorem coreCalculusSoundnessSlice_as_components
    (h_core : CoreCalculusSoundnessSlice) :
    CoreCalculusSoundnessSliceComponents :=
  (coreCalculusSoundnessSlice_iff_components).1 h_core

/-- Direct components-route decomposition for `CoreCalculusSoundnessSlice`. -/
theorem coreCalculusSoundnessSlice_as_components_of_components
    (h_comp : CoreCalculusSoundnessSliceComponents) :
    CoreCalculusSoundnessSliceComponents :=
  (coreCalculusSoundnessSlice_iff_components).1
    ((coreCalculusSoundnessSlice_iff_components).2 h_comp)

/-- The canonical bundled core-calculus soundness slice is fully proved. -/
theorem coreCalculusSoundnessSlice_proved : CoreCalculusSoundnessSlice := by
  exact ⟨verticalEvalUnifyBridgeSlice_proved, coreProgressPreservationEvalUnifySlice_proved⟩

/--
Hook-parameterized canonical core-calculus soundness package for
unification-threaded runs.
-/
def CoreCalculusSoundnessSliceFromHooks : Prop :=
  VerticalEvalUnifyBridgeSliceFromHooks ∧ CoreProgressPreservationEvalUnifySliceFromHooks

/-- Explicit component alias for `CoreCalculusSoundnessSliceFromHooks`. -/
abbrev CoreCalculusSoundnessSliceFromHooksComponents : Prop :=
  VerticalEvalUnifyBridgeSliceFromHooks ∧ CoreProgressPreservationEvalUnifySliceFromHooks

/-- `CoreCalculusSoundnessSliceFromHooks` is equivalent to explicit components. -/
theorem coreCalculusSoundnessSliceFromHooks_iff_components :
    CoreCalculusSoundnessSliceFromHooks ↔
      CoreCalculusSoundnessSliceFromHooksComponents := Iff.rfl

/-- Build `CoreCalculusSoundnessSliceFromHooks` from explicit components. -/
theorem coreCalculusSoundnessSliceFromHooks_of_components
    (h_comp : CoreCalculusSoundnessSliceFromHooksComponents) :
    CoreCalculusSoundnessSliceFromHooks :=
  (coreCalculusSoundnessSliceFromHooks_iff_components).2 h_comp

/--
Decompose `CoreCalculusSoundnessSliceFromHooks` into explicit components.
-/
theorem coreCalculusSoundnessSliceFromHooks_as_components
    (h_core : CoreCalculusSoundnessSliceFromHooks) :
    CoreCalculusSoundnessSliceFromHooksComponents :=
  (coreCalculusSoundnessSliceFromHooks_iff_components).1 h_core

/--
Direct components-route decomposition for
`CoreCalculusSoundnessSliceFromHooks`.
-/
theorem coreCalculusSoundnessSliceFromHooks_as_components_of_components
    (h_comp : CoreCalculusSoundnessSliceFromHooksComponents) :
    CoreCalculusSoundnessSliceFromHooksComponents :=
  (coreCalculusSoundnessSliceFromHooks_iff_components).1
    ((coreCalculusSoundnessSliceFromHooks_iff_components).2 h_comp)

/--
The hook-parameterized bundled core-calculus soundness slice is fully proved.
-/
theorem coreCalculusSoundnessSliceFromHooks_proved :
    CoreCalculusSoundnessSliceFromHooks := by
  exact
    ⟨verticalEvalUnifyBridgeSliceFromHooks_proved,
      coreProgressPreservationEvalUnifySliceFromHooks_proved⟩

/--
Bridge from the canonical core-calculus soundness package to the packaged
core-soundness-bundle slice.
-/
theorem coreTypeSoundnessEvalUnifySlice_of_coreCalculusSoundnessSlice
    (h_core : CoreCalculusSoundnessSlice) :
    CoreTypeSoundnessEvalUnifySlice := by
  intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
  have h_sound :
      ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
    h_core.1 h_hooks st st' fuel h_ok h_env h_frag
  have h_progressPres :
      CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
    h_core.2 h_hooks st st' fuel h_ok h_env h_frag
  exact
    (coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
      tenv venv e ty).2 ⟨h_sound, h_progressPres⟩

/--
Hook-parameterized bridge from the canonical core-calculus soundness package to
the packaged core-soundness-bundle slice.
-/
theorem coreTypeSoundnessEvalUnifySliceFromHooks_of_coreCalculusSoundnessSliceFromHooks
    (h_core : CoreCalculusSoundnessSliceFromHooks) :
    CoreTypeSoundnessEvalUnifySliceFromHooks := by
  intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
  have h_sound :
      ∃ v, eval venv e = some v ∧ ValueHasType v ty :=
    h_core.1 h_app h_proj st st' fuel h_ok h_env h_frag
  have h_progressPres :
      CoreProgressPreservationEvalFragmentFull tenv venv e ty :=
    h_core.2 h_app h_proj st st' fuel h_ok h_env h_frag
  exact
    (coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
      tenv venv e ty).2 ⟨h_sound, h_progressPres⟩

/--
Proved-route convenience wrapper from canonical bundled core-calculus
soundness to the packaged core-soundness slice.
-/
theorem coreTypeSoundnessEvalUnifySlice_of_coreCalculusSoundnessSlice_proved :
    CoreTypeSoundnessEvalUnifySlice :=
  coreTypeSoundnessEvalUnifySlice_of_coreCalculusSoundnessSlice
    coreCalculusSoundnessSlice_proved

/--
Proved-route convenience wrapper from canonical explicit-hook bundled
core-calculus soundness to the packaged core-soundness slice.
-/
theorem coreTypeSoundnessEvalUnifySliceFromHooks_of_coreCalculusSoundnessSliceFromHooks_proved :
    CoreTypeSoundnessEvalUnifySliceFromHooks :=
  coreTypeSoundnessEvalUnifySliceFromHooks_of_coreCalculusSoundnessSliceFromHooks
    coreCalculusSoundnessSliceFromHooks_proved

/--
Reverse bridge: recover the canonical core-calculus soundness package from the
packaged core-soundness-bundle slice.
-/
theorem coreCalculusSoundnessSlice_of_coreTypeSoundnessEvalUnifySlice
    (h_bundleSlice : CoreTypeSoundnessEvalUnifySlice) :
    CoreCalculusSoundnessSlice := by
  refine ⟨?_, ?_⟩
  · intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
    exact (h_bundleSlice h_hooks st st' fuel h_ok h_env h_frag).soundness
  · intro tenv venv e ty h_hooks st st' fuel h_ok h_env h_frag
    have h_bundle :=
      h_bundleSlice h_hooks st st' fuel h_ok h_env h_frag
    exact
      (coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
        tenv venv e ty).1 h_bundle |>.2

/--
Hook-parameterized reverse bridge from the packaged core-soundness-bundle
slice to the canonical core-calculus soundness package.
-/
theorem coreCalculusSoundnessSliceFromHooks_of_coreTypeSoundnessEvalUnifySliceFromHooks
    (h_bundleSlice : CoreTypeSoundnessEvalUnifySliceFromHooks) :
    CoreCalculusSoundnessSliceFromHooks := by
  refine ⟨?_, ?_⟩
  · intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
    exact (h_bundleSlice h_app h_proj st st' fuel h_ok h_env h_frag).soundness
  · intro tenv venv e ty h_app h_proj st st' fuel h_ok h_env h_frag
    have h_bundle :=
      h_bundleSlice h_app h_proj st st' fuel h_ok h_env h_frag
    exact
      (coreTypeSoundnessEvalUnifyBundle_iff_soundness_and_coreProgressPreservation
        tenv venv e ty).1 h_bundle |>.2

/--
Canonical and packaged core-soundness slice families are equivalent (bundled
hook route).
-/
theorem coreCalculusSoundnessSlice_iff_coreTypeSoundnessEvalUnifySlice :
    CoreCalculusSoundnessSlice ↔ CoreTypeSoundnessEvalUnifySlice := by
  constructor
  · exact coreTypeSoundnessEvalUnifySlice_of_coreCalculusSoundnessSlice
  · exact coreCalculusSoundnessSlice_of_coreTypeSoundnessEvalUnifySlice

/--
Canonical and packaged core-soundness slice families are equivalent (explicit
hook route).
-/
theorem coreCalculusSoundnessSliceFromHooks_iff_coreTypeSoundnessEvalUnifySliceFromHooks :
    CoreCalculusSoundnessSliceFromHooks ↔ CoreTypeSoundnessEvalUnifySliceFromHooks := by
  constructor
  · exact coreTypeSoundnessEvalUnifySliceFromHooks_of_coreCalculusSoundnessSliceFromHooks
  · exact coreCalculusSoundnessSliceFromHooks_of_coreTypeSoundnessEvalUnifySliceFromHooks

/--
Proved-route convenience wrapper from packaged core-soundness slice back to
the canonical bundled core-calculus soundness pair.
-/
theorem coreCalculusSoundnessSlice_of_coreTypeSoundnessEvalUnifySlice_proved :
    CoreCalculusSoundnessSlice :=
  coreCalculusSoundnessSlice_of_coreTypeSoundnessEvalUnifySlice
    coreTypeSoundnessEvalUnifySlice_proved

/--
Proved-route convenience wrapper from packaged explicit-hook core-soundness
slice back to the canonical explicit-hook core-calculus soundness pair.
-/
theorem coreCalculusSoundnessSliceFromHooks_of_coreTypeSoundnessEvalUnifySliceFromHooks_proved :
    CoreCalculusSoundnessSliceFromHooks :=
  coreCalculusSoundnessSliceFromHooks_of_coreTypeSoundnessEvalUnifySliceFromHooks
    coreTypeSoundnessEvalUnifySliceFromHooks_proved

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

/-!
  Minimal handler-step boundary scaffold.

  `CoreExpr`/`HasType` in `Kea/Typing.lean` currently model the pure evaluator
  core only (no `handle`/`resume` constructors). This section introduces an
  explicit handler-step judgment boundary inside `Kea/Eval.lean` so the open
  preservation gap for handler reduction is machine-checkable.
-/
namespace HandlerStepBoundary

abbrev HandleContract := HandleClauseContract.HandleContract

/-- Minimal semantic shape of a single handler clause. -/
structure HandlerClauseSem where
  handled : Label
  argName : String
  kName : String
  opArgTy : Ty
  opRetTy : Ty
  body : CoreExpr
  instantiate : CoreExpr → CoreExpr → CoreExpr
  instantiate_sound :
    ∀ {tenv : TermEnv} {ty : Ty} {arg k : CoreExpr},
      HasType tenv arg opArgTy →
      HasType tenv k (continuationTy opRetTy ty) →
      HasType
        ((kName, continuationTy opRetTy ty) ::
          (argName, opArgTy) ::
          tenv)
        body
        ty →
      HasType tenv (instantiate arg k) ty
  contract : HandleClauseContract

/-- Continuation type used by the minimal handler-step boundary model. -/
def continuationTy (opRetTy handlerTy : Ty) : Ty :=
  .function (.cons opRetTy .nil) handlerTy

/-- Minimal effectful expression layer for handler-step boundary statements. -/
inductive HandlerExpr : Type where
  | core : CoreExpr → HandlerExpr
  | perform : Label → Ty → Ty → CoreExpr → CoreExpr → HandlerExpr
  | handle : HandlerExpr → HandleContract → HandlerClauseSem → HandlerExpr

/--
Placeholder binder for the handler reduction result.
The substitution behavior is abstracted by `HandlerClauseSem.instantiate`.
-/
def bindTailResumptive (clause : HandlerClauseSem) (_arg _k : CoreExpr) : CoreExpr :=
  clause.instantiate _arg _k

/-- Minimal typing judgment for `HandlerExpr` used by boundary propositions. -/
inductive HandlerHasType : TermEnv → HandlerExpr → Ty → Prop where
  | core (tenv : TermEnv) (e : CoreExpr) (ty : Ty)
      (h_core : HasType tenv e ty) :
      HandlerHasType tenv (.core e) ty
  | perform (tenv : TermEnv) (op : Label) (argTy opRetTy handlerTy : Ty)
      (arg k : CoreExpr)
      (h_arg : HasType tenv arg argTy)
      (h_k : HasType tenv k (continuationTy opRetTy handlerTy)) :
      HandlerHasType tenv (.perform op argTy opRetTy arg k) handlerTy
  | handle (tenv : TermEnv) (body : HandlerExpr) (handler : HandleContract)
      (clause : HandlerClauseSem) (ty : Ty)
      (h_body : HandlerHasType tenv body ty)
      (h_contract_shape : clause.contract.handled = clause.handled)
      (h_mem : clause.contract ∈ handler.clauses)
      (h_clause_contract : HandleClauseContract.wellTypedSlice clause.contract)
      (h_clause_body :
        HasType
          ((clause.kName, continuationTy clause.opRetTy ty) ::
            (clause.argName, clause.opArgTy) ::
            tenv)
          clause.body
          ty) :
      HandlerHasType tenv (.handle body handler clause) ty

/--
Single handler-step rule at the current boundary:
`handle (perform op arg k) with clause` reduces to clause-body instantiation,
explicitly tracking the tail-resumptive clause case.
-/
inductive HandlerStep : HandlerExpr → HandlerExpr → Prop where
  | handle_perform_tail
      (handler : HandleContract)
      (clause : HandlerClauseSem)
      (arg k : CoreExpr)
      (h_contract_shape : clause.contract.handled = clause.handled)
      (h_mem : clause.contract ∈ handler.clauses)
      (h_summary :
        HandleClauseContract.handlerClauseHasResumeSummary
          handler clause.contract clause.contract.resumeUse)
      (h_tail_resumptive :
        clause.contract.resumeUse = .zero ∨ clause.contract.resumeUse = .one) :
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        (.core (bindTailResumptive clause arg k))

/--
Typed refinement of `HandlerStep` that records the precise preservation-side
obligation: the tail-resumptive clause-body instantiation is well-typed in the
ambient environment.
-/
inductive HandlerStepTyped (tenv : TermEnv) (ty : Ty) : HandlerExpr → HandlerExpr → Prop where
  | handle_perform_tail
      (handler : HandleContract)
      (clause : HandlerClauseSem)
      (arg k : CoreExpr)
      (h_contract_shape : clause.contract.handled = clause.handled)
      (h_mem : clause.contract ∈ handler.clauses)
      (h_summary :
        HandleClauseContract.handlerClauseHasResumeSummary
          handler clause.contract clause.contract.resumeUse)
      (h_tail_resumptive :
        clause.contract.resumeUse = .zero ∨ clause.contract.resumeUse = .one)
      (h_instantiated :
        HasType tenv (bindTailResumptive clause arg k) ty) :
      HandlerStepTyped tenv ty
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        (.core (bindTailResumptive clause arg k))

/--
Bridge from handler-step premises into the existing handler-level resume
linearity theorem surface.
-/
theorem handler_step_tail_resumptive_atMostOnce
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {e' : HandlerExpr}
    (h_handler_typed : HandleClauseContract.handlerWellTypedSlice handler)
    (h_step :
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        e') :
    resume_at_most_once clause.contract.resumeUse := by
  cases h_step with
  | handle_perform_tail _ _ _ _ _ _ h_summary _ =>
      exact
        HandleClauseContract.handlerClauseHasResumeSummary_implies_atMostOnce_of_handlerWellTypedSlice
          handler
          clause.contract
          clause.contract.resumeUse
          h_handler_typed
          h_summary

/--
Bridge from a typed handler step into the untyped step relation.
-/
theorem handlerStep_of_handlerStepTyped
    {tenv : TermEnv}
    {ty : Ty}
    {e e' : HandlerExpr}
    (h_step_typed : HandlerStepTyped tenv ty e e') :
    HandlerStep e e' := by
  cases h_step_typed with
  | handle_perform_tail handler clause arg k h_contract_shape h_mem h_summary h_tail _ =>
      exact
        HandlerStep.handle_perform_tail
          handler clause arg k h_contract_shape h_mem h_summary h_tail

/--
Named progress proposition for the single explicit handler-step redex case.
-/
def handler_step_progress_prop : Prop :=
  ∀ {tenv : TermEnv} {handler : HandleContract} {clause : HandlerClauseSem}
    {arg k : CoreExpr} {ty : Ty},
    HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty →
    HandleClauseContract.handlerClauseHasResumeSummary
      handler
      clause.contract
      clause.contract.resumeUse →
    clause.contract.resumeUse = .zero ∨ clause.contract.resumeUse = .one →
    ∃ e',
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        e'

/-- Progress witness for the explicit handler-step redex boundary. -/
theorem handler_step_progress : handler_step_progress_prop := by
  intro tenv handler clause arg k ty h_typed h_summary h_tail
  cases h_typed with
  | handle _ _ _ _ _ _ h_contract_shape h_mem _ _ =>
      refine ⟨.core (bindTailResumptive clause arg k), ?_⟩
      exact
        HandlerStep.handle_perform_tail
          handler clause arg k h_contract_shape h_mem h_summary h_tail

/--
Direct progress corollary from typed redex premises alone.
The summary and tail-resumptive premises are derived from the handler typing
contract attached to the clause.
-/
theorem handler_step_progress_of_typed_redex
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty) :
    ∃ e',
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        e' := by
  cases h_typed with
  | handle _ _ _ _ _ _ h_contract_shape h_mem h_clause_contract _ =>
      have h_summary :
          HandleClauseContract.handlerClauseHasResumeSummary
            handler
            clause.contract
            clause.contract.resumeUse :=
        HandleClauseContract.handlerClauseHasResumeSummary.mk
          clause.contract
          clause.contract.resumeUse
          h_mem
          (HandleClauseContract.clauseHasResumeSummary.mk clause.contract)
      have h_tail :
          clause.contract.resumeUse = .zero ∨ clause.contract.resumeUse = .one :=
        HandleClauseContract.wellTypedSlice_implies_resumeProvenance
          clause.contract
          h_clause_contract
      exact
        ⟨.core (bindTailResumptive clause arg k),
          HandlerStep.handle_perform_tail
            handler clause arg k h_contract_shape h_mem h_summary h_tail⟩

/--
Direct clause-level at-most-once corollary from typed redex premises alone.
-/
theorem handler_step_clause_atMostOnce_of_typed_redex
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty) :
    resume_at_most_once clause.contract.resumeUse := by
  cases h_typed with
  | handle _ _ _ _ _ _ _ _ h_clause_contract _ =>
      exact
        HandleClauseContract.clauseHasResumeSummary_implies_atMostOnce_of_wellTypedSlice
          clause.contract
          clause.contract.resumeUse
          h_clause_contract
          (HandleClauseContract.clauseHasResumeSummary.mk clause.contract)

/--
Extract clause contract well-typedness from any typed `handle` expression.
-/
theorem handler_clause_wellTypedSlice_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty) :
    HandleClauseContract.wellTypedSlice clause.contract := by
  cases h_typed with
  | handle _ _ _ _ _ _ _ _ h_clause_contract _ =>
      exact h_clause_contract

/--
General linearity bridge from handle typing to clause `resume_at_most_once`.
-/
theorem handler_clause_atMostOnce_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty) :
    resume_at_most_once clause.contract.resumeUse := by
  exact
    HandleClauseContract.clauseHasResumeSummary_implies_atMostOnce_of_wellTypedSlice
      clause.contract
      clause.contract.resumeUse
      (handler_clause_wellTypedSlice_of_handlerHasType h_typed)
      (HandleClauseContract.clauseHasResumeSummary.mk clause.contract)

/--
General classification bridge from handle typing to non-invalid clause class.
-/
theorem handler_clause_notInvalid_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty) :
    TailResumptiveClassification.classifyClause clause.contract ≠
      TailResumptiveClassification.TailResumptiveClass.invalid := by
  exact
    (TailResumptiveClassification.classifyClause_notInvalid_iff_atMostOnce
      clause.contract).2 (by
        simpa [resume_at_most_once] using
          handler_clause_atMostOnce_of_handlerHasType h_typed)

/--
General typed-handle bridge to packaged tail-resumptive bundle.
-/
theorem handler_clause_tail_resumptive_bundle_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty) :
    TailResumptiveClassification.TailResumptiveBundle clause.contract := by
  exact
    TailResumptiveClassification.tail_resumptive_bundle_of_wellTyped
      clause.contract
      (handler_clause_wellTypedSlice_of_handlerHasType h_typed)

/--
General typed-handle bridge to tail-resumptive classification alternatives.
-/
theorem handler_clause_tail_resumptive_classification_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty) :
    TailResumptiveClassification.classifyClause clause.contract =
      TailResumptiveClassification.TailResumptiveClass.nonResumptive
      ∨
    TailResumptiveClassification.classifyClause clause.contract =
      TailResumptiveClassification.TailResumptiveClass.tailResumptive := by
  exact
    (handler_clause_tail_resumptive_bundle_of_handlerHasType h_typed).classification

/--
General typed-handle bridge to packaged tail-capability bundle under explicit
capability-origin premises.
-/
theorem handler_clause_tail_capability_bundle_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    {baseEffects : EffectRow}
    {capability : Label}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty)
    (h_expr :
      clause.contract.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ clause.contract.handled) :
    TailCapabilityComposition.TailCapabilityBundle clause.contract capability := by
  exact
    TailCapabilityComposition.tailCapabilityBundle_of_wellTyped
      clause.contract
      baseEffects
      capability
      (handler_clause_wellTypedSlice_of_handlerHasType h_typed)
      h_expr
      h_ne

/--
General typed-handle projection to tail-capability bundle components under
explicit capability-origin premises.
-/
theorem handler_clause_tail_capability_as_components_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    {baseEffects : EffectRow}
    {capability : Label}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty)
    (h_expr :
      clause.contract.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ clause.contract.handled) :
    (RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffectsCore clause.contract))
        capability = true)
    ∧
    (RowFields.has
        (EffectRow.fields (HandleClauseContract.resultEffects clause.contract))
        capability = true)
    ∧
    (TailResumptiveClassification.classifyClause clause.contract ≠
      TailResumptiveClassification.TailResumptiveClass.invalid) := by
  exact
    TailCapabilityComposition.tailCapabilityBundle_as_components
      clause.contract
      capability
      (handler_clause_tail_capability_bundle_of_handlerHasType h_typed h_expr h_ne)

/--
General typed-handle bridge to packaged closed-aware tail-capability bundle
under explicit capability-origin premises.
-/
theorem handler_clause_tail_capability_closedAware_bundle_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    {baseEffects : EffectRow}
    {capability : Label}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty)
    (h_expr :
      clause.contract.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ clause.contract.handled) :
    TailCapabilityComposition.TailCapabilityClosedAwareBundle
      clause.contract
      capability := by
  exact
    TailCapabilityComposition.tailCapabilityClosedAwareBundle_of_wellTyped
      clause.contract
      baseEffects
      capability
      (handler_clause_wellTypedSlice_of_handlerHasType h_typed)
      h_expr
      h_ne

/--
General typed-handle projection to closed-aware tail-capability bundle
components under explicit capability-origin premises.
-/
theorem handler_clause_tail_capability_closedAware_as_components_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    {baseEffects : EffectRow}
    {capability : Label}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty)
    (h_expr :
      clause.contract.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ clause.contract.handled) :
    (RowFields.has
        (EffectRow.fields
          (HandlerClosedAwareContracts.resultEffectsClosedAware clause.contract))
        capability = true)
    ∧
    (TailResumptiveClassification.classifyClause clause.contract ≠
      TailResumptiveClassification.TailResumptiveClass.invalid) := by
  exact
    TailCapabilityComposition.tailCapabilityClosedAwareBundle_as_components
      clause.contract
      capability
      (handler_clause_tail_capability_closedAware_bundle_of_handlerHasType
        h_typed h_expr h_ne)

/--
General typed-handle contract capstone:
from one `HandlerHasType` witness we can recover clause well-typedness,
linearity, non-invalid classification, and the packaged tail-resumptive bundle.
-/
theorem handler_clause_contract_capstone_of_handlerHasType
    {tenv : TermEnv}
    {body : HandlerExpr}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {ty : Ty}
    (h_typed : HandlerHasType tenv (.handle body handler clause) ty) :
    HandleClauseContract.wellTypedSlice clause.contract
    ∧ resume_at_most_once clause.contract.resumeUse
    ∧ (TailResumptiveClassification.classifyClause clause.contract ≠
        TailResumptiveClassification.TailResumptiveClass.invalid)
    ∧ TailResumptiveClassification.TailResumptiveBundle clause.contract := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact handler_clause_wellTypedSlice_of_handlerHasType h_typed
  · exact handler_clause_atMostOnce_of_handlerHasType h_typed
  · exact handler_clause_notInvalid_of_handlerHasType h_typed
  · exact handler_clause_tail_resumptive_bundle_of_handlerHasType h_typed

/--
Determinism for the one-step handler boundary relation.
-/
theorem handler_step_deterministic
    {e e1 e2 : HandlerExpr}
    (h1 : HandlerStep e e1)
    (h2 : HandlerStep e e2) :
    e1 = e2 := by
  cases h1 with
  | handle_perform_tail _ clause arg k _ _ _ _ =>
      cases h2 with
      | handle_perform_tail _ _ _ _ _ _ _ _ =>
          rfl

/--
One-step typed-redex preservation corollary:
from a typed handler redex we can construct a concrete next expression and
show it is well-typed at the same type.
-/
theorem handler_step_exists_and_preserves_of_typed_redex
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty) :
    ∃ e',
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        e' ∧
      HandlerHasType tenv e' ty := by
  rcases handler_step_progress_of_typed_redex h_typed with ⟨e', h_step⟩
  refine ⟨e', h_step, ?_⟩
  exact handler_step_preservation h_typed h_step

/--
Capstone boundary theorem for typed handler redexes:
step existence, post-step type preservation, and clause at-most-once.
-/
theorem handler_typed_redex_capstone
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty) :
    (∃ e',
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        e' ∧
      HandlerHasType tenv e' ty) ∧
    resume_at_most_once clause.contract.resumeUse := by
  refine ⟨handler_step_exists_and_preserves_of_typed_redex h_typed, ?_⟩
  exact handler_step_clause_atMostOnce_of_typed_redex h_typed

/--
Bridge theorem: typed-redex linearity excludes the invalid tail-resumptive
classification bucket for the selected handler clause.
-/
theorem handler_step_clause_notInvalid_of_typed_redex
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty) :
    TailResumptiveClassification.classifyClause clause.contract ≠
      TailResumptiveClassification.TailResumptiveClass.invalid := by
  have h_linear : resume_at_most_once clause.contract.resumeUse :=
    handler_step_clause_atMostOnce_of_typed_redex h_typed
  exact
    (TailResumptiveClassification.classifyClause_notInvalid_iff_atMostOnce
      clause.contract).2 (by simpa [resume_at_most_once] using h_linear)

/--
Extended capstone route for typed handler redexes: one-step existence,
preservation, linearity, and non-invalid tail-resumptive classification.
-/
theorem handler_typed_redex_capstone_with_classification
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty) :
    (∃ e',
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        e' ∧
      HandlerHasType tenv e' ty) ∧
    resume_at_most_once clause.contract.resumeUse ∧
    TailResumptiveClassification.classifyClause clause.contract ≠
      TailResumptiveClassification.TailResumptiveClass.invalid := by
  refine ⟨?_, ?_, ?_⟩
  · exact handler_step_exists_and_preserves_of_typed_redex h_typed
  · exact handler_step_clause_atMostOnce_of_typed_redex h_typed
  · exact handler_step_clause_notInvalid_of_typed_redex h_typed

/--
Extract the clause well-typed slice from a typed handler redex premise.
-/
theorem handler_typed_redex_clause_wellTypedSlice
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty) :
    HandleClauseContract.wellTypedSlice clause.contract := by
  exact handler_clause_wellTypedSlice_of_handlerHasType h_typed

/--
Typed-redex bridge into the packaged tail-resumptive bundle surface.
-/
theorem handler_typed_redex_tail_resumptive_bundle
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty) :
    TailResumptiveClassification.TailResumptiveBundle clause.contract := by
  exact handler_clause_tail_resumptive_bundle_of_handlerHasType h_typed

/--
Extended capstone route for typed handler redexes with the packaged
tail-resumptive bundle consequence.
-/
theorem handler_typed_redex_capstone_with_tail_resumptive_bundle
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty) :
    (∃ e',
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        e' ∧
      HandlerHasType tenv e' ty) ∧
    resume_at_most_once clause.contract.resumeUse ∧
    TailResumptiveClassification.TailResumptiveBundle clause.contract := by
  refine ⟨?_, ?_, ?_⟩
  · exact handler_step_exists_and_preserves_of_typed_redex h_typed
  · exact handler_step_clause_atMostOnce_of_typed_redex h_typed
  · exact handler_typed_redex_tail_resumptive_bundle h_typed

/--
Typed-redex bridge into packaged tail-capability composition contracts.
-/
theorem handler_typed_redex_tail_capability_bundle
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    {baseEffects : EffectRow}
    {capability : Label}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty)
    (h_expr :
      clause.contract.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ clause.contract.handled) :
    TailCapabilityComposition.TailCapabilityBundle clause.contract capability := by
  exact handler_clause_tail_capability_bundle_of_handlerHasType h_typed h_expr h_ne

/--
Extended capstone route for typed handler redexes with tail-capability bundle
consequences under explicit capability-origin premises.
-/
theorem handler_typed_redex_capstone_with_tail_capability_bundle
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    {baseEffects : EffectRow}
    {capability : Label}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty)
    (h_expr :
      clause.contract.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ clause.contract.handled) :
    (∃ e',
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        e' ∧
      HandlerHasType tenv e' ty) ∧
    resume_at_most_once clause.contract.resumeUse ∧
    TailCapabilityComposition.TailCapabilityBundle clause.contract capability := by
  refine ⟨?_, ?_, ?_⟩
  · exact handler_step_exists_and_preserves_of_typed_redex h_typed
  · exact handler_step_clause_atMostOnce_of_typed_redex h_typed
  · exact handler_typed_redex_tail_capability_bundle h_typed h_expr h_ne

/--
Typed-redex bridge into packaged closed-aware tail-capability contracts.
-/
theorem handler_typed_redex_tail_capability_closedAware_bundle
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    {baseEffects : EffectRow}
    {capability : Label}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty)
    (h_expr :
      clause.contract.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ clause.contract.handled) :
    TailCapabilityComposition.TailCapabilityClosedAwareBundle
      clause.contract
      capability := by
  exact
    handler_clause_tail_capability_closedAware_bundle_of_handlerHasType
      h_typed h_expr h_ne

/--
Extended capstone route for typed handler redexes with closed-aware
tail-capability bundle consequences under explicit capability-origin premises.
-/
theorem handler_typed_redex_capstone_with_tail_capability_closedAware_bundle
    {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    {baseEffects : EffectRow}
    {capability : Label}
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty)
    (h_expr :
      clause.contract.exprEffects =
        EffectOperationTyping.performOperationEffects baseEffects capability)
    (h_ne : capability ≠ clause.contract.handled) :
    (∃ e',
      HandlerStep
        (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
          handler
          clause)
        e' ∧
      HandlerHasType tenv e' ty) ∧
    resume_at_most_once clause.contract.resumeUse ∧
    TailCapabilityComposition.TailCapabilityClosedAwareBundle
      clause.contract
      capability := by
  refine ⟨?_, ?_, ?_⟩
  · exact handler_step_exists_and_preserves_of_typed_redex h_typed
  · exact handler_step_clause_atMostOnce_of_typed_redex h_typed
  · exact handler_typed_redex_tail_capability_closedAware_bundle h_typed h_expr h_ne

/-- Inversion lemma for the `core` constructor of `HandlerHasType`. -/
theorem handlerHasType_core_inv
    {tenv : TermEnv}
    {e : CoreExpr}
    {ty : Ty}
    (h : HandlerHasType tenv (.core e) ty) :
    HasType tenv e ty := by
  cases h with
  | core _ _ _ h_core =>
      exact h_core

/--
Bridge theorem: once a typed handler redex takes its one-step boundary
reduction to a core expression, existing core evaluator soundness applies.
-/
theorem handler_typed_redex_core_eval_sound
    {tenv : TermEnv}
    {venv : ValueEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    (h_env : EnvWellTyped tenv venv)
    (h_typed : HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty)
    (h_frag : EvalFragmentFull (bindTailResumptive clause arg k)) :
    ∃ v, eval venv (bindTailResumptive clause arg k) = some v ∧ ValueHasType v ty := by
  rcases handler_typed_redex_capstone h_typed with ⟨h_step_pack, _h_linear⟩
  rcases h_step_pack with ⟨e', h_step, h_typed'⟩
  have h_target :
      e' = .core (bindTailResumptive clause arg k) := by
    cases h_step with
    | handle_perform_tail _ _ _ _ _ _ _ _ =>
        rfl
  subst h_target
  have h_core_ty :
      HasType tenv (bindTailResumptive clause arg k) ty :=
    handlerHasType_core_inv h_typed'
  exact eval_sound_evalFragmentFull h_env h_core_ty h_frag

/--
Preservation for the typed handler-step refinement.

This theorem isolates the remaining untyped-preservation gap to proving
`HandlerStepTyped` from the ordinary `HandlerStep` premises.
-/
theorem handler_step_typed_preservation
    {tenv : TermEnv}
    {e e' : HandlerExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv e ty)
    (h_step_typed : HandlerStepTyped tenv ty e e') :
    HandlerHasType tenv e' ty := by
  cases h_step_typed with
  | handle_perform_tail _ clause arg k _ _ _ _ h_instantiated =>
      exact
        HandlerHasType.core tenv
          (bindTailResumptive clause arg k)
          ty
          h_instantiated

/--
Named preservation proposition for handler reduction:
if a handler expression is well-typed and takes one handler step, the result
is well-typed at the same type.
-/
def handler_step_preservation_prop : Prop :=
  ∀ {tenv : TermEnv} {e e' : HandlerExpr} {ty : Ty},
    HandlerHasType tenv e ty →
    HandlerStep e e' →
    HandlerHasType tenv e' ty

/--
Precise remaining preservation-side obligation for the current boundary model:
typing the clause-body instantiation produced by a handler step.
-/
def handler_step_instantiation_obligation_prop : Prop :=
  ∀ {tenv : TermEnv}
    {handler : HandleContract}
    {clause : HandlerClauseSem}
    {arg k : CoreExpr}
    {ty : Ty}
    {e' : HandlerExpr},
    HandlerHasType tenv
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      ty →
    HandlerStep
      (.handle (.perform clause.handled clause.opArgTy clause.opRetTy arg k)
        handler
        clause)
      e' →
    HasType tenv (bindTailResumptive clause arg k) ty

/--
Lift an untyped handler step into `HandlerStepTyped` using the explicit
instantiation typing obligation.
-/
theorem handler_step_typed_of_handler_step
    (h_instantiation : handler_step_instantiation_obligation_prop)
    {tenv : TermEnv}
    {e e' : HandlerExpr}
    {ty : Ty}
    (h_typed : HandlerHasType tenv e ty)
    (h_step : HandlerStep e e') :
    HandlerStepTyped tenv ty e e' := by
  cases h_step with
  | handle_perform_tail handler clause arg k h_contract_shape h_mem h_summary h_tail =>
      have h_inst :
          HasType tenv (bindTailResumptive clause arg k) ty :=
        h_instantiation h_typed
          (HandlerStep.handle_perform_tail
            handler clause arg k h_contract_shape h_mem h_summary h_tail)
      exact
        HandlerStepTyped.handle_perform_tail
          handler clause arg k h_contract_shape h_mem h_summary h_tail h_inst

/--
Preservation follows from the explicit instantiation typing obligation.
-/
theorem handler_step_preservation_of_instantiation_obligation
    (h_instantiation : handler_step_instantiation_obligation_prop) :
    handler_step_preservation_prop := by
  intro tenv e e' ty h_typed h_step
  exact handler_step_typed_preservation h_typed
    (handler_step_typed_of_handler_step h_instantiation h_typed h_step)

/--
Open proof target for the exact remaining handler-step obligation.
-/
theorem handler_step_instantiation_obligation :
    handler_step_instantiation_obligation_prop := by
  intro tenv handler clause arg k ty e' h_typed h_step
  cases h_typed with
  | handle _ body handler' clause' ty' h_body _h_contract_shape _h_mem _h_clause_contract h_clause_body =>
      cases h_body with
      | perform _ op argTy opRetTy handlerTy arg' k' h_arg h_k =>
          cases h_step with
          | handle_perform_tail _ _ _ _ _ _ _ _ =>
              simpa [bindTailResumptive] using
                clause.instantiate_sound
                  (tenv := tenv)
                  (ty := ty)
                  (arg := arg)
                  (k := k)
                  h_arg
                  h_k
                  h_clause_body

/--
Handler-step preservation at the current boundary, reduced to the explicit
instantiation obligation above.
-/
theorem handler_step_preservation : handler_step_preservation_prop :=
  handler_step_preservation_of_instantiation_obligation
    handler_step_instantiation_obligation

end HandlerStepBoundary

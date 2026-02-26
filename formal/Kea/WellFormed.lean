import Kea.Ty

/-
  Kea.WellFormed — Well-formedness predicates for the core type surface.

  This module introduces structural WF judgments parameterized by:
  - type-variable kind assumptions (`kctx`)
  - in-scope row variables (`rctx`)

  The predicates are intentionally lightweight for Phase 1:
  - type vars must be present in `kctx`
  - row tail vars must be present in `rctx`
  - constructors recurse structurally over components
-/

/-- Type-variable context: variable id paired with its kind. -/
abbrev KindCtx := List (TypeVarId × Kind)

/-- Row-variable context: in-scope row variables. -/
abbrev RowCtx := List RowVarId

mutual
  /-- Well-formed types under kind and row contexts. -/
  def Ty.WellFormed (kctx : KindCtx) (rctx : RowCtx) : Ty → Prop
    | .var v => ∃ k, (v, k) ∈ kctx
    | .int | .intN _ _ | .float | .floatN _ | .decimal _ _ | .bool | .string
      | .html | .markdown | .atom | .date | .dateTime | .unit | .dynamic => True
    | .list t | .set t | .option t | .fixedSizeList t _ | .tensor t _
      | .dataframe t | .column t | .stream t | .task t | .actor t | .arc t
      | .groupedFrame t _ | .tagged t _ =>
      Ty.WellFormed kctx rctx t
    | .map k v | .result k v =>
      Ty.WellFormed kctx rctx k ∧ Ty.WellFormed kctx rctx v
    | .sum _ args | .opaque _ args | .existential _ args | .tuple args =>
      TyList.WellFormed kctx rctx args
    | .record _ r | .anonRecord r | .row r =>
      Row.WellFormed kctx rctx r
    | .function params ret =>
      TyList.WellFormed kctx rctx params ∧ Ty.WellFormed kctx rctx ret
    | .functionEff params effects ret =>
      TyList.WellFormed kctx rctx params ∧ EffectRow.WellFormed kctx rctx effects ∧ Ty.WellFormed kctx rctx ret
    | .forall _ body =>
      Ty.WellFormed kctx rctx body
    | .app ctor args =>
      Ty.WellFormed kctx rctx ctor ∧ TyList.WellFormed kctx rctx args
    | .constructor _ fixedArgs _ =>
      TyList.WellFormed kctx rctx fixedArgs

  /-- Well-formed rows under kind and row contexts. -/
  def Row.WellFormed (kctx : KindCtx) (rctx : RowCtx) : Row → Prop
    | .mk fields none =>
      RowFields.WellFormed kctx rctx fields
    | .mk fields (some rv) =>
      RowFields.WellFormed kctx rctx fields ∧ rv ∈ rctx

  /-- Well-formed type lists. -/
  def TyList.WellFormed (kctx : KindCtx) (rctx : RowCtx) : TyList → Prop
    | .nil => True
    | .cons t rest =>
      Ty.WellFormed kctx rctx t ∧ TyList.WellFormed kctx rctx rest

  /-- Well-formed row fields. -/
  def RowFields.WellFormed (kctx : KindCtx) (rctx : RowCtx) : RowFields → Prop
    | .nil => True
    | .cons _ ty rest =>
      Ty.WellFormed kctx rctx ty ∧ RowFields.WellFormed kctx rctx rest

  /-- Well-formed effect rows (delegates to row WF). -/
  def EffectRow.WellFormed (kctx : KindCtx) (rctx : RowCtx) : EffectRow → Prop
    | .mk row =>
      Row.WellFormed kctx rctx row
end

namespace RowFields

/-- Well-formedness is preserved by row-field append. -/
def wellFormedAppend
    (kctx : KindCtx) (rctx : RowCtx) (a b : RowFields)
    (ha : RowFields.WellFormed kctx rctx a)
    (hb : RowFields.WellFormed kctx rctx b) :
    RowFields.WellFormed kctx rctx (a.append b) :=
  match a with
  | .nil =>
    by simpa [RowFields.append] using hb
  | .cons l ty rest =>
    match ha with
    | ⟨h_ty, h_rest⟩ =>
      by
        simp [RowFields.append]
        exact ⟨h_ty, wellFormedAppend kctx rctx rest b h_rest hb⟩

/-- Well-formedness is preserved by row-field append. -/
theorem wellFormed_append
    (kctx : KindCtx) (rctx : RowCtx) (a b : RowFields)
    (ha : RowFields.WellFormed kctx rctx a)
    (hb : RowFields.WellFormed kctx rctx b) :
    RowFields.WellFormed kctx rctx (a.append b) :=
  wellFormedAppend kctx rctx a b ha hb

end RowFields

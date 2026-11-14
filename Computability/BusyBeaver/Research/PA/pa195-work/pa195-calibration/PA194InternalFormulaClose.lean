import PA194InternalClose
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic
/-! A model-uniform internal formula traversal closing one free label.

The parameter packs the label and current binder depth.  This is a Foundation
UformulaRec1 construction, not yet a candidate-PRA formula-closing Code.
The internal formula, its parameters, and its depth may all be nonstandard.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194InternalFormulaClose
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ label, !pi₁Def label param ∧ ∃ depth, !pi₂Def depth param ∧ ∃ w, !(PA194InternalClose.blueprint.resultVec ℒₒᵣ) w k v label depth ∧ !qqRelDef y k R w”
  nrel := .mkSigma “y param k R v. ∃ label, !pi₁Def label param ∧ ∃ depth, !pi₂Def depth param ∧ ∃ w, !(PA194InternalClose.blueprint.resultVec ℒₒᵣ) w k v label depth ∧ !qqNRelDef y k R w”
  verum := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. !qqAllDef y y₁”
  exs := .mkSigma “y param p₁ y₁. !qqExsDef y y₁”
  allChanges := .mkSigma “param' param. ∃ label, !pi₁Def label param ∧ ∃ depth, !pi₂Def depth param ∧ !pairDef param' label (depth + 1)”
  exsChanges := .mkSigma “param' param. ∃ label, !pi₁Def label param ∧ ∃ depth, !pi₂Def depth param ∧ !pairDef param' label (depth + 1)”
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def construction : UformulaRec1.Construction M blueprint where
  rel p k R v := ^rel k R (PA194InternalClose.construction.resultVec ℒₒᵣ ![π₁ p,π₂ p] k v)
  nrel p k R v := ^nrel k R (PA194InternalClose.construction.resultVec ℒₒᵣ ![π₁ p,π₂ p] k v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ y₁ y₂ := y₁ ^⋏ y₂
  or _ _ _ y₁ y₂ := y₁ ^⋎ y₂
  all _ _ y := ^∀ y
  exs _ _ y := ^∃ y
  allChanges p := pair (π₁ p) (π₂ p+1)
  exsChanges p := pair (π₁ p) (π₂ p+1)
  rel_defined := .mk fun v => by
    simp [blueprint, PA194InternalClose.construction.eval_resultVec, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
  nrel_defined := .mk fun v => by
    simp [blueprint, PA194InternalClose.construction.eval_resultVec, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
  verum_defined := .mk fun v => by simp [blueprint]
  falsum_defined := .mk fun v => by simp [blueprint]
  and_defined := .mk fun v => by simp [blueprint]
  or_defined := .mk fun v => by simp [blueprint]
  all_defined := .mk fun v => by simp [blueprint]
  exs_defined := .mk fun v => by simp [blueprint]
  allChanges_defined := .mk fun v => by simp [blueprint]
  exChanges_defined := .mk fun v => by simp [blueprint]
/-- The packed parameter stores the label and current binder depth. -/
noncomputable def close (label depth p : M) : M := construction.result ℒₒᵣ (pair label depth) p

/-- One formula, independent of the model, defines the packed traversal. -/
theorem graph : 𝚺₁-Function₂ ((construction (M := M)).result ℒₒᵣ) via blueprint.result ℒₒᵣ := construction.result_defined

/-- The term-vector traversal preserves internal well-formedness. -/
theorem close_vec_wellformed (label depth k v : M) (hv : IsSemitermVec ℒₒᵣ k depth v) :
    IsSemitermVec ℒₒᵣ k (depth+1)
      (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v) := by
  apply IsSemitermVec.iff.mpr
  constructor
  · simp [hv.isUTerm]
  · intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact PA194InternalClose.close_well_formed label depth v.[i] (hv.nth hi)

/-- Each atom argument is exactly the established candidate-PRA term closer. -/
theorem close_vec_nth (label depth k v i : M) (hv : IsSemitermVec ℒₒᵣ k depth v) (hi : i < k) :
    (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v).[i] =
      F (PA194TermRecursion.closeCode PA194TermWellFormedUnconditional.canonicalFirst
        PA194TermWellFormedUnconditional.canonicalSecond) ![v.[i],label,depth] := by
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
  exact (PA194InternalClose.canonical_agree label depth v.[i] (hv.nth hi)).symm

theorem close_rel (label depth k r v : M) (hr : (ℒₒᵣ : Language).IsRel k r) (hv : IsUTermVec ℒₒᵣ k v) :
    close label depth (^rel k r v) = ^rel k r (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v) := by
  simp [close, construction, hr, hv]
theorem close_nrel (label depth k r v : M) (hr : (ℒₒᵣ : Language).IsRel k r) (hv : IsUTermVec ℒₒᵣ k v) :
    close label depth (^nrel k r v) = ^nrel k r (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v) := by
  simp [close, construction, hr, hv]
theorem close_verum (label depth : M) : close label depth ^⊤ = ^⊤ := by simp [close, construction]
theorem close_falsum (label depth : M) : close label depth ^⊥ = ^⊥ := by simp [close, construction]
theorem close_and (label depth p q : M) (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    close label depth (p ^⋏ q) = close label depth p ^⋏ close label depth q := by
  simp [close, construction, hp, hq]
theorem close_or (label depth p q : M) (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    close label depth (p ^⋎ q) = close label depth p ^⋎ close label depth q := by
  simp [close, construction, hp, hq]
theorem close_all (label depth p : M) (hp : IsUFormula ℒₒᵣ p) :
    close label depth (^∀ p) = ^∀ (close label (depth+1) p) := by
  simp [close, construction, hp]
theorem close_exs (label depth p : M) (hp : IsUFormula ℒₒᵣ p) :
    close label depth (^∃ p) = ^∃ (close label (depth+1) p) := by
  simp [close, construction, hp]

/-- Internal formula well-formedness is preserved at every model-valued depth. -/
theorem close_wellformed (label depth p : M) (hp : IsSemiformula ℒₒᵣ depth p) :
    IsSemiformula ℒₒᵣ (depth+1) (close label depth p) := by
  haveI : 𝚺₁-Function₂ ((construction (M := M)).result ℒₒᵣ) := graph.to_definable
  have hdef : 𝚺₁-Relation (fun depth p : M => IsSemiformula ℒₒᵣ (depth+1) (close label depth p)) := by
    unfold close
    definability
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k R v hR hv
    rw [close, UformulaRec1.Construction.result_rel construction hR hv.isUTerm]
    simpa [construction,hR] using close_vec_wellformed label n k v hv
  · intro n k R v hR hv
    rw [close, UformulaRec1.Construction.result_nrel construction hR hv.isUTerm]
    simpa [construction,hR] using close_vec_wellformed label n k v hv
  · intro n; simp [close, construction]
  · intro n; simp [close, construction]
  · intro n p q hp hq ihp ihq
    simp [close, hp.isUFormula, hq.isUFormula, construction] at *
    exact ⟨ihp, ihq⟩
  · intro n p q hp hq ihp ihq
    simp [close, hp.isUFormula, hq.isUFormula, construction] at *
    exact ⟨ihp, ihq⟩
  · intro n p hp ih
    simp [close, hp.isUFormula, construction] at *
    exact ih
  · intro n p hp ih
    simp [close, hp.isUFormula, construction] at *
    exact ih

#print axioms close_vec_nth
#print axioms close_all
#print axioms close_wellformed
#print axioms graph
#print axioms close_vec_wellformed
#print axioms construction
end models
end PA194InternalFormulaClose

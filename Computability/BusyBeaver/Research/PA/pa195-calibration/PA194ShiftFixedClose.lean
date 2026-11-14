import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import PA194InternalFormulaClose
/-! Closing does not change shift-fixed internally well-formed arithmetic syntax.
The induction-schema corollary uses Foundation's concrete nonstandard recognizer.
No proof renaming or invariance of all PA axioms is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ShiftFixedClose
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
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

lemma close_of_shift_fixed (label depth t : M) (ht : IsSemiterm ℒₒᵣ depth t)
    (hf : termShift ℒₒᵣ t = t) : PA194InternalClose.close label depth t = t := by
  have hdef : 𝚺₁-Predicate (fun t : M => termShift ℒₒᵣ t = t → PA194InternalClose.close label depth t = t) := by
    haveI := PA194InternalClose.close_definable label depth
    definability
  revert hf
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz _
    simp [PA194InternalClose.close, PA194InternalClose.construction, hz]
  · intro x h
    simp only [termShift_fvar, qqFvar_inj] at h
    exact False.elim ((ne_of_lt (lt_add_one x)) h.symm)
  · intro k f v hfunc hv ih hf
    rw [termShift_func hfunc hv.isUTerm] at hf
    have hvfixed : termShiftVec ℒₒᵣ k v = v := by simpa using hf
    change PA194InternalClose.construction.result ℒₒᵣ ![label,depth] (^func k f v) = ^func k f v
    rw [Language.TermRec.Construction.result_func' _ hfunc hv.isUTerm]
    change ^func k f (PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v) = ^func k f v
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm) (by simpa using hv.lh)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    change PA194InternalClose.close label depth v.[i] = v.[i]
    apply ih i hi
    have hh := congrArg (fun z : M => z.[i]) hvfixed
    simpa [nth_termShiftVec hv.isUTerm hi] using hh

lemma close_vec_of_shift_fixed (label depth k v : M) (hv : IsSemitermVec ℒₒᵣ k depth v)
    (hf : termShiftVec ℒₒᵣ k v = v) :
    PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] k v = v := by
  apply nth_ext' k
    (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm) (by simpa using hv.lh)
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
  change PA194InternalClose.close label depth v.[i] = v.[i]
  apply close_of_shift_fixed label depth v.[i] (hv.nth hi)
  have hh := congrArg (fun z : M => z.[i]) hf
  simpa [nth_termShiftVec hv.isUTerm hi] using hh

lemma formula_close_of_shift_fixed (label depth p : M) (hp : IsSemiformula ℒₒᵣ depth p)
    (hf : shift ℒₒᵣ p = p) : PA194InternalFormulaClose.close label depth p = p := by
  haveI : 𝚺₁-Function₂ ((PA194InternalFormulaClose.construction (M := M)).result ℒₒᵣ) := PA194InternalFormulaClose.graph.to_definable
  have hdef : 𝚺₁-Relation (fun depth p : M => shift ℒₒᵣ p = p → PA194InternalFormulaClose.close label depth p = p) := by
    unfold PA194InternalFormulaClose.close
    definability
  revert hf
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k R v hR hv hf
    rw [shift_rel hR hv.isUTerm] at hf
    have hvec : termShiftVec ℒₒᵣ k v = v := by simpa using hf
    rw [PA194InternalFormulaClose.close_rel label n k R v hR hv.isUTerm, close_vec_of_shift_fixed label n k v hv hvec]
  · intro n k R v hR hv hf
    rw [shift_nrel hR hv.isUTerm] at hf
    have hvec : termShiftVec ℒₒᵣ k v = v := by simpa using hf
    rw [PA194InternalFormulaClose.close_nrel label n k R v hR hv.isUTerm, close_vec_of_shift_fixed label n k v hv hvec]
  · intro n _; simp [PA194InternalFormulaClose.close_verum]
  · intro n _; simp [PA194InternalFormulaClose.close_falsum]
  · intro n p q hp hq ihp ihq hf
    rw [shift_and hp.isUFormula hq.isUFormula] at hf
    have h : shift ℒₒᵣ p = p ∧ shift ℒₒᵣ q = q := by simpa using hf
    rw [PA194InternalFormulaClose.close_and label n p q hp.isUFormula hq.isUFormula, ihp h.1, ihq h.2]
  · intro n p q hp hq ihp ihq hf
    rw [shift_or hp.isUFormula hq.isUFormula] at hf
    have h : shift ℒₒᵣ p = p ∧ shift ℒₒᵣ q = q := by simpa using hf
    rw [PA194InternalFormulaClose.close_or label n p q hp.isUFormula hq.isUFormula, ihp h.1, ihq h.2]
  · intro n p hp ih hf
    rw [shift_all hp.isUFormula] at hf
    have h : shift ℒₒᵣ p = p := by simpa using hf
    rw [PA194InternalFormulaClose.close_all label n p hp.isUFormula, ih h]
  · intro n p hp ih hf
    rw [shift_exs hp.isUFormula] at hf
    have h : shift ℒₒᵣ p = p := by simpa using hf
    rw [PA194InternalFormulaClose.close_exs label n p hp.isUFormula, ih h]

lemma shift_qqAlls_of_fixed {b : M} (hb : IsUFormula ℒₒᵣ b)
    (hshift : shift ℒₒᵣ b = b) (k : M) :
    shift ℒₒᵣ (qqAlls b k) = qqAlls b k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hshift
  case succ k ih => rw [qqAlls_succ, shift_all (isUFormula_qqAlls.mpr hb), ih]

lemma induction_axiom_close_fixed (label p : M) (h : InductionUnivR p) :
    PA194InternalFormulaClose.close label 0 p = p := by
  obtain ⟨m, hm, b, hbp, rfl, hb, hshift, hbv, _⟩ := h
  have hformula : IsSemiformula ℒₒᵣ 0 (qqAlls b m) := by
    rw [isSemiformula_iff]
    constructor
    · exact isUFormula_qqAlls.mpr hb
    · rw [bv_qqAlls hb, hbv]
      simp
  have hfixed : shift ℒₒᵣ (qqAlls b m) = qqAlls b m := shift_qqAlls_of_fixed hb hshift m
  exact formula_close_of_shift_fixed label 0 (qqAlls b m) hformula hfixed

#print axioms close_of_shift_fixed
#print axioms formula_close_of_shift_fixed
#print axioms induction_axiom_close_fixed
end PA194ShiftFixedClose

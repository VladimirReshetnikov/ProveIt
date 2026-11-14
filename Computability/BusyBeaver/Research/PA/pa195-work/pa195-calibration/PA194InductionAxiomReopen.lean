import PA194ShiftFixedClose
/-! The specific closing-and-reopening operation fixes every induction-schema axiom.
This is a formula-level fact; it is not yet a derivation transformer. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194InductionAxiomReopen
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

lemma subst_extra_self {n w p : M} (hp : IsSemiformula ℒₒᵣ n p) (hw : IsSemitermVec ℒₒᵣ (n + 1) (n + 1) w) (H : ∀ i < n, w.[i] = ^#i) :
    subst ℒₒᵣ w p = p := by
  revert w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv w _ H
    simp only [substs_rel, qqRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n k R v hR hv w _ H
    simp only [substs_nrel, qqNRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n w _ _; simp
  · intro n w _ _; simp
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp hw H, ihq hw H]
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp hw H, ihq hw H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (qVec ℒₒᵣ w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by rw [hw.lh]; exact lt_trans hi (lt_add_one n))]
        simp [H i hi]
    simp [*, hp.isUFormula, ih (by simpa [add_assoc] using hw.qVec) H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (qVec ℒₒᵣ w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by rw [hw.lh]; exact lt_trans hi (lt_add_one n))]
        simp [H i hi]
    simp [*, hp.isUFormula, ih (by simpa [add_assoc] using hw.qVec) H]


lemma free_of_shift_fixed {p : M} (hp : IsSemiformula ℒₒᵣ 0 p) (hshift : shift ℒₒᵣ p = p) :
    free ℒₒᵣ p = p := by
  unfold free substs1
  rw [hshift]
  exact subst_extra_self hp (by simp) (by simp)

lemma induction_axiom_reopen_fixed (label p : M) (h : InductionUnivR p) :
    free ℒₒᵣ (PA194InternalFormulaClose.close label 0 p) = p := by
  have hclose := PA194ShiftFixedClose.induction_axiom_close_fixed label p h
  rw [hclose]
  obtain ⟨m, hm, b, hbp, rfl, hb, hshift, hbv, _⟩ := h
  apply free_of_shift_fixed
  · rw [isSemiformula_iff]
    constructor
    · exact isUFormula_qqAlls.mpr hb
    · rw [bv_qqAlls hb, hbv]; simp
  · exact PA194ShiftFixedClose.shift_qqAlls_of_fixed hb hshift m
#print axioms subst_extra_self
#print axioms free_of_shift_fixed
#print axioms induction_axiom_reopen_fixed
end PA194InductionAxiomReopen

module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionVectorReadback
@[expose] public section
/-! Substitution depends only on the actual bound-variable support. The two
replacement vectors need not have equal lengths. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

theorem termSubst_agree_on_bound {n w v t : V} (ht : IsSemiterm L n t)
    (h : ∀ i < n, w.[i] = v.[i]) : termSubst L w t = termSubst L v t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i hi; simp [h i hi]
  · intro i; simp
  · intro k r ts hr hts ih
    rw [termSubst_func hr hts.isUTerm, termSubst_func hr hts.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by simp [hts.isUTerm]) (by simp [hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec hts.isUTerm hi, nth_termSubstVec hts.isUTerm hi, ih i hi]

#print axioms termSubst_agree_on_bound
end M6.PA.FoundationPAeqCode


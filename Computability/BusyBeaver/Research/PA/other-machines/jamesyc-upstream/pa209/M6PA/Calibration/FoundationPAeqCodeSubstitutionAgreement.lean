module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeSubstitutionAgreementVectors
@[expose] public section
/-! Model-valued substitution ignores surplus entries. The proof uses the
pinned definable formula induction, including unequal vector lengths under binders. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

theorem subst_agree_on_bound {n p : V} (hp : IsSemiformula L n p)
    {m k l w v : V} (hw : IsSemitermVec L k m w) (hv : IsSemitermVec L l m v)
    (hnw : n ≤ k) (hnv : n ≤ l) (h : ∀ i < n, w.[i]=v.[i]) :
    subst L w p = subst L v p := by
  revert m k l w v
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n a r ts hr hts m k l w v hw hv hnw hnv h
    rw [substs_rel hr hts.isUTerm,substs_rel hr hts.isUTerm]
    simp only [qqRel_inj,true_and]
    apply nth_ext' a (by simp [hts.isUTerm]) (by simp [hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec hts.isUTerm hi,nth_termSubstVec hts.isUTerm hi,
      termSubst_agree_on_bound (hts.nth hi) h]
  · intro n a r ts hr hts m k l w v hw hv hnw hnv h
    rw [substs_nrel hr hts.isUTerm,substs_nrel hr hts.isUTerm]
    simp only [qqNRel_inj,true_and]
    apply nth_ext' a (by simp [hts.isUTerm]) (by simp [hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec hts.isUTerm hi,nth_termSubstVec hts.isUTerm hi,
      termSubst_agree_on_bound (hts.nth hi) h]
  · intros; simp
  · intros; simp
  · intro n p q hp hq ihp ihq m k l w v hw hv hnw hnv h
    rw [substs_and hp.isUFormula hq.isUFormula,substs_and hp.isUFormula hq.isUFormula,
      ihp hw hv hnw hnv h,ihq hw hv hnw hnv h]
  · intro n p q hp hq ihp ihq m k l w v hw hv hnw hnv h
    rw [substs_or hp.isUFormula hq.isUFormula,substs_or hp.isUFormula hq.isUFormula,
      ihp hw hv hnw hnv h,ihq hw hv hnw hnv h]
  · intro n p hp ih m k l w v hw hv hnw hnv h
    rw [substs_all hp.isUFormula,substs_all hp.isUFormula,
      ih hw.qVec hv.qVec (by simpa using hnw) (by simpa using hnv)
        (qVec_agree_on_bound hw hv hnw hnv h)]
  · intro n p hp ih m k l w v hw hv hnw hnv h
    rw [substs_ex hp.isUFormula,substs_ex hp.isUFormula,
      ih hw.qVec hv.qVec (by simpa using hnw) (by simpa using hnv)
        (qVec_agree_on_bound hw hv hnw hnv h)]

#print axioms subst_agree_on_bound
end M6.PA.FoundationPAeqCode


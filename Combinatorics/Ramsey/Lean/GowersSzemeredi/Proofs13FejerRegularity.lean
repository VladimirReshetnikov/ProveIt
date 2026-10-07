import GowersSzemeredi.Proofs13FejerDiagonal

/-! If all short feature relations lie on the intended line, an
unrespected phase has only diagonal simultaneous relations. The same
condition excludes repeated vertices when there are at least three labels. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem fejer_diagonal_of_feature_line {N L : Nat} [NeZero N] [Fact N.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (hLN : L ≤ N) (lambda phi feature : I → ZMod N)
    (hphase : ∑ i, lambda i * phi i ≠ 0)
    (hline : ∀ v : I → Fin L × Fin L, fejerPairRelation v feature = 0 →
      ∃ c : ZMod N, ∀ i, ((v i).1 - (v i).2 : ZMod N) = c * lambda i) :
    ∀ v : I → Fin L × Fin L,
      (fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0) ↔
        ∀ i, (v i).1 = (v i).2 := by
  intro v
  constructor
  · rintro ⟨hp, hf⟩
    obtain ⟨c, hc⟩ := hline v hf
    have he : fejerPairRelation v phi = c * ∑ i, lambda i * phi i := by
      simp only [fejerPairRelation, hc, Finset.mul_sum, mul_assoc]
    have hc0 : c = 0 := (mul_eq_zero.mp (he.symm.trans hp)).resolve_right hphase
    intro i
    have hi : ((v i).1 : ZMod N) = ((v i).2 : ZMod N) := by
      apply sub_eq_zero.mp
      rw [hc, hc0, zero_mul]
    have hv := congrArg ZMod.val hi
    rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le (v i).1.isLt hLN),
      ZMod.val_natCast_of_lt (lt_of_lt_of_le (v i).2.isLt hLN)] at hv
    exact Fin.ext hv
  · intro hv
    constructor <;> simp [fejerPairRelation, hv]

theorem fejer_vertex_injective_of_feature_line {N L : Nat} [NeZero N] [Fact N.Prime]
    {I X : Type*} [Fintype I] [DecidableEq I]
    (hL : 2 ≤ L) (hI : 2 < Fintype.card I)
    (vertex : I → X) (feature : X → ZMod N) (lambda : I → ZMod N)
    (hlambda : ∀ i, lambda i ≠ 0)
    (hline : ∀ v : I → Fin L × Fin L, fejerPairRelation v (feature ∘ vertex) = 0 →
      ∃ c : ZMod N, ∀ i, ((v i).1 - (v i).2 : ZMod N) = c * lambda i) :
    Function.Injective vertex := by
  classical
  intro i j hij
  by_contra hne
  have hk : ∃ k : I, k ≠ i ∧ k ≠ j := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset I) ⊆ {i, j} := by
      intro k _
      by_cases hki : k = i
      · simp [hki]
      · simp [h k hki]
    have hc := Finset.card_le_card hsub
    have htwo : ({i, j} : Finset I).card ≤ 2 := by
      exact (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at hc
    omega
  obtain ⟨k, hki, hkj⟩ := hk
  let v : I → Fin L × Fin L := fun a =>
    (⟨if a = i then 1 else 0, by split_ifs <;> omega⟩,
      ⟨if a = j then 1 else 0, by split_ifs <;> omega⟩)
  have hv (a : I) : ((v a).1 - (v a).2 : ZMod N) =
      (if a = i then 1 else 0) - (if a = j then 1 else 0) := by
    simp [v]
  have hf : fejerPairRelation v (feature ∘ vertex) = 0 := by
    simp only [fejerPairRelation, hv, sub_mul, Finset.sum_sub_distrib, Function.comp_apply]
    simp [ite_mul, hij]
  obtain ⟨c, hc⟩ := hline v hf
  have hc0 : c = 0 := by
    have ht := hc k
    rw [hv] at ht
    simp only [if_neg hki, if_neg hkj, sub_self] at ht
    exact (mul_eq_zero.mp ht.symm).resolve_right (hlambda k)
  have hi := hc i
  rw [hv, hc0] at hi
  simp [hne] at hi

end LeanProofs.GowersSzemeredi

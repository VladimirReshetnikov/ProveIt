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
  intro i j hij
  by_contra hne
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (Finset.card_le_two.trans_lt (hI.trans_eq Finset.card_univ.symm) :
      ({i, j} : Finset I).card < (Finset.univ : Finset I).card)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  let v : I → Fin L × Fin L := fun a =>
    (⟨if a = i then 1 else 0, by split_ifs <;> omega⟩,
      ⟨if a = j then 1 else 0, by split_ifs <;> omega⟩)
  have hv (a : I) : ((v a).1 - (v a).2 : ZMod N) =
      (if a = i then 1 else 0) - (if a = j then 1 else 0) := by
    simp [v]
  obtain ⟨c, hc⟩ := hline v (by
    simp only [fejerPairRelation, hv, sub_mul, Finset.sum_sub_distrib, Function.comp_apply]
    simp [ite_mul, hij])
  have hc0 : c = 0 := by simpa [hv, hk.1, hk.2, hlambda k] using (hc k).symm
  simpa [hv, hc0, hne] using hc i

end LeanProofs.GowersSzemeredi

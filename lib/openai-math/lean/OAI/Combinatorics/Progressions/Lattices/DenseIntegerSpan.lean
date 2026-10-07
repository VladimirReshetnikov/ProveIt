/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.ProperSubspaceCount
import OAI.Combinatorics.Progressions.Lattices.IntegerAbsInterval

namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bounded_integer_points_card_le_of_proper_subspace
    (U : Submodule ℝ (ι → ℝ)) (hU : U ≠ ⊤)
    (H : Finset (ι → ℤ)) (T : ι → ℝ) (R : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hR : 1 ≤ R)
    (hmem : ∀ h ∈ H, (fun i => (h i : ℝ)) ∈ U)
    (hbound : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ R * T i) :
    ∃ j : ι, (H.card : ℝ) ≤
      (3 * R) ^ (Fintype.card ι - 1) * ∏ i : {i : ι // i ≠ j}, T i.val := by
  classical
  obtain ⟨j, hj⟩ := integer_points_card_le_of_proper_subspace U hU H
    (fun i => integerAbsInterval (R * T i)) hmem
    (fun h hh i => (mem_integerAbsInterval _ _).mpr (hbound h hh i))
  refine ⟨j, ?_⟩
  have hnum : Fintype.card {i : ι // i ≠ j} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    (H.card : ℝ) ≤ ∏ i : {i : ι // i ≠ j}, ((integerAbsInterval (R * T i.val)).card : ℝ) := by
      exact_mod_cast hj
    _ ≤ ∏ i : {i : ι // i ≠ j}, (3 * R) * T i.val := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        have hRT : 1 ≤ R * T i.val := by
          simpa only [mul_one] using mul_le_mul hR (hT i.val)
            (show (0 : ℝ) ≤ 1 by norm_num) (show 0 ≤ R by linarith)
        simpa only [mul_assoc] using integerAbsInterval_card_le_three (R * T i.val)
          hRT
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,
        Finset.card_univ, hnum]

theorem integer_points_span_eq_top_of_density
    (H : Finset (ι → ℤ)) (T : ι → ℝ) (R δ : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hR : 1 ≤ R)
    (hbound : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ R * T i)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card ι - 1) < δ * T i) :
    Submodule.span ℝ {x : ι → ℝ | ∃ h ∈ H, x = fun i => (h i : ℝ)} = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨j, hj⟩ := bounded_integer_points_card_le_of_proper_subspace _ hspan H T R hT hR
    (fun h hh => Submodule.subset_span ⟨h, hh, rfl⟩) hbound
  have hp : 0 < ∏ i : {i : ι // i ≠ j}, T i.val :=
    Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (hT i.val))
  have hprod : T j * (∏ i : {i : ι // i ≠ j}, T i.val) = ∏ i, T i := by
    have he : (∏ i ∈ Finset.univ.erase j, T i) = ∏ i : {i : ι // i ≠ j}, T i.val :=
      Finset.prod_subtype _ (by simp) T
    rw [← he]
    exact Finset.mul_prod_erase Finset.univ T (Finset.mem_univ j)
  have hstrict := mul_lt_mul_of_pos_right (hlarge j) hp
  have hidentity : δ * T j * (∏ i : {i : ι // i ≠ j}, T i.val) = δ * ∏ i, T i := by
    rw [mul_assoc, hprod]
  rw [hidentity] at hstrict
  exact (hstrict.trans_le hdense).not_ge hj

end Erdos3

end

end OAI

import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Round

namespace OAI

section

namespace Erdos3

open Module

theorem exists_zspan_near_of_basis_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Basis ι ℝ E) (R : ℝ) (hb : ∀ i, ‖b i‖ ≤ R) (x : E) :
    ∃ z ∈ Submodule.span ℤ (Set.range b), ‖x - z‖ ≤ (Fintype.card ι : ℝ) * R / 2 := by
  classical
  let a : ι → ℤ := fun i => round (b.repr x i)
  let z : E := ∑ i, (a i : ℝ) • b i
  have hz : z ∈ Submodule.span ℤ (Set.range b) := by
    apply Submodule.sum_mem
    intro i _
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have he : x - z = ∑ i, (b.repr x i - (a i : ℝ)) • b i := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [b.sum_repr]
  refine ⟨z, hz, ?_⟩
  rw [he]
  calc
    _ ≤ ∑ i, ‖(b.repr x i - (a i : ℝ)) • b i‖ := norm_sum_le _ _
    _ = ∑ i, |b.repr x i - (a i : ℝ)| * ‖b i‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ _i : ι, (1 / 2 : ℝ) * R := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (abs_sub_round (b.repr x i)) (hb i) (norm_nonneg _) (by norm_num)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI

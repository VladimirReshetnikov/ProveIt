import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem product_piecewise_split (S : Finset ι) (a b : ι → ℝ) :
    (∏ i, if i ∈ S then a i else b i) = (∏ i ∈ S, a i) * ∏ i ∈ Finset.univ \ S, b i := by
  rw [Finset.prod_ite]
  have h₁ : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
  have h₂ : Finset.univ.filter (fun i => i ∉ S) = Finset.univ \ S := by ext i; simp
  rw [h₁, h₂]

theorem partial_product_difference (S : Finset ι) (a b : ι → ℝ) :
    (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * (∏ i, if i ∈ S \ U then a i else b i)) =
      ∏ i, if i ∈ S then a i - b i else b i := by
  calc
    _ = (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * (∏ i ∈ S \ U, a i) * ∏ i ∈ U, b i) *
        ∏ i ∈ Finset.univ \ S, b i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U hU
      have hUS := Finset.mem_powerset.mp hU
      have he : Finset.univ \ (S \ U) = (Finset.univ \ S) ∪ U := by
        ext i
        by_cases hi : i ∈ S <;> by_cases hu : i ∈ U <;> simp_all
      have hd : Disjoint (Finset.univ \ S) U := by
        apply Finset.disjoint_left.mpr
        intro i hi hu
        exact (Finset.mem_sdiff.mp hi).2 (hUS hu)
      rw [product_piecewise_split, he, Finset.prod_union hd]
      ring
    _ = (∏ i ∈ S, (a i - b i)) * ∏ i ∈ Finset.univ \ S, b i := by
      rw [← Finset.prod_sub]
    _ = _ := (product_piecewise_split S (fun i => a i - b i) b).symm

end Erdos3

end

end OAI

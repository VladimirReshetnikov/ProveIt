import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem fiberMean_eq_zero_of_not_mem_image (F : X → R) (f : X → ℝ)
    (r : R) (hr : r ∉ Finset.univ.image F) : p.fiberMean F r f = 0 := by
  have hne : ∀ x, F x ≠ r := by
    intro x hx
    exact hr (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
  simp only [fiberMean, hne, ite_false, mean_const]

theorem fiberMean_support_subset_image (F : X → R) (f : X → ℝ) :
    Function.support (fun r => p.fiberMean F r f) ⊆ (Finset.univ.image F : Set R) := by
  intro r hr
  by_contra hn
  exact hr (p.fiberMean_eq_zero_of_not_mem_image F f r hn)

theorem fiberMean_hasFiniteSupport (F : X → R) (f : X → ℝ) :
    Function.HasFiniteSupport (fun r => p.fiberMean F r f) :=
  (Finset.finite_toSet (Finset.univ.image F)).subset (p.fiberMean_support_subset_image F f)

theorem complexMean_fiber_factor_sum_image (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    p.complexMean (fun x => (f x : ℂ) * a (F x)) =
      ∑ r ∈ Finset.univ.image F, (p.fiberMean F r f : ℂ) * a r := by
  unfold complexMean fiberMean mean
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hx : F x ∈ Finset.univ.image F := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have he (r : R) : ((if F x = r then f x else 0 : ℝ) : ℂ) =
      if F x = r then (f x : ℂ) else 0 := by split_ifs <;> rfl
  simp [he, mul_ite, ite_mul, mul_assoc, hx]

theorem complexMean_fiber_factor_summable (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    Summable (fun r => (p.fiberMean F r f : ℂ) * a r) := by
  apply summable_of_ne_finset_zero (s := Finset.univ.image F)
  intro r hr
  rw [p.fiberMean_eq_zero_of_not_mem_image F f r hr, Complex.ofReal_zero, zero_mul]

theorem complexMean_fiber_factor_tsum (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    p.complexMean (fun x => (f x : ℂ) * a (F x)) =
      ∑' r, (p.fiberMean F r f : ℂ) * a r := by
  rw [tsum_eq_sum (s := Finset.univ.image F) (fun r hr => by
    rw [p.fiberMean_eq_zero_of_not_mem_image F f r hr, Complex.ofReal_zero, zero_mul])]
  exact p.complexMean_fiber_factor_sum_image F f a

end Erdos3.FiniteProbabilityWeights

end

end OAI

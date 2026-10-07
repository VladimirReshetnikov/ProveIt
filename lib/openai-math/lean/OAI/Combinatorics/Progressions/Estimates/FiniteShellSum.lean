import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_le_local_sum_add_shell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L U : Finset ι) (hLU : L ⊆ U) (f : ι → ℝ) {M : ℝ}
    (hsupport : ∀ x, x ∉ U → f x = 0) (hf : ∀ x, f x ≤ M) :
    (∑ x, f x) ≤ (∑ x ∈ L, f x) + M * ((U.card : ℝ) - L.card) := by
  have hpoint (x : ι) : f x ≤ (if x ∈ L then f x else 0) +
      M * ((if x ∈ U then 1 else 0) - (if x ∈ L then 1 else 0)) := by
    by_cases hxL : x ∈ L
    · simp [hxL, hLU hxL]
    · by_cases hxU : x ∈ U
      · simpa only [hxL, hxU, ite_false, ite_true, sub_zero, mul_one, zero_add] using hf x
      · simp [hxL, hxU, hsupport x hxU]
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset ι)) => hpoint x)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one] using h

end Erdos3

end

end OAI

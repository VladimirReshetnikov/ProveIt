import FabiusFunction.HyperbolicActivation
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Taylor expansion of the activation probability

This module computes the degree-nine Taylor jet of the real hyperbolic
tangent at the origin and transfers it through the removable quotient
defining `activationProbability`.  The resulting headline theorem is

`activationProbability x = x^2/3 - 2*x^4/15 + 17*x^6/315 -
  62*x^8/2835 + O(x^10)`.

The proof avoids ten rounds of symbolic differentiation.  Analyticity gives
the canonical power series with coefficients `iteratedDeriv n f 0 / n!`,
while the identity

`tanh * cosh = sinh`

and the iterated Leibniz rule recursively determine the finite derivative
table.  Mathlib's analytic partial-sum estimate supplies the order-eleven
remainder for `tanh`; division by the removable factor `x` then gives the
order-ten activation remainder.  This is deliberately a finite-jet result,
not an all-order Bernoulli expansion or a radius-of-convergence theorem.
-/

set_option autoImplicit false

open Asymptotics Filter
open scoped Topology

namespace Fabius

noncomputable section

private theorem analyticAt_tanh (x : ℝ) : AnalyticAt ℝ Real.tanh x := by
  have htanh : Real.tanh = Real.sinh / Real.cosh := by
    funext y
    simpa only [Pi.div_apply] using
      (Real.tanh_eq_sinh_div_cosh (x := y))
  have h := (Real.analyticAt_sinh (x := x)).div
    (Real.analyticAt_cosh (x := x)) (Real.cosh_pos x).ne'
  rw [htanh]
  exact h

private theorem tanh_mul_cosh : Real.tanh * Real.cosh = Real.sinh := by
  funext x
  simp only [Pi.mul_apply, Real.tanh_eq_sinh_div_cosh]
  exact div_mul_cancel₀ _ (Real.cosh_pos x).ne'

private theorem iteratedDeriv_tanh_zero_table :
    iteratedDeriv 0 Real.tanh 0 = 0 ∧
    iteratedDeriv 1 Real.tanh 0 = 1 ∧
    iteratedDeriv 2 Real.tanh 0 = 0 ∧
    iteratedDeriv 3 Real.tanh 0 = -2 ∧
    iteratedDeriv 4 Real.tanh 0 = 0 ∧
    iteratedDeriv 5 Real.tanh 0 = 16 ∧
    iteratedDeriv 6 Real.tanh 0 = 0 ∧
    iteratedDeriv 7 Real.tanh 0 = -272 ∧
    iteratedDeriv 8 Real.tanh 0 = 0 ∧
    iteratedDeriv 9 Real.tanh 0 = 7936 ∧
    iteratedDeriv 10 Real.tanh 0 = 0 := by
  have hprod (n : ℕ) := iteratedDeriv_mul
    (x := (0 : ℝ)) (n := n)
    ((analyticAt_tanh 0).contDiffAt)
    (Real.analyticAt_cosh (x := (0 : ℝ)).contDiffAt)
  rw [tanh_mul_cosh] at hprod
  have h0 : iteratedDeriv 0 Real.tanh 0 = 0 := by simp
  have h1 : iteratedDeriv 1 Real.tanh 0 = 1 := by
    simpa [iteratedDeriv_succ] using (hasDerivAt_tanh 0).deriv
  have h2 : iteratedDeriv 2 Real.tanh 0 = 0 := by
    have h := hprod 2
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1] at h
    linarith
  have h3 : iteratedDeriv 3 Real.tanh 0 = -2 := by
    have h := hprod 3
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2] at h
    linarith
  have h4 : iteratedDeriv 4 Real.tanh 0 = 0 := by
    have h := hprod 4
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3] at h
    linarith
  have h5 : iteratedDeriv 5 Real.tanh 0 = 16 := by
    have h := hprod 5
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4] at h
    linarith
  have h6 : iteratedDeriv 6 Real.tanh 0 = 0 := by
    have h := hprod 6
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4, h5] at h
    linarith
  have h7 : iteratedDeriv 7 Real.tanh 0 = -272 := by
    have h := hprod 7
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4, h5, h6] at h
    linarith
  have h8 : iteratedDeriv 8 Real.tanh 0 = 0 := by
    have h := hprod 8
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4, h5, h6, h7] at h
    linarith
  have h9 : iteratedDeriv 9 Real.tanh 0 = 7936 := by
    have h := hprod 9
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4, h5, h6, h7, h8] at h
    linarith
  have h10 : iteratedDeriv 10 Real.tanh 0 = 0 := by
    have h := hprod 10
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at h
    linarith
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The degree-nine Taylor polynomial of `Real.tanh` has an analytic
remainder of order eleven at the origin. -/
theorem tanh_sub_taylor_nine_isBigO :
    (fun x : ℝ ↦ Real.tanh x -
      (x - x ^ 3 / 3 + 2 * x ^ 5 / 15 - 17 * x ^ 7 / 315 +
        62 * x ^ 9 / 2835)) =O[𝓝 0] (fun x : ℝ ↦ ‖x‖ ^ 11) := by
  rcases iteratedDeriv_tanh_zero_table with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  let p := FormalMultilinearSeries.ofScalars ℝ
    (fun n ↦ iteratedDeriv n Real.tanh 0 / n.factorial)
  have hp : HasFPowerSeriesAt Real.tanh p 0 := by
    simpa only [p] using (analyticAt_tanh 0).hasFPowerSeriesAt
  have hpartial (x : ℝ) :
      p.partialSum 11 x =
        x - x ^ 3 / 3 + 2 * x ^ 5 / 15 - 17 * x ^ 7 / 315 +
          62 * x ^ 9 / 2835 := by
    simp only [p, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.ofScalars_apply_eq]
    norm_num [Finset.sum_range_succ, Nat.factorial, h0, h1, h2, h3,
      h4, h5, h6, h7, h8, h9, h10]
    ring
  simpa only [zero_add, hpartial] using hp.isBigO_sub_partialSum_pow 11

/-- The activation probability has the degree-eight expansion

`p(x) = x²/3 - 2x⁴/15 + 17x⁶/315 - 62x⁸/2835 + O(x¹⁰)`

at the origin.  The norm-power form is canonical for asymptotic estimates
and is pointwise equal to `x ^ 10` over the reals. -/
theorem activationProbability_sub_taylor_eight_isBigO :
    (fun x : ℝ ↦ activationProbability x -
      (x ^ 2 / 3 - 2 * x ^ 4 / 15 + 17 * x ^ 6 / 315 -
        62 * x ^ 8 / 2835)) =O[𝓝 0] (fun x : ℝ ↦ ‖x‖ ^ 10) := by
  let R : ℝ → ℝ := fun x ↦ Real.tanh x -
    (x - x ^ 3 / 3 + 2 * x ^ 5 / 15 - 17 * x ^ 7 / 315 +
      62 * x ^ 9 / 2835)
  let A : ℝ → ℝ := fun x ↦ activationProbability x -
    (x ^ 2 / 3 - 2 * x ^ 4 / 15 + 17 * x ^ 6 / 315 -
      62 * x ^ 8 / 2835)
  have hR : R =O[𝓝 0] (fun x : ℝ ↦ ‖x‖ ^ 11) := by
    simpa only [R] using tanh_sub_taylor_nine_isBigO
  have hx_ne : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hR_ne : R =O[𝓝[≠] 0] (fun x : ℝ ↦ ‖x‖ ^ 11) :=
    hR.mono nhdsWithin_le_nhds
  have hdiv_raw :
      (fun x : ℝ ↦ R x / x) =O[𝓝[≠] 0]
        (fun x : ℝ ↦ ‖x‖ ^ 11 / x) := by
    apply (isBigO_mul_iff_isBigO_div hx_ne).mp
    refine hR_ne.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [hx_ne] with x hx
    field_simp [hx]
  have hdiv :
      (fun x : ℝ ↦ R x / x) =O[𝓝[≠] 0]
        (fun x : ℝ ↦ ‖x‖ ^ 10) := by
    refine hdiv_raw.norm_right.congr' (Eventually.of_forall fun _ ↦ rfl) ?_
    filter_upwards [hx_ne] with x hx
    simp only [norm_div, norm_norm, norm_pow]
    field_simp [norm_ne_zero_iff.mpr hx]
  have hA_ne : A =O[𝓝[≠] 0] (fun x : ℝ ↦ ‖x‖ ^ 10) := by
    refine hdiv.neg_left.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [hx_ne] with x hx
    simp only [A, R]
    rw [activationProbability_of_ne_zero hx]
    field_simp [hx]
    ring
  rcases hA_ne.exists_pos with ⟨C, _hC, hA_ne⟩
  have hA_zero :
      ‖A 0‖ ≤ C * ‖(fun x : ℝ ↦ ‖x‖ ^ 10) 0‖ := by
    simp [A]
  have hA : IsBigOWith C (𝓝[Set.insert 0 ({0} : Set ℝ)ᶜ] 0) A
      (fun x : ℝ ↦ ‖x‖ ^ 10) :=
    hA_ne.insert hA_zero
  have hA' : A =O[𝓝 0] (fun x : ℝ ↦ ‖x‖ ^ 10) := by
    have huniv : Set.insert 0 ({0} : Set ℝ)ᶜ = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x = 0
      · exact Set.mem_insert_iff.mpr (Or.inl hx)
      · exact Set.mem_insert_iff.mpr (Or.inr (by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact hx))
    rw [huniv] at hA
    apply IsBigOWith.isBigO
    simpa only [nhdsWithin_univ] using hA
  simpa only [A] using hA'

/-- Human-facing power form of
`activationProbability_sub_taylor_eight_isBigO`. -/
theorem activationProbability_sub_taylor_eight_isBigO_pow :
    (fun x : ℝ ↦ activationProbability x -
      (x ^ 2 / 3 - 2 * x ^ 4 / 15 + 17 * x ^ 6 / 315 -
        62 * x ^ 8 / 2835)) =O[𝓝 0] (fun x : ℝ ↦ x ^ 10) := by
  refine activationProbability_sub_taylor_eight_isBigO.congr_right fun x ↦ ?_
  rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg]
  positivity

end

end Fabius

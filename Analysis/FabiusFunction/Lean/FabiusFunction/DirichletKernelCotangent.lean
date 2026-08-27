import FabiusFunction.LacunaryRieszIntegral

/-!
# The Dirichlet-kernel cotangent identity

The elementary engine behind the log-sine Fourier coefficients
(the audits' Clausen layer): for every `n`,

`sin (2(n+1)θ)·cot θ = 1 + cos (2(n+1)θ) + 2·∑_{k=1}^{n} cos (2kθ)`,

so the cotangent pairing `∫₀¹ sin (2π(n+1)t)·cot (πt) dt` collapses to
the constant term `1` — every cosine detector integrates to zero.
Combined (in later modules) with integration by parts against
`(log 2 sin πt)' = π cot πt`, this yields the Fourier coefficients
`∫₀¹ log (2 sin πt) cos (2πnt) dt = −1/(2n)` and hence, via Parseval
and Basel, the Clausen values `c₀ = π²/12` (cocycle) and `π²/4`
(Gordin observable).

Stated multiplied through by `sin θ`, the identity is a polynomial
trigonometric identity valid for **all** `θ`, proved by induction with
one `linear_combination` against `sin² + cos² = 1` per step.

* `sin_two_succ_mul_mul_cos` — the product form (all `θ`).
* `sin_two_succ_mul_mul_cot` — the cotangent form (`sin θ ≠ 0`).
* `integral_cos_two_succ_mul_pi_mul` — the detector
  `∫₀¹ cos (2(m+1)πt) dt = 0`.
* `integral_sin_two_pi_succ_mul_cot` — **the cotangent pairing**
  `∫₀¹ sin (2(n+1)πt)·cot (πt) dt = 1`.
-/

set_option autoImplicit false

open Finset Real intervalIntegral

namespace Fabius

/-- **Dirichlet-kernel identity, product form** (all `θ`):
`sin (2(n+1)θ)·cos θ = sin θ·(1 + cos (2(n+1)θ) + 2 ∑_{k=1}ⁿ cos 2kθ)`. -/
theorem sin_two_succ_mul_mul_cos (θ : ℝ) (n : ℕ) :
    Real.sin (2 * (n + 1) * θ) * Real.cos θ =
      Real.sin θ * (1 + Real.cos (2 * (n + 1) * θ) +
        2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * θ)) := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_add, mul_one, Finset.range_zero,
        Finset.sum_empty, mul_zero, add_zero]
      rw [Real.sin_two_mul, Real.cos_two_mul]
      ring
  | succ n ih =>
      push_cast
      rw [Finset.sum_range_succ,
        show (2:ℝ) * (↑n + 1 + 1) * θ = 2 * (↑n + 1) * θ + 2 * θ by ring,
        Real.sin_add, Real.cos_add, Real.sin_two_mul θ,
        Real.cos_two_mul θ]
      linear_combination 2 * Real.sin (2 * (↑n + 1) * θ) * Real.cos θ *
        Real.sin_sq_add_cos_sq θ + ih

/-- **Dirichlet-kernel identity, cotangent form** (`sin θ ≠ 0`):
`sin (2(n+1)θ)·cot θ = 1 + cos (2(n+1)θ) + 2 ∑_{k=1}ⁿ cos 2kθ`. -/
theorem sin_two_succ_mul_mul_cot {θ : ℝ} (hs : Real.sin θ ≠ 0) (n : ℕ) :
    Real.sin (2 * (n + 1) * θ) * (Real.cos θ / Real.sin θ) =
      1 + Real.cos (2 * (n + 1) * θ) +
        2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * θ) := by
  have h := sin_two_succ_mul_mul_cos θ n
  rw [← mul_div_assoc, div_eq_iff hs]
  linear_combination h

/-- The cosine detector at a nonzero integer frequency:
`∫₀¹ cos (2(m+1)·πt) dt = 0`. -/
theorem integral_cos_two_succ_mul_pi_mul (m : ℕ) :
    ∫ t in (0:ℝ)..1, Real.cos (2 * (m + 1) * (π * t)) = 0 := by
  have h := integral_cos_int_freq (K := (m + 1 : ℤ)) (ψ := 0)
  rw [if_neg (by omega : (m + 1 : ℤ) ≠ 0)] at h
  calc ∫ t in (0:ℝ)..1, Real.cos (2 * (m + 1) * (π * t))
      = ∫ t in (0:ℝ)..1,
          Real.cos (2 * π * ((m + 1 : ℤ) : ℝ) * t + 0) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        congr 1
        push_cast
        ring
    _ = 0 := h

/-- The Dirichlet kernel is continuous. -/
theorem continuous_dirichlet_kernel (n : ℕ) :
    Continuous fun t : ℝ => (1 + Real.cos (2 * (n + 1) * (π * t)) +
      2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t))) := by
  have hC : Continuous fun t : ℝ => Real.cos (2 * (n + 1) * (π * t)) := by
    fun_prop
  have hS : Continuous fun t : ℝ =>
      ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t)) := by
    apply continuous_finsetSum
    intro k _
    fun_prop
  exact (continuous_const.add hC).add (hS.const_mul 2)

/-- The Dirichlet kernel has unit mean:
`∫₀¹ (1 + cos (2(n+1)πt) + 2 ∑ cos (2(k+1)πt)) dt = 1`. -/
theorem integral_dirichlet_kernel_eq_one (n : ℕ) :
    ∫ t in (0:ℝ)..1, (1 + Real.cos (2 * (n + 1) * (π * t)) +
      2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t))) = 1 := by
  have hC : Continuous fun t : ℝ => Real.cos (2 * (n + 1) * (π * t)) := by
    fun_prop
  have hS : Continuous fun t : ℝ =>
      ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t)) := by
    apply continuous_finsetSum
    intro k _
    fun_prop
  rw [intervalIntegral.integral_add
      (intervalIntegrable_const.add (hC.intervalIntegrable 0 1))
      ((hS.const_mul 2).intervalIntegrable 0 1),
    intervalIntegral.integral_add intervalIntegrable_const
      (hC.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul]
  have hsum_swap : ∫ x in (0:ℝ)..1,
      ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * x)) =
      ∑ k ∈ Finset.range n,
        ∫ x in (0:ℝ)..1, Real.cos (2 * (k + 1) * (π * x)) :=
    intervalIntegral.integral_finsetSum (fun k _ =>
      ((by fun_prop : Continuous fun t : ℝ =>
        Real.cos (2 * (k + 1) * (π * t))).intervalIntegrable 0 1))
  rw [hsum_swap, integral_cos_two_succ_mul_pi_mul n,
    Finset.sum_eq_zero fun k _ => integral_cos_two_succ_mul_pi_mul k]
  simp

/-- **The cotangent pairing**:
`∫₀¹ sin (2(n+1)·πt)·cot (πt) dt = 1` — the Dirichlet kernel reduces
the pairing to its constant term; every cosine detector vanishes.  This
is the integral consumed by the integration by parts that computes the
log-sine Fourier coefficients. -/
theorem integral_sin_two_pi_succ_mul_cot (n : ℕ) :
    ∫ t in (0:ℝ)..1, Real.sin (2 * (n + 1) * (π * t)) *
      (Real.cos (π * t) / Real.sin (π * t)) = 1 := by
  have hcongr : ∫ t in (0:ℝ)..1, Real.sin (2 * (n + 1) * (π * t)) *
      (Real.cos (π * t) / Real.sin (π * t)) =
      ∫ t in (0:ℝ)..1, (1 + Real.cos (2 * (n + 1) * (π * t)) +
        2 * ∑ k ∈ Finset.range n, Real.cos (2 * (k + 1) * (π * t))) := by
    apply intervalIntegral.integral_congr_ae
    have h1ae : ∀ᵐ t : ℝ, t ≠ (1:ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [h1ae] with t ht1 hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have hs : Real.sin (π * t) ≠ 0 := by
      have h : 0 < Real.sin (π * t) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · have := hmem.1
          positivity
        · nlinarith [Real.pi_pos, hmem.1, lt_of_le_of_ne hmem.2 ht1]
      exact ne_of_gt h
    exact sin_two_succ_mul_mul_cot hs n
  rw [hcongr, integral_dirichlet_kernel_eq_one n]

end Fabius

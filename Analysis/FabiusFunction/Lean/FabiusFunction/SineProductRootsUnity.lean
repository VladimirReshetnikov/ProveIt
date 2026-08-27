import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The sine product over roots of unity: `∏_{r=1}^{N-1} 2 sin (π r/N) = N`

The exact-grid normalization identity of the Fourier-decay audit — the
product of the chord lengths from `1` to the other `N`-th roots of
unity equals `N`.  Together with the discrete Parseval identity of
`DiscreteLacunaryParseval` it pins the dyadic sampling theory of the
Thue–Morse sine product: for `N = 2ⁿ` it is the exact evaluation
`∏_{r<2ⁿ} 2 sin (π r/2ⁿ) = 2ⁿ` used by the audit's grid identities.

* `norm_one_sub_exp_mul_I` — the **chord-length formula**
  `‖1 - e^{iθ}‖ = 2 |sin (θ/2)|`, for every real `θ`.
* `prod_two_sin_pi_div_succ` — the sine product:
  `∏_{k<n} 2 sin (π (k+1)/(n+1)) = n + 1` (stated with `N = n + 1` so
  that no nonvanishing hypothesis is needed).  The algebraic half is
  Mathlib's `IsPrimitiveRoot.prod_one_sub_pow_eq_order` applied to
  `μ = exp(2πi/(n+1))`; taking norms and evaluating each chord length
  turns it into the sine product.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- **Chord length on the unit circle**: `‖1 - e^{iθ}‖ = 2 |sin (θ/2)|`
for every real `θ`. -/
theorem norm_one_sub_exp_mul_I (θ : ℝ) :
    ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ = 2 * |Real.sin (θ / 2)| := by
  have hns : Complex.normSq (1 - Complex.exp ((θ : ℂ) * Complex.I)) =
      2 - 2 * Real.cos θ := by
    simp only [Complex.exp_mul_I, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    linear_combination Real.sin_sq_add_cos_sq θ
  have hsq : ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 =
      (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hns, mul_pow, sq_abs]
    have hc := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hc
    have hs := Real.sin_sq_add_cos_sq (θ / 2)
    nlinarith [hc, hs]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- **The sine product over the `(n+1)`-st roots of unity**:
`∏_{k<n} 2 sin (π (k+1)/(n+1)) = n + 1`.  Equivalently,
`∏_{r=1}^{N-1} 2 sin (π r/N) = N` for every `N ≥ 1` — the exact grid
normalization of the Fourier-decay audit (`N = 2ⁿ` gives
`∏_{r<2ⁿ} 2 sin (π r/2ⁿ) = 2ⁿ`). -/
theorem prod_two_sin_pi_div_succ (n : ℕ) :
    ∏ k ∈ range n, (2 * Real.sin (π * (k + 1) / (n + 1))) = (n : ℝ) + 1 := by
  have hn1C : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hμ := Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)
  have halg := hμ.prod_one_sub_pow_eq_order
  have hnorm := congrArg norm halg
  rw [norm_prod] at hnorm
  have hfac : ∀ k ∈ range n,
      ‖1 - Complex.exp (2 * π * Complex.I / ((n + 1 : ℕ) : ℂ)) ^ (k + 1)‖ =
        2 * Real.sin (π * (k + 1) / (n + 1)) := by
    intro k hk
    have hpow : Complex.exp (2 * π * Complex.I / ((n + 1 : ℕ) : ℂ)) ^ (k + 1) =
        Complex.exp (((2 * π * (k + 1) / (n + 1) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      rw [Nat.cast_add_one n]
      push_cast
      field_simp
    rw [hpow, norm_one_sub_exp_mul_I,
      show (2 * π * (k + 1) / (n + 1) : ℝ) / 2 = π * (k + 1) / (n + 1) by ring]
    have hpos : 0 < Real.sin (π * (k + 1) / (n + 1)) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n : ℝ) + 1)]
        have hk' : (k : ℝ) + 1 < (n : ℝ) + 1 := by
          have hkn := Finset.mem_range.mp hk
          exact_mod_cast Nat.add_lt_add_right hkn 1
        nlinarith [Real.pi_pos, hk']
    rw [abs_of_pos hpos]
  rw [Finset.prod_congr rfl hfac] at hnorm
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) from (Nat.cast_add_one n).symm,
    Complex.norm_natCast, Nat.cast_add, Nat.cast_one] at hnorm
  exact hnorm

/-- The sine product over the `N`-th roots of unity, for any `N ≥ 1`:
`∏_{r=1}^{N-1} 2 sin (π r/N) = N`. -/
theorem prod_two_sin_pi_div (N : ℕ) (hN : 0 < N) :
    ∏ k ∈ range (N - 1), (2 * Real.sin (π * (k + 1) / N)) = (N : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simpa using prod_two_sin_pi_div_succ m

/-- **The dyadic grid normalization of the Fourier-decay audit**:
`∏_{r=1}^{2ⁿ-1} 2 sin (π r/2ⁿ) = 2ⁿ`. -/
theorem prod_two_sin_pi_div_two_pow (n : ℕ) :
    ∏ k ∈ range (2 ^ n - 1), (2 * Real.sin (π * (k + 1) / (2:ℝ) ^ n)) =
      (2:ℝ) ^ n := by
  have h := prod_two_sin_pi_div (2 ^ n) (Nat.two_pow_pos n)
  have hc : ((2 ^ n : ℕ) : ℝ) = (2:ℝ) ^ n := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [hc] at h
  exact h

end Fabius

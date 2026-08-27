import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The variance bookkeeping of the doubling cocycle

The exact finite-`n` variance of the audit,
`Var(Sₙ) = (π²/4)n - (π²/3)(1 - 2⁻ⁿ)`, decomposes into an analytic
input and a summation identity.  The analytic input is the covariance
sequence `c_r = (π²/12)·2⁻ʳ` (the Clausen/Parseval layer, and — for
`r ≥ 1` in continuous form — the halving mechanism of
`DoublingTransferAdjoint`); the summation identity is stationarity
bookkeeping, `Var(Sₙ) = n·c₀ + 2·∑_{r=1}^{n-1} (n-r)·c_r`, evaluated
in closed form.  This file formalizes the bookkeeping layer exactly as
displayed in the audit's variance theorem:

* `sum_Ico_half_pow` — `∑_{r=1}^{n-1} (1/2)ʳ = 1 - 2·(1/2)ⁿ`;
* `sum_Ico_sub_mul_half_pow` — the audit's displayed identity
  `∑_{r=1}^{n-1} (n-r)·(1/2)ʳ = n - 2 + 2·(1/2)ⁿ`;
* `variance_closed_form` — plugging in the covariance values:
  `n·(π²/12) + 2·∑_{r=1}^{n-1} (n-r)·(π²/12)·(1/2)ʳ
     = (π²/4)·n - (π²/3)·(1 - (1/2)ⁿ)`.

Once the `L²` theory supplies `c_r = (π²/12)·2⁻ʳ` and the
stationarity decomposition, this closed form is the audit's
`thm:variance` (and the corrected variance behind the `π/√2`
iterated-logarithm constant).
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- Geometric tail: `∑_{r=1}^{n-1} (1/2)ʳ = 1 - 2·(1/2)ⁿ`. -/
theorem sum_Ico_half_pow (n : ℕ) (hn : 1 ≤ n) :
    ∑ r ∈ Finset.Ico 1 n, ((1:ℝ) / 2) ^ r = 1 - 2 * (1 / 2) ^ n := by
  induction n with
  | zero => omega
  | succ n ihn =>
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0
        simp
      · rw [Finset.sum_Ico_succ_top hn0, ihn hn0, pow_succ]
        ring

/-- **The audit's summation identity**:
`∑_{r=1}^{n-1} (n-r)·(1/2)ʳ = n - 2 + 2·(1/2)ⁿ` — the exact evaluation
of the stationarity cross terms of the doubling covariances. -/
theorem sum_Ico_sub_mul_half_pow (n : ℕ) (hn : 1 ≤ n) :
    ∑ r ∈ Finset.Ico 1 n, ((n : ℝ) - r) * ((1:ℝ) / 2) ^ r =
      (n : ℝ) - 2 + 2 * (1 / 2) ^ n := by
  induction n with
  | zero => omega
  | succ n ihn =>
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0
        simp
        norm_num
      · have hsplit : ∑ r ∈ Finset.Ico 1 n,
            (((n : ℝ) + 1) - r) * ((1:ℝ) / 2) ^ r =
            (∑ r ∈ Finset.Ico 1 n, ((n : ℝ) - r) * ((1:ℝ) / 2) ^ r) +
              ∑ r ∈ Finset.Ico 1 n, ((1:ℝ) / 2) ^ r := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun r _ => by ring
        rw [Finset.sum_Ico_succ_top hn0]
        push_cast
        rw [hsplit, ihn hn0, sum_Ico_half_pow n hn0]
        rw [pow_succ]
        ring

/-- **The variance closed form of the audit**: with the covariance
values `c_r = (π²/12)·(1/2)ʳ`, the stationarity decomposition
evaluates to `n·c₀ + 2·∑_{r=1}^{n-1}(n-r)·c_r
  = (π²/4)·n - (π²/3)·(1 - (1/2)ⁿ)` — the exact finite-`n` variance
behind the corrected iterated-logarithm constant `π/√2`. -/
theorem variance_closed_form (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (π ^ 2 / 12) +
      2 * ∑ r ∈ Finset.Ico 1 n,
        ((n : ℝ) - r) * (π ^ 2 / 12 * (1 / 2) ^ r) =
      π ^ 2 / 4 * n - π ^ 2 / 3 * (1 - (1 / 2) ^ n) := by
  have hfac : ∑ r ∈ Finset.Ico 1 n,
      ((n : ℝ) - r) * (π ^ 2 / 12 * (1 / 2) ^ r) =
      π ^ 2 / 12 * ∑ r ∈ Finset.Ico 1 n,
        ((n : ℝ) - r) * ((1:ℝ) / 2) ^ r := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [hfac, sum_Ico_sub_mul_half_pow n hn]
  ring

end Fabius

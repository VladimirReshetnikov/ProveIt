import FabiusFunction.BaileyChain
import FabiusFunction.QPochhammerInfiniteBounds

/-!
# Growth bounds along a Bailey chain

If `‖a‖ ≤ 1`, `‖q‖ ≤ 1`, `‖(q;q)_m‖⁻¹ ≤ C` for all `m`, and `‖β_j‖ ≤ B (j+1)^s`, then the
`t`-fold chain transform satisfies `‖β^{(t)}_n‖ ≤ B C^t (n+1)^{s+t}`
(`norm_baileyChainBeta_le`): each chain step is a sum of at most `n+1` terms, each bounded by
`C` times the previous bound.  This is the "constant depending only on `R` and `K`" of the
convergence discussion in the Andrews–Gordon proof.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜]

/-- Polynomial growth bound along a Bailey chain. -/
theorem norm_baileyChainBeta_le {a q : 𝕜} (ha : ‖a‖ ≤ 1) (hq : ‖q‖ ≤ 1) {C : ℝ}
    (hC : ∀ m, ‖finiteQPochhammerIn q q m‖⁻¹ ≤ C) {β : ℕ → 𝕜} {B : ℝ} {s : ℕ}
    (hβ : ∀ j, ‖β j‖ ≤ B * ((j : ℝ) + 1) ^ s) (t n : ℕ) :
    ‖baileyChainBeta a q β t n‖ ≤ B * C ^ t * ((n : ℝ) + 1) ^ (s + t) := by
  have hC0 : 0 ≤ C := (inv_nonneg.mpr (norm_nonneg _)).trans (hC 0)
  have hB0 : 0 ≤ B := by
    have := hβ 0
    simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at this
    exact (norm_nonneg _).trans this
  induction t generalizing n with
  | zero =>
      rw [baileyChainBeta_zero, pow_zero, mul_one, add_zero]
      exact hβ n
  | succ t ih =>
      rw [baileyChainBeta_succ]
      have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      calc ‖∑ j ∈ range (n + 1), a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) *
              baileyChainBeta a q β t j‖
          ≤ ∑ j ∈ range (n + 1), ‖a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) *
              baileyChainBeta a q β t j‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ range (n + 1), C * (B * C ^ t * ((n : ℝ) + 1) ^ (s + t)) := by
            refine sum_le_sum fun j hj => ?_
            have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
            rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, div_eq_mul_inv]
            have h1 : ‖a‖ ^ j * ‖q‖ ^ (j * j) ≤ 1 :=
              mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ha) (by positivity)
                (pow_le_one₀ (norm_nonneg _) hq)
            have h2 : ‖baileyChainBeta a q β t j‖ ≤ B * C ^ t * ((n : ℝ) + 1) ^ (s + t) :=
              (ih j).trans (mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hjn) _)
                (by positivity))
            calc ‖a‖ ^ j * ‖q‖ ^ (j * j) * ‖finiteQPochhammerIn q q (n - j)‖⁻¹ *
                  ‖baileyChainBeta a q β t j‖
                ≤ 1 * C * (B * C ^ t * ((n : ℝ) + 1) ^ (s + t)) := by
                  gcongr
                  exact hC _
              _ = C * (B * C ^ t * ((n : ℝ) + 1) ^ (s + t)) := by ring
        _ = ((n : ℝ) + 1) * (C * (B * C ^ t * ((n : ℝ) + 1) ^ (s + t))) := by
            rw [sum_const, card_range, nsmul_eq_mul]
            push_cast
            ring
        _ = B * C ^ (t + 1) * ((n : ℝ) + 1) ^ (s + (t + 1)) := by ring

end Fabius

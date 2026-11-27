import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Data.Rat.BigOperators

/-!
# Certified constants for the complex class-polynomial computation

Machin's identity and a geometric majorant for the arctangent tails provide
the precision needed for the large coefficients in the two quartics.
-/

namespace GRHArticle.SingularModuli

open Real
open scoped BigOperators

private def arctanPartial (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (-1 : ℚ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℚ)

private def arctanTail (x : ℚ) (N : ℕ) : ℚ := x ^ (2 * N + 1) / (1 - x ^ 2)

private theorem arctan_error {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (N : ℕ) :
    |arctan x - ∑ n ∈ Finset.range N,
      (-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)| ≤
        x ^ (2 * N + 1) / (1 - x ^ 2) := by
  let f (n : ℕ) := (-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)
  have hs : HasSum f (arctan x) := Real.hasSum_arctan
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hx₀] using hx₁)
  have hx₂ : x ^ 2 < 1 := pow_lt_one₀ hx₀ hx₁ (by decide)
  let g (n : ℕ) := x ^ (2 * N + 1) * (x ^ 2) ^ n
  have hg : HasSum g (x ^ (2 * N + 1) / (1 - x ^ 2)) := by
    simpa only [g, div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one (sq_nonneg x) hx₂).mul_left (x ^ (2 * N + 1))
  have hd (n : ℕ) : ‖f (n + N)‖ ≤ g n := by
    have he : 2 * (n + N) + 1 = (2 * N + 1) + 2 * n := by omega
    have hden : (1 : ℝ) ≤ ((2 * (n + N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_pos (2 * (n + N)))
    simp only [f, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg hx₀, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * (n + N) + 1 : ℕ) : ℝ))]
    calc
      _ ≤ x ^ (2 * (n + N) + 1) := div_le_self (pow_nonneg hx₀ _) hden
      _ = g n := by rw [he, pow_add, pow_mul]
  have hnorm : Summable (fun n ↦ ‖f (n + N)‖) :=
    hg.summable.of_nonneg_of_le (fun n ↦ norm_nonneg (f (n + N))) hd
  have hsplit := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at hsplit
  have htail : arctan x - ∑ n ∈ Finset.range N, f n = ∑' n, f (n + N) := by linarith only [hsplit]
  change |arctan x - ∑ n ∈ Finset.range N, f n| ≤ _
  rw [htail, ← Real.norm_eq_abs, ← hg.tsum_eq]
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hd hg.summable)

def piLower : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
def piUpper : ℚ := 314159265358979323846264338327950288419716939937511 / 10 ^ 50

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pi_certificate :
    piLower ≤ 16 * (arctanPartial (1 / 5) 40 - arctanTail (1 / 5) 40) -
      4 * (arctanPartial (1 / 239) 40 + arctanTail (1 / 239) 40) ∧
    16 * (arctanPartial (1 / 5) 40 + arctanTail (1 / 5) 40) -
      4 * (arctanPartial (1 / 239) 40 - arctanTail (1 / 239) 40) ≤ piUpper := by
  decide +kernel

/-- A fifty-decimal-place enclosure of π. -/
theorem piLower_le_pi_le_piUpper : (piLower : ℝ) ≤ π ∧ π ≤ (piUpper : ℝ) := by
  obtain ⟨h5l, h5u⟩ := abs_le.mp (arctan_error (x := 1 / 5) (by norm_num) (by norm_num) 40)
  obtain ⟨h239l, h239u⟩ := abs_le.mp (arctan_error (x := 1 / 239) (by norm_num) (by norm_num) 40)
  have hl := (Rat.cast_le (K := ℝ)).mpr pi_certificate.1
  have hu := (Rat.cast_le (K := ℝ)).mpr pi_certificate.2
  simp only [arctanPartial, arctanTail, Rat.cast_sum, Rat.cast_sub, Rat.cast_add, Rat.cast_mul,
    Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] at hl hu
  have hpi := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  rw [← one_div, ← one_div] at hpi
  exact ⟨by linarith only [hl, h5l, h239u, hpi], by linarith only [hu, h5u, h239l, hpi]⟩

end GRHArticle.SingularModuli

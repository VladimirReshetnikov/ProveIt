import GowersSzemeredi.Proofs16PropNineThree

/-! Explicit exponents for Proposition 9.3 (J.5c Further question 2).

Write `L = d·log(2R+1)` and `ℓ = log(1/ε)`, with `0 < ε ≤ 1`.
* `log_inv_claimNineFourDensity_le`:
  `log(1/claimNineFourDensity ε R d) ≤ 6540·log 2 + 37264·L + 9316·ℓ`.
* `log_inv_claimNineFiveDensity_le`:
  `log(1/claimNineFiveDensity ε R d) ≤ 25172·log 2 + 149056·L + 9316·ℓ`.
* `choose_window_le`: the window loss satisfies
  `C(m + k, k) ≤ (m + k)^k`.

So every loss of `milicevic_prop_9_3` is `exp(O(d·log R + log 1/ε))` per
round, with an `(m + 8s₀)^(8s₀)` window factor. Its logarithm is
`O(s₀·log(s₀/δ))`, which is polynomial in `d`, `log R` and `log(1/ε)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `log(1/(2^(−a)·x^n)) = a·log 2 + n·log(1/x)` for the shapes used here. -/
theorem log_inv_claim_density {a : Real} {c : Real} (hc : 0 < c) :
    Real.log (1 / ((2 : Real) ^ (-a) * ((c / 2) ^ 4) ^ 1164 * (c / 2) ^ 2)) =
      a * Real.log 2 + 4658 * Real.log (2 / c) := by
  have hc2 : 0 < c / 2 := by positivity
  have h2a : (0 : Real) < (2 : Real) ^ (-a) := by positivity
  rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
    Real.log_pow, Real.log_pow, Real.log_pow,
    show (2 : Real) / c = (c / 2)⁻¹ by field_simp, Real.log_inv]
  push_cast
  ring

theorem log_inv_claimNineFourDensity_le {ε : Real} (hε : 0 < ε) (hε1 : ε ≤ 1) (R d : Nat) :
    Real.log (1 / claimNineFourDensity ε R d) ≤
      6540 * Real.log 2 + 37264 * (d * Real.log (2 * R + 1)) + 9316 * Real.log (1 / ε) := by
  set K : Real := (((2 * R + 1) ^ d : Nat) : Real) with hK
  have hK1 : 1 ≤ K := by
    rw [hK]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hKpos : 0 < K := by linarith
  set c := (ε / K ^ 4) ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hlogK : Real.log K = d * Real.log (2 * R + 1) := by
    rw [hK]; push_cast; rw [Real.log_pow]
  unfold claimNineFourDensity
  simp only
  rw [← hK, ← hc, log_inv_claim_density hcpos]
  have hlog2c : Real.log (2 / c) = Real.log 2 + 2 * (4 * Real.log K + Real.log (1 / ε)) := by
    rw [Real.log_div (by norm_num) hcpos.ne', hc, Real.log_pow, Real.log_div hε.ne'
      (by positivity), Real.log_pow, one_div, Real.log_inv]
    push_cast; ring
  rw [hlog2c, hlogK]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

theorem log_inv_claimNineFiveDensity_le {ε : Real} (hε : 0 < ε) (hε1 : ε ≤ 1) (R d : Nat) :
    Real.log (1 / claimNineFiveDensity ε R d) ≤
      25172 * Real.log 2 + 149056 * (d * Real.log (2 * R + 1)) + 9316 * Real.log (1 / ε) := by
  set K : Real := (((2 * R + 1) ^ d : Nat) : Real) with hK
  have hK1 : 1 ≤ K := by
    rw [hK]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hKpos : 0 < K := by linarith
  set c := (ε / (4 * K ^ 16)) ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hlogK : Real.log K = d * Real.log (2 * R + 1) := by
    rw [hK]; push_cast; rw [Real.log_pow]
  unfold claimNineFiveDensity
  simp only
  rw [← hK, ← hc, log_inv_claim_density hcpos]
  have hlog2c : Real.log (2 / c) =
      Real.log 2 + 2 * (2 * Real.log 2 + 16 * Real.log K + Real.log (1 / ε)) := by
    rw [Real.log_div (by norm_num) hcpos.ne', hc, Real.log_pow, Real.log_div hε.ne'
      (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_pow, one_div,
      Real.log_inv, show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hlog2c, hlogK]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- The window loss. -/
theorem choose_window_le (m k : Nat) : (m + k).choose k ≤ (m + k) ^ k :=
  Nat.choose_le_pow _ _

end LeanProofs.GowersSzemeredi

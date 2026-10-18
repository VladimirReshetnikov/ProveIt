import GowersSzemeredi.Proofs13PolyStage136
import GowersSzemeredi.Proofs13UniformDensityParameters
import GowersSzemeredi.Proofs13RecurrenceParameterBudgets
import GowersSzemeredi.Proofs13SpectralExponentBound

/-! The row-length exponent of the polynomial Section 13 route (Notes L.7c, P3a).

With the polynomial Stage 13.5 the Stage 13.6 row length is `N^(e)` with
`e = polyRowExponent p α = (4Q³(2p(Q+1)^8)^4)⁻¹`, where `Q = section13Q α`.
This exponent is polynomial in `Q`, hence in `1/α`. The catalogue's row
exponent `2^(−13Q)` is doubly exponential.

Four facts make it a drop-in replacement in the corpus's rounded-budget
machinery (`uniform_rounded_power_budgets_explicit`):
* `two_mul_polyRowExponent_le`: `2e ≤ u·u₁₃₅` for every admissible `q`,
  where `u = θ₁²/(16q)` is the Stage 13.4 exponent and
  `u₁₃₅ = stage135UniformExponent p q`;
* `catalogue_length_exponent_le_polyRowExponent`: `2^(−13Q) ≤ e` whenever
  `p ≤ 2^(2^64)` (only `p ≤ 2^Q` is used), so the catalogue's Stage 13.6
  length bound follows;
* `polyRowExponent_antitone`: smaller densities give smaller exponents;
* `two_mul_polyRowExponent_le_one`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The polynomial Stage 13.6 row exponent `(4Q³(2p(Q+1)^8)^4)⁻¹`. -/
def polyRowExponent (p : Nat) (alpha : Real) : Real :=
  (4 * section13Q alpha ^ 3 * (2 * p * (section13Q alpha + 1) ^ 8) ^ 4)⁻¹

theorem polyRowDenominator_pos {p : Nat} (hp : 0 < p) {Q : Real} (hQ : 0 < Q) :
    0 < 4 * Q ^ 3 * (2 * p * (Q + 1) ^ 8) ^ 4 := by positivity

theorem polyRowExponent_pos {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1)
    {p : Nat} (hp : 0 < p) : 0 < polyRowExponent p alpha := by
  have hQ : (512 : Real) ≤ section13Q alpha := section13Q_ge_512 hα hαone
  exact inv_pos.mpr (polyRowDenominator_pos hp (by linarith))

theorem two_mul_polyRowExponent_le_one {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1)
    {p : Nat} (hp : 0 < p) : 2 * polyRowExponent p alpha ≤ 1 := by
  have hQ : (512 : Real) ≤ section13Q alpha := section13Q_ge_512 hα hαone
  have hpR : (1 : Real) ≤ p := by exact_mod_cast hp
  have hQ3 : (1 : Real) ≤ section13Q alpha ^ 3 := one_le_pow₀ (by linarith)
  have hc : (1 : Real) ≤ 2 * p * (section13Q alpha + 1) ^ 8 := by
    have h8 : (1 : Real) ≤ (section13Q alpha + 1) ^ 8 := one_le_pow₀ (by linarith)
    nlinarith only [h8, hpR]
  have hc4 : (1 : Real) ≤ (2 * p * (section13Q alpha + 1) ^ 8) ^ 4 := one_le_pow₀ hc
  have hden : (2 : Real) ≤ 4 * section13Q alpha ^ 3 * (2 * p * (section13Q alpha + 1) ^ 8) ^ 4 := by
    nlinarith only [hQ3, hc4]
  unfold polyRowExponent
  rw [mul_inv_le_iff₀ (by linarith), one_mul]
  exact hden

/-- **The power comparison.** `4Q³(2p(Q+1)^8)^4 ≤ 2^(13Q)` once `Q ≥ 512` and
`p ≤ 2^Q`. -/
theorem poly_row_power_le {Q p : Real} (hQ : 512 ≤ Q) (hp0 : 0 ≤ p) (hpQ : p ≤ (2 : Real) ^ Q) :
    4 * Q ^ 3 * (2 * p * (Q + 1) ^ 8) ^ 4 ≤ (2 : Real) ^ (13 * Q) := by
  -- write everything as powers of `y = 2 ^ (Q / 64)`, which is at least `Q / 128`
  have hpow (n : Nat) : (2 : Real) ^ (n * Q / 64) = ((2 : Real) ^ (2 * (Q / 128))) ^ n := by
    rw [← Real.rpow_mul_natCast zero_le_two]
    congr 1
    ring
  have hQy := le_two_rpow_two_mul (x := Q / 128) (by linarith)
  have hp : p ≤ ((2 : Real) ^ (2 * (Q / 128))) ^ 64 :=
    hpQ.trans_eq (by rw [← hpow]; congr 1; push_cast; ring)
  generalize (2 : Real) ^ (2 * (Q / 128)) = y at hpow hQy hp
  have hy : 4 ≤ y := by linarith
  have hy5 : Q + 1 ≤ y ^ 5 := by
    linarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hy 4)
      (by linarith : 0 ≤ y)]
  calc 4 * Q ^ 3 * (2 * p * (Q + 1) ^ 8) ^ 4
      ≤ y * (y ^ 5) ^ 3 * (y * y ^ 64 * (y ^ 5) ^ 8) ^ 4 := by gcongr <;> linarith
    _ = y ^ 436 := by ring
    _ ≤ y ^ 832 := pow_le_pow_right₀ (by linarith) (by norm_num)
    _ = (2 : Real) ^ (13 * Q) := by
      rw [← hpow]
      congr 1
      push_cast
      ring

/-- The catalogue's Stage 13.6 length exponent is below the polynomial one. -/
theorem catalogue_length_exponent_le_polyRowExponent {alpha : Real} (hα : 0 < alpha)
    (hαone : alpha ≤ 1) {p : Nat} (hp : 0 < p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    (1 : Real) / (2 : Real) ^ (13 * section13Q alpha) ≤ polyRowExponent p alpha := by
  have hQbase : (2 : Real) ^ ((2 : Nat) ^ 20) ≤ section13Q alpha := by
    have h := section13_monomial_le_Q hα hαone (a := 2 ^ 20) (b := 0) le_rfl (Nat.zero_le _)
    rwa [pow_zero, mul_one] at h
  have hQ64 : (2 : Real) ^ (64 : Nat) ≤ section13Q alpha :=
    (pow_le_pow_right₀ (by norm_num) (by norm_num)).trans hQbase
  have hpQ : (p : Real) ≤ (2 : Real) ^ section13Q alpha := by
    refine hpB.trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact hQ64
  have hQ512 : (512 : Real) ≤ section13Q alpha := section13Q_ge_512 hα hαone
  unfold polyRowExponent
  rw [one_div]
  exact inv_anti₀ (polyRowDenominator_pos hp (by linarith only [hQ512]))
    (poly_row_power_le hQ512 (Nat.cast_nonneg p) hpQ)

/-- **The recurrence and Bohr margins.** `2e ≤ u·u₁₃₅` for every admissible
spectrum size `q`. -/
theorem two_mul_polyRowExponent_le {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1)
    {p q : Nat} (hp : 0 < p) (hq : 0 < q)
    (hqBound : (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16))) :
    2 * polyRowExponent p alpha ≤
      (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real))) *
        stage135UniformExponent p q := by
  have hθ : 0 < section10Lambda (alpha ^ 32 / 16) := by unfold section10Lambda; positivity
  have hθone : section10Lambda (alpha ^ 32 / 16) ≤ 1 := by
    rw [section13_lambda_formula hα]
    exact mul_le_one₀ (by norm_num) (by positivity) (pow_le_one₀ hα.le hαone)
  have hB : 0 < section13QBound (section10Lambda (alpha ^ 32 / 16)) := by
    unfold section13QBound; positivity
  have h1 := (one_le_zpow_of_nonpos₀ hθ hθone (by norm_num)).trans_eq
    (section13_thetaOne_qBound_product hθ).symm
  have hQB := section13_qBound_le_half_Q hα hαone
  have hQ512 := section13Q_ge_512 hα hαone
  have hv : ((2 * p * (section13Q alpha + 1) ^ 8) ^ 4)⁻¹ ≤ stage135UniformExponent p q := by
    refine inv_anti₀ (by positivity) ?_
    push_cast
    gcongr
    linarith
  rw [polyRowExponent]
  generalize section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) = t1 at h1 ⊢
  generalize section13QBound (section10Lambda (alpha ^ 32 / 16)) = B at hB h1 hQB hqBound
  generalize section13Q alpha = Q at hQB hQ512 hv ⊢
  -- `t1 * B ≥ 1`, `q ≤ B` and `2B ≤ Q` give the first factor
  have hu : 1 / (2 * Q ^ 3) ≤ t1 ^ 2 / (16 * (q : Real)) := by
    refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
    linarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (by linarith : 2 * B ≤ Q) 3) (sq_nonneg t1),
      mul_le_mul_of_nonneg_right (one_le_pow₀ h1 : (1 : Real) ≤ (t1 * B) ^ 2) hB.le]
  have hX : 0 < (2 * (p : Real) * (Q + 1) ^ 8) ^ 4 := by positivity
  generalize (2 * (p : Real) * (Q + 1) ^ 8) ^ 4 = X at hX hv ⊢
  calc 2 * (4 * Q ^ 3 * X)⁻¹ = 1 / (2 * Q ^ 3) * X⁻¹ := by ring
    _ ≤ _ := mul_le_mul hu hv (inv_nonneg.mpr hX.le) (by positivity)

/-- Smaller densities give smaller row exponents. -/
theorem polyRowExponent_antitone {a b : Real} (ha : 0 < a) (hab : a ≤ b) (hbone : b ≤ 1)
    {p : Nat} (hp : 0 < p) : polyRowExponent p a ≤ polyRowExponent p b := by
  have hQ := section13Q_antitone ha hab
  have hb : 0 < b := ha.trans_le hab
  have hQb : (512 : Real) ≤ section13Q b := section13Q_ge_512 hb hbone
  have hQb0 : 0 ≤ section13Q b := by linarith only [hQb]
  have hQa0 : 0 ≤ section13Q a := by linarith only [hQb, hQ]
  have h1 : section13Q b ^ 3 ≤ section13Q a ^ 3 := pow_le_pow_left₀ hQb0 hQ 3
  have h8 : (section13Q b + 1) ^ 8 ≤ (section13Q a + 1) ^ 8 :=
    pow_le_pow_left₀ (by linarith only [hQb0]) (by linarith only [hQ]) 8
  have h2 : (2 * p * (section13Q b + 1) ^ 8) ^ 4 ≤ (2 * p * (section13Q a + 1) ^ 8) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h8 (by positivity)) 4
  unfold polyRowExponent
  apply inv_anti₀ (polyRowDenominator_pos hp (by linarith only [hQb]))
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity)
    (mul_nonneg (by norm_num) (pow_nonneg hQa0 3))

end LeanProofs.GowersSzemeredi

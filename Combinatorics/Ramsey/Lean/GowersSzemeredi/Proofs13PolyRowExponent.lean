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
    0 < 4 * Q ^ 3 * (2 * p * (Q + 1) ^ 8) ^ 4 := by
  have hpR : (0 : Real) < p := by exact_mod_cast hp
  exact mul_pos (mul_pos (by norm_num) (pow_pos hQ 3))
    (pow_pos (mul_pos (mul_pos (by norm_num) hpR) (pow_pos (by linarith) 8)) 4)

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
  have hQ0 : 0 ≤ Q := by linarith only [hQ]
  have hp4 : p ^ 4 ≤ (2 : Real) ^ (4 * Q) := by
    calc p ^ 4 ≤ ((2 : Real) ^ Q) ^ 4 := pow_le_pow_left₀ hp0 hpQ 4
      _ = (2 : Real) ^ (4 * Q) := by
        rw [← Real.rpow_mul_natCast (by norm_num)]
        congr 1
        push_cast
        ring
  have hQ1 : (Q + 1) ^ 32 ≤ 2 ^ 32 * Q ^ 32 := by
    have h := pow_le_pow_left₀ (by linarith only [hQ]) (show Q + 1 ≤ 2 * Q by linarith only [hQ]) 32
    rwa [mul_pow] at h
  have hx := le_two_rpow_two_mul (x := Q / 128) (by positivity)
  have hQle : Q ≤ 128 * (2 : Real) ^ (Q / 64) := by
    have h : (2 : Real) * (Q / 128) = Q / 64 := by ring
    rw [h] at hx
    linarith only [hx]
  have h245 : (2 : Real) ^ (245 : Real) = 128 ^ 35 := by
    rw [show (245 : Real) = ((245 : Nat) : Real) by norm_num, Real.rpow_natCast,
      show (128 : Real) = 2 ^ 7 by norm_num, ← pow_mul]
  have h38 : (2 : Real) ^ (38 : Real) = 2 ^ 38 := by
    rw [show (38 : Real) = ((38 : Nat) : Real) by norm_num, Real.rpow_natCast]
  have hsplit : (2 : Real) ^ (35 * Q / 64) = ((2 : Real) ^ (Q / 64)) ^ 35 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  have hQ35 : Q ^ 35 ≤ (2 : Real) ^ (245 : Real) * (2 : Real) ^ (35 * Q / 64) := by
    rw [h245, hsplit, ← mul_pow]
    exact pow_le_pow_left₀ hQ0 hQle 35
  have hQ3 : 0 ≤ 64 * Q ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hQ0 3)
  have h4Q : (0 : Real) ≤ (2 : Real) ^ (4 * Q) := Real.rpow_nonneg (by norm_num) _
  calc 4 * Q ^ 3 * (2 * p * (Q + 1) ^ 8) ^ 4 = 64 * Q ^ 3 * p ^ 4 * (Q + 1) ^ 32 := by ring
    _ ≤ 64 * Q ^ 3 * (2 : Real) ^ (4 * Q) * (2 ^ 32 * Q ^ 32) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp4 hQ3) hQ1 (by positivity) (mul_nonneg hQ3 h4Q)
    _ = 2 ^ 38 * Q ^ 35 * (2 : Real) ^ (4 * Q) := by ring
    _ ≤ 2 ^ 38 * ((2 : Real) ^ (245 : Real) * (2 : Real) ^ (35 * Q / 64)) * (2 : Real) ^ (4 * Q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ35 (by norm_num)) h4Q
    _ = (2 : Real) ^ ((38 : Real) + 245 + 35 * Q / 64 + 4 * Q) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), h38]
        ring
    _ ≤ (2 : Real) ^ (13 * Q) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hQ])

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
  obtain ⟨theta, hθdef⟩ : ∃ t : Real, t = section10Lambda (alpha ^ 32 / 16) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ b : Real, b = section13QBound theta := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Real, Q = section13Q alpha := ⟨_, rfl⟩
  obtain ⟨t1, ht1def⟩ : ∃ t : Real, t = section13ThetaOne theta := ⟨_, rfl⟩
  rw [← hθdef, ← ht1def]
  rw [← hθdef, ← hBdef] at hqBound
  have hθ : 0 < theta := by rw [hθdef]; unfold section10Lambda; positivity
  have hθone : theta ≤ 1 := by
    rw [hθdef, section13_lambda_formula hα]
    calc
      _ ≤ (2 : Real) ^ (-(59 : Int)) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hα.le hαone) (by positivity)
      _ ≤ 1 := by norm_num
  have hB : 0 < B := by
    rw [hBdef]
    unfold section13QBound
    exact mul_pos (pow_pos (by norm_num) _) (zpow_pos hθ _)
  have hQB : B ≤ Q / 2 := by rw [hBdef, hQdef, hθdef]; exact section13_qBound_le_half_Q hα hαone
  have hQ512 : (512 : Real) ≤ Q := by rw [hQdef]; exact section13Q_ge_512 hα hαone
  have hQpos : 0 < Q := by linarith only [hQ512]
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hqQ : (q : Real) ≤ Q / 2 := hqBound.trans hQB
  have hprod : t1 * B = theta ^ (-(2 : Int)) := by
    rw [ht1def, hBdef]
    exact section13_thetaOne_qBound_product hθ
  have hθlower : 1 / B ≤ t1 := by
    apply (div_le_iff₀ hB).mpr
    rw [hprod]
    exact one_le_zpow_of_nonpos₀ hθ hθone (by norm_num)
  have hB3 : 0 < 16 * B ^ 3 := by positivity
  have huB : 1 / (16 * B ^ 3) ≤ t1 ^ 2 / (16 * (q : Real)) := by
    have hsq : (1 / B) ^ 2 ≤ t1 ^ 2 := pow_le_pow_left₀ (by positivity) hθlower 2
    have hden : 16 * (q : Real) ≤ 16 * B := mul_le_mul_of_nonneg_left hqBound (by norm_num)
    calc 1 / (16 * B ^ 3) = (1 / B) ^ 2 / (16 * B) := by
          rw [div_pow, one_pow, div_div]
          congr 1
          ring
      _ ≤ t1 ^ 2 / (16 * (q : Real)) :=
        div_le_div₀ (sq_nonneg _) hsq (by positivity) hden
  have hden : 16 * B ^ 3 ≤ 2 * Q ^ 3 := by
    have hp3 := pow_le_pow_left₀ hB.le hQB 3
    nlinarith only [hp3]
  have hu : 1 / (2 * Q ^ 3) ≤ t1 ^ 2 / (16 * (q : Real)) :=
    (one_div_le_one_div_of_le hB3 hden).trans huB
  have hpR : (0 : Real) < p := by exact_mod_cast hp
  have hc : (((2 * p * (q + 1) ^ 8 : Nat)) : Real) ≤ 2 * p * (Q + 1) ^ 8 := by
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hqQ, hQpos]) 8
  have hcpos : (0 : Real) < ((2 * p * (q + 1) ^ 8 : Nat) : Real) := by
    have : 0 < 2 * p * (q + 1) ^ 8 := by positivity
    exact_mod_cast this
  have hv : ((2 * p * (Q + 1) ^ 8) ^ 4)⁻¹ ≤ stage135UniformExponent p q := by
    unfold stage135UniformExponent
    exact inv_anti₀ (pow_pos hcpos 4) (pow_le_pow_left₀ hcpos.le hc 4)
  have hupos : 0 < t1 ^ 2 / (16 * (q : Real)) :=
    (div_pos one_pos (mul_pos two_pos (pow_pos hQpos 3)) : (0 : Real) < 1 / (2 * Q ^ 3)).trans_le hu
  have heq : 2 * polyRowExponent p alpha = 1 / (2 * Q ^ 3) * ((2 * p * (Q + 1) ^ 8) ^ 4)⁻¹ := by
    unfold polyRowExponent
    rw [← hQdef]
    generalize (2 * (p : Real) * (Q + 1) ^ 8) ^ 4 = X
    ring
  rw [heq]
  exact mul_le_mul hu hv (by positivity) hupos.le

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

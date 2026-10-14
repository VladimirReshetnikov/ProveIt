import GowersSzemeredi.Proofs18LengthSixDensity
import GowersSzemeredi.Proofs13ThresholdExponentialEnvelope

/-! The width exponents of the length-six route are polynomial.

For `γ, θ, ρ ∈ (0, 1]` and `w = 2/(γθρ)`, every width exponent of the
length-six controls satisfies `e⁻¹ ≤ w^n` with an explicit `n`. This holds
once the recurrence constants satisfy `K₁, p₁ ≤ w³`:
* `sixEb_inv_le_power : (sixEb A Bq l γ θ ρ)⁻¹ ≤ w^(2^132)`, for
  `A = familyWidthPrefactor K₁` and `Bq = familyWidthDivisor 1 p₁`.

Thresholds are tracked as `T ≤ exp(w^n)` and exponents as `e⁻¹ ≤ w^n`.
The Bohr radius `ζ = 2^(-s)` has `s = (2/(θγ))^(2^128)`, so it enters
only through `ζ⁻¹ ≤ exp(w^(2^128))`.

As in `Proofs18LengthSixCounts`, no plain `linarith` ever sees a
hypothesis with an exponent beyond `2^24`. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The calculus -/

theorem one_le_pow_of_two_le {w : Real} (hw : 2 ≤ w) (n : Nat) : 1 ≤ w ^ n :=
  one_le_pow₀ (le_trans (by norm_num) hw)

theorem le_exp_pow_of_le_pow {w x : Real} {n : Nat} (hx : x ≤ w ^ n) : x ≤ Real.exp (w ^ n) :=
  hx.trans ((Real.add_one_le_exp _).trans' (by linarith only))

/-- A positive-power threshold with exponential numerator and denominator. -/
theorem ppt_le_exp_pow {C D e w : Real} {a r : Nat} (hw : 2 ≤ w) (hD : 0 < D) (he : 0 < e)
    (hC : C ≤ Real.exp (w ^ a)) (hDi : D⁻¹ ≤ Real.exp (w ^ a)) (hei : e⁻¹ ≤ w ^ r) :
    positivePowerThreshold C D e ≤ Real.exp (w ^ (a + r + 1)) := by
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have h := positivePowerThreshold_le_exp hD he.le
    (add_nonneg (pow_nonneg hw0 _) (pow_nonneg hw0 _)) hC hDi hei
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hp : 0 ≤ w ^ a * w ^ r := mul_nonneg (pow_nonneg hw0 _) (pow_nonneg hw0 _)
  calc (w ^ a + w ^ a) * w ^ r = 2 * (w ^ a * w ^ r) := by ring
    _ ≤ w * (w ^ a * w ^ r) := mul_le_mul_of_nonneg_right hw hp
    _ = w ^ (a + r + 1) := by rw [pow_succ, pow_add]; ring

/-- The capped width exponent `min e (log 2 / log (max 2 T))`. -/
theorem capped_inv_le_pow {e T w : Real} {r n : Nat} (hw : 2 ≤ w) (he : 0 < e)
    (hei : e⁻¹ ≤ w ^ r) (hT : T ≤ Real.exp (w ^ n)) (hrn : n + 1 ≤ r) :
    (section16CappedWidthExponent e T)⁻¹ ≤ w ^ r := by
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have hn1 := one_le_pow_of_two_le hw n
  have hL : Real.log (max 2 T) ≤ w ^ n := by
    rw [Real.log_le_iff_le_exp (lt_of_lt_of_le (by norm_num) (le_max_left _ _))]
    refine max_le ?_ hT
    calc (2 : Real) ≤ w ^ n + 1 := by linarith only [hn1]
      _ ≤ Real.exp (w ^ n) := Real.add_one_le_exp _
  have hlog2 : (1 : Real) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith only [this]
  unfold section16CappedWidthExponent
  rcases min_choice e (Real.log 2 / Real.log (max 2 T)) with h | h
  · rw [h]; exact hei
  · rw [h, inv_div]
    calc Real.log (max 2 T) / Real.log 2 ≤ w ^ n / (1 / 2) :=
          div_le_div₀ (pow_nonneg hw0 _) hL (by norm_num) hlog2
      _ = 2 * w ^ n := by ring
      _ ≤ w * w ^ n := mul_le_mul_of_nonneg_right hw (pow_nonneg hw0 _)
      _ = w ^ (n + 1) := (pow_succ' w n).symm
      _ ≤ w ^ r := pow_le_pow_right₀ (le_trans (by norm_num) hw) hrn

/-- `cubicBaseExponent q s = 2^(-27) s³ / q⁴` has `(·)⁻¹ ≤ w^(27 + 3b + 4a)`. -/
theorem cubicBaseExponent_inv_le {q : Nat} {s w : Real} {a b : Nat} (hw : 2 ≤ w) (hq : 0 < q)
    (hqw : (q : Real) ≤ w ^ a) (hs : 0 < s) (hsw : s⁻¹ ≤ w ^ b) :
    (cubicBaseExponent q s)⁻¹ ≤ w ^ (27 + b * 3 + a * 4) := by
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  have hval : (cubicBaseExponent q s)⁻¹ = (2 : Real) ^ 27 * s⁻¹ ^ 3 * (q : Real) ^ 4 := by
    unfold cubicBaseExponent
    rw [show (-(27 : Real)) = -((27 : Nat) : Real) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    field_simp
  rw [hval, pow_add, pow_add, pow_mul, pow_mul]
  have h27 : (2 : Real) ^ 27 ≤ w ^ 27 := pow_le_pow_left₀ (by norm_num) hw 27
  exact mul_le_mul (mul_le_mul h27 (pow_le_pow_left₀ (inv_pos.mpr hs).le hsw 3)
      (pow_nonneg (inv_pos.mpr hs).le _) (pow_nonneg hw0 _))
    (pow_le_pow_left₀ hq0.le hqw 4) (pow_nonneg hq0.le _)
    (mul_nonneg (pow_nonneg hw0 _) (pow_nonneg (pow_nonneg hw0 _) _))

/-- The fixed density loss has a polynomial reciprocal bound. -/
theorem section16Delta_inv_le_pw {t u : Real} {a : Nat} (hu : 2 ≤ u) (ha : 5 ≤ a)
    (ht : 0 < t) (ht1 : t ≤ 1) (hi : t⁻¹ ≤ u ^ (2 ^ a)) :
    (section16Delta t)⁻¹ ≤ u ^ (2 ^ (a + 3)) := by
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  have h32 : 32 ≤ (2 : Nat) ^ a :=
    (by norm_num : 32 ≤ (2 : Nat) ^ 5).trans (Nat.pow_le_pow_right (by norm_num) ha)
  have h4t : 4 / t ≤ u ^ (2 ^ a + 2) := by
    rw [div_eq_mul_inv, pow_add, mul_comm]
    exact mul_le_mul hi (show (4 : Real) ≤ u ^ 2 by nlinarith only [hu])
      (by norm_num) (pow_nonneg hu0 _)
  have h4t1 : 1 ≤ 4 / t := by rw [le_div_iff₀ ht]; linarith only [ht1]
  have hval : (section16Delta t)⁻¹ = (2 : Real) ^ (37 : Real) * (4 / t) ^ ((11 : Real) / 2) := by
    unfold section16Delta
    rw [mul_inv, Real.rpow_neg (by norm_num), inv_inv,
      ← Real.inv_rpow (div_nonneg ht.le (by norm_num)), inv_div]
  rw [hval]
  have h37 : (2 : Real) ^ (37 : Real) ≤ u ^ 37 := by
    rw [show (37 : Real) = ((37 : Nat) : Real) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hu 37
  have h6 : (4 / t) ^ ((11 : Real) / 2) ≤ (4 / t) ^ 6 := by
    rw [show (4 / t) ^ 6 = (4 / t) ^ ((6 : Nat) : Real) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le h4t1 (by norm_num)
  calc (2 : Real) ^ (37 : Real) * (4 / t) ^ ((11 : Real) / 2)
      ≤ u ^ 37 * (u ^ (2 ^ a + 2)) ^ 6 :=
        mul_le_mul h37 (h6.trans (pow_le_pow_left₀ (div_pos (by norm_num) ht).le h4t 6))
          (Real.rpow_nonneg (div_pos (by norm_num) ht).le _) (pow_nonneg hu0 _)
    _ = u ^ (37 + (2 ^ a + 2) * 6) := by rw [← pow_mul, ← pow_add]
    _ ≤ u ^ (2 ^ (a + 3)) := pow_le_pow_right₀ hu1 (by rw [pow_add]; norm_num; omega)

/-! ### The spectrum count -/

theorem section16ThetaOne_one_inv_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16ThetaOne theta gamma 1)⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 65) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := quarter_prod_ge_inv_sq hg ht hu2
  have hq0 : 0 < theta * gamma / 4 := by positivity
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hqi : (theta * gamma / 4)⁻¹ ≤ u ^ 2 := by
    have := inv_anti₀ (inv_pos.mpr (pow_pos hupos 2)) hq
    rwa [inv_inv] at this
  unfold section16ThetaOne
  rw [← inv_pow, show (2 : Nat) ^ 65 = 2 * (2 : Nat) ^ ((2 : Nat) ^ (1 + 5)) by norm_num, pow_mul]
  exact pow_le_pow_left₀ (inv_pos.mpr hq0).le hqi _

/-- `δ(θ₁)⁻¹ ≤ (2/(γθ))^(2^68)` for `δ = section16Delta`. -/
theorem section16Delta_one_inv_le {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16Delta (section16ThetaOne theta gamma 1))⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 68) := by
  obtain ⟨hu, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨h0, h1, -, -⟩ := section16_theta_delta_bounds 1 ht ht1 hg hg1
  exact (section16Delta_inv_le_pw hu (by norm_num) h0 h1
    (section16ThetaOne_one_inv_le hg hg1 ht ht1))

/-- The spectrum count `polyPieceSpecCount θ γ ≤ (2/(γθ))^(2^84)`. -/
theorem polyPieceSpecCount_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceSpecCount theta gamma : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 84) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨-, -, hd0, hd1⟩ := section16_theta_delta_bounds 1 ht ht1 hg hg1
  obtain ⟨hb, hb1⟩ := polyPieceBudget_pos_le hg hg1 ht ht1
  have hdi := section16Delta_one_inv_le hg hg1 ht ht1
  have hbi := polyPieceBudget_inv_le_power hg hg1 ht ht1
  have hBF := section16BaseFamilyBound_le_dyadic_power hd0 hd1 hb hb1
  unfold polyPieceSpecCount
  set d := section16Delta (section16ThetaOne theta gamma 1)
  set b := polyPieceBudget theta gamma
  set u := 2 / (gamma * theta) with hu
  clear_value u d b
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hbase : 2 / (d * b) ≤ u ^ (1 + ((2 : Nat) ^ 68 + (2 : Nat) ^ 69)) := by
    rw [show 2 / (d * b) = 2 * (d⁻¹ * b⁻¹) by field_simp, pow_add, pow_one, pow_add]
    exact mul_le_mul hu2 (mul_le_mul hdi hbi (inv_pos.mpr hb).le (pow_nonneg hupos.le _))
      (mul_nonneg (inv_pos.mpr hd0).le (inv_pos.mpr hb).le) hupos.le
  refine hBF.trans ?_
  calc (2 / (d * b)) ^ ((2 : Nat) ^ 14)
      ≤ (u ^ (1 + ((2 : Nat) ^ 68 + (2 : Nat) ^ 69))) ^ ((2 : Nat) ^ 14) :=
        pow_le_pow_left₀ (div_pos (by norm_num) (mul_pos hd0 hb)).le hbase _
    _ = u ^ ((1 + ((2 : Nat) ^ 68 + (2 : Nat) ^ 69)) * (2 : Nat) ^ 14) := (pow_mul _ _ _).symm
    _ ≤ u ^ ((2 : Nat) ^ 84) := pow_le_pow_right₀ hu1 (by norm_num)

/-! ### The capped family exponent -/

/-- The rounded power threshold and its cap, from bounds on the line exponent
`L`, the slice exponent `S` and the scale `z`. -/
theorem capped_rounded_inv_le {w L S z : Real} {nL nS nz : Nat} (hw : 2 ≤ w) (hnz : 6 ≤ nz)
    (hL : 0 < L) (hLi : L⁻¹ ≤ w ^ nL) (hS : 0 < S) (hS1 : S ≤ 1) (hSi : S⁻¹ ≤ w ^ nS)
    (hz : 0 < z) (hz1 : z ≤ 1) (hzi : z⁻¹ ≤ Real.exp (w ^ nz)) :
    (section16CappedWidthExponent (L * S / 4) (section16RoundedPowerThreshold z L S))⁻¹ ≤
      w ^ (nz + nL + nS + 5) := by
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw
  have h64 : (64 : Real) ≤ Real.exp (w ^ nz) := by
    refine le_exp_pow_of_le_pow ?_
    exact (show (64 : Real) ≤ 2 ^ 6 by norm_num).trans
      ((pow_le_pow_left₀ (by norm_num) hw 6).trans (pow_le_pow_right₀ hw1 hnz))
  have h1e : (1 : Real) ≤ Real.exp (w ^ nz) := le_trans (by norm_num) h64
  have h16 : (16 : Real) ≤ Real.exp (w ^ nz) := le_trans (by norm_num) h64
  -- the exponent `L S / 4`
  have hLS : (L * S / 4)⁻¹ ≤ w ^ (2 + nL + nS) := by
    rw [show (L * S / 4)⁻¹ = 4 * (L⁻¹ * S⁻¹) by field_simp, pow_add, pow_add, mul_assoc]
    exact mul_le_mul (show (4 : Real) ≤ w ^ 2 by nlinarith only [hw])
      (mul_le_mul hLi hSi (inv_pos.mpr hS).le (pow_nonneg hw0 _))
      (mul_nonneg (inv_pos.mpr hL).le (inv_pos.mpr hS).le) (pow_nonneg hw0 _)
  have hLS0 : 0 < L * S / 4 := by positivity
  -- the two positive-power thresholds
  have hT1 : positivePowerThreshold 16 z L ≤ Real.exp (w ^ (nz + nL + 1)) :=
    ppt_le_exp_pow hw hz hL h16 hzi hLi
  have hD2 : 0 < (z / 16) ^ (S / 2) / 4 := by positivity
  have hD2i : ((z / 16) ^ (S / 2) / 4)⁻¹ ≤ Real.exp (w ^ (nz + 1)) := by
    have hzz : 1 ≤ 16 / z := by rw [le_div_iff₀ hz]; linarith only [hz1]
    have hval : ((z / 16) ^ (S / 2) / 4)⁻¹ = 4 * (16 / z) ^ (S / 2) := by
      rw [inv_div, div_eq_mul_inv, ← Real.inv_rpow (by positivity), inv_div]
    rw [hval]
    have hr : (16 / z) ^ (S / 2) ≤ 16 / z := by
      calc (16 / z) ^ (S / 2) ≤ (16 / z) ^ (1 : Real) :=
            Real.rpow_le_rpow_of_exponent_le hzz (by linarith only [hS1])
        _ = 16 / z := Real.rpow_one _
    have hexp : Real.exp (w ^ nz) * Real.exp (w ^ nz) ≤ Real.exp (w ^ (nz + 1)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [pow_succ]
      have := pow_nonneg hw0 nz
      calc w ^ nz + w ^ nz = w ^ nz * 2 := by ring
        _ ≤ w ^ nz * w := mul_le_mul_of_nonneg_left hw this
    calc 4 * (16 / z) ^ (S / 2) ≤ 4 * (16 / z) :=
          mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = 64 * z⁻¹ := by ring
      _ ≤ Real.exp (w ^ nz) * Real.exp (w ^ nz) :=
          mul_le_mul h64 hzi (inv_pos.mpr hz).le (Real.exp_pos _).le
      _ ≤ Real.exp (w ^ (nz + 1)) := hexp
  have hT2 : positivePowerThreshold 1 ((z / 16) ^ (S / 2) / 4) (L * S / 2 - L * S / 4) ≤
      Real.exp (w ^ (nz + 1 + (2 + nL + nS) + 1)) := by
    have he : L * S / 2 - L * S / 4 = L * S / 4 := by ring
    rw [he]
    exact ppt_le_exp_pow hw hD2 hLS0
      (Real.one_le_exp_iff.mpr (pow_nonneg hw0 _))
      hD2i hLS
  have hT : section16RoundedPowerThreshold z L S ≤ Real.exp (w ^ (nz + nL + nS + 4)) := by
    unfold section16RoundedPowerThreshold section16RoundedExponentThreshold
    apply max_le
    · exact hT1.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hw1 (by omega)))
    · exact hT2.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hw1 (by omega)))
  exact capped_inv_le_pow hw hLS0 (hLS.trans (pow_le_pow_right₀ hw1 (by omega))) hT (by omega)

/-! ### The width exponents `sixEb` -/

theorem multipleS_one_eq (theta gamma : Real) :
    multipleS theta gamma 1 = (2 / (gamma * theta)) ^ ((2 : Nat) ^ 128) := by
  unfold multipleS; rw [mul_comm theta gamma]; norm_num

theorem section16Zeta_one_bounds {gamma theta : Real} (hg : 0 < gamma) (ht : 0 < theta) :
    0 < section16Zeta theta gamma 1 ∧ section16Zeta theta gamma 1 ≤ 1 ∧
      (section16Zeta theta gamma 1)⁻¹ ≤ Real.exp ((2 / (gamma * theta)) ^ ((2 : Nat) ^ 128)) := by
  have hm0 : 0 ≤ multipleS theta gamma 1 := by rw [multipleS_one_eq]; positivity
  unfold section16Zeta
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hm0])
  · rw [Real.rpow_neg (by norm_num), inv_inv, Real.rpow_def_of_pos (by norm_num),
      ← multipleS_one_eq]
    apply Real.exp_le_exp.mpr
    have h : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
    calc Real.log 2 * multipleS theta gamma 1 ≤ 1 * multipleS theta gamma 1 :=
          mul_le_mul_of_nonneg_right h hm0
      _ = multipleS theta gamma 1 := one_mul _

/-- A dimension-two width bound from counts, recurrence constants and a radius bound. -/
theorem famTwoWidth_inv_le_power {K1 p1 m qs qf d t : Nat} {w rho ζ : Real}
    (hK1 : 0 < K1) (hp1 : 0 < p1) (hw2 : 2 ≤ w) (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hrw : rho⁻¹ ≤ w)
    (hm' : (m : Real) ≤ w ^ d) (hqs' : (qs : Real) ≤ w ^ d) (hqf' : (qf : Real) ≤ w ^ d)
    (hK : (K1 : Real) ≤ w ^ 3) (hp : (p1 : Real) ≤ w ^ 3)
    (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1) (hζi : ζ⁻¹ ≤ Real.exp (w ^ t)) :
    let L := pieceLineExponent (familyWidthDivisor 1 p1) (famTwoQb m qs) (famTwoEb m qs)
      (famTwoEr m qf) rho
    let S := famPieceSliceExponent (famTwoQr m qf) (famTwoEs m qf) m rho
    let z := pieceWidthScale (familyWidthPrefactor K1) (famTwoQb m qs) ζ rho
    (section16CappedWidthExponent (L * S / 4) (section16RoundedPowerThreshold z L S))⁻¹ ≤
      w ^ (max t (2 * d + 9) + 52 * d + 222) := by
  dsimp only
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw2
  set T := max t (2 * d + 9) with hTdef
  have hζw : ζ⁻¹ ≤ Real.exp (w ^ T) :=
    hζi.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hw1 (le_max_left _ _)))
  have hr8 : (rho / 8)⁻¹ ≤ w ^ 4 := by
    rw [inv_div, div_eq_mul_inv, pow_succ]
    exact mul_le_mul (const_le_pow hw2 (by norm_num)) hrw
      (inv_pos.mpr hr).le (pow_nonneg hw0 _)
  have hr4 : (rho / 4)⁻¹ ≤ w ^ 3 := by
    rw [inv_div, div_eq_mul_inv, pow_succ]
    exact mul_le_mul (const_le_pow hw2 (by norm_num)) hrw
      (inv_pos.mpr hr).le (pow_nonneg hw0 _)
  -- the counts `m qs + 1`, `m qf + 1` and `n = 3 (m qs + 1)`
  have hmqs : ((m * qs + 1 : Nat) : Real) ≤ w ^ (d + d + 1) := by
    have h := nat_mul_le_pow hw2 hm' hqs'
    push_cast; push_cast at h
    exact add_le_pow_succ hw2 h (one_le_pow_of_two_le hw2 _)
  have hmqf : ((m * qf + 1 : Nat) : Real) ≤ w ^ (d + d + 1) := by
    have h := nat_mul_le_pow hw2 hm' hqf'
    push_cast; push_cast at h
    exact add_le_pow_succ hw2 h (one_le_pow_of_two_le hw2 _)
  have hn' : ((3 * (m * qs + 1) : Nat) : Real) ≤
      w ^ (2 + (d + d + 1)) := by
    rw [Nat.cast_mul]
    exact const_mul_le_pow hw2 (by norm_num) (by norm_num) (Nat.cast_nonneg _) hmqs
  have hn1 : ((3 * (m * qs + 1) + 1 : Nat) : Real) ≤
      w ^ (2 + (d + d + 1) + 1) := by
    rw [Nat.cast_succ]
    exact add_le_pow_succ hw2 hn' (one_le_pow_of_two_le hw2 _)
  have hfloor : ⌊famTwoQb m qs (rho / 8)⌋₊ = 3 * (m * qs + 1) := by
    unfold famTwoQb; exact Nat.floor_natCast _
  -- the line exponent
  have hBq : familyWidthDivisor 1 p1 (3 * (m * qs + 1)) ≤
      w ^ (3 + (3 + (2 + (d + d + 1) + 1) * 8)) := by
    have hval : familyWidthDivisor 1 p1 (3 * (m * qs + 1)) =
        8 * ((p1 : Real) * ((3 * (m * qs + 1) + 1 : Nat) : Real) ^ 8) := by
      unfold familyWidthDivisor; push_cast; ring
    rw [hval, pow_add, pow_add, pow_mul]
    exact mul_le_mul (const_le_pow hw2 (by norm_num))
      (mul_le_mul hp (pow_le_pow_left₀ (Nat.cast_nonneg _) hn1 8) (by positivity)
        (pow_nonneg hw0 _)) (by positivity) (pow_nonneg hw0 _)
  have hBq0 : 0 < familyWidthDivisor 1 p1 (3 * (m * qs + 1)) := familyWidthDivisor_pos hp1 _
  have hEb0 : 0 < famTwoEb m qs (rho / 8) :=
    cubicBaseExponent_pos (Nat.succ_pos _) (by positivity)
  have hEb : (famTwoEb m qs (rho / 8))⁻¹ ≤
      w ^ (27 + 4 * 3 + (d + d + 1) * 4) := by
    unfold famTwoEb
    exact cubicBaseExponent_inv_le hw2 (Nat.succ_pos _) hmqs (by positivity) hr8
  have hEr0 : 0 < famTwoEr m qf (rho / 8) := by
    unfold famTwoEr
    exact div_pos (cubicBaseExponent_pos (Nat.succ_pos _) (by positivity)) (by norm_num)
  have hEr : (famTwoEr m qf (rho / 8))⁻¹ ≤
      w ^ (4 + (27 + 4 * 3 + (d + d + 1) * 4)) := by
    unfold famTwoEr
    rw [inv_div, div_eq_mul_inv, pow_add]
    exact mul_le_mul (const_le_pow hw2 (by norm_num))
      (cubicBaseExponent_inv_le hw2 (Nat.succ_pos _) hmqf (by positivity) hr8)
      (inv_pos.mpr (cubicBaseExponent_pos (Nat.succ_pos _) (by positivity))).le
      (pow_nonneg hw0 _)
  set L := pieceLineExponent (familyWidthDivisor 1 p1) (famTwoQb m qs) (famTwoEb m qs)
    (famTwoEr m qf) rho with hLdef
  have hLval : L = famTwoEr m qf (rho / 8) * famTwoEb m qs (rho / 8) /
      familyWidthDivisor 1 p1 (3 * (m * qs + 1)) := by
    rw [hLdef]; unfold pieceLineExponent; rw [hfloor]
  have hL0 : 0 < L := by rw [hLval]; positivity
  have hLi : L⁻¹ ≤ w ^ (32 * d + 128) := by
    rw [hLval, inv_div, div_eq_mul_inv, mul_inv]
    have h := mul_le_pow_add
      (mul_nonneg (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le) hBq
      (mul_le_pow_add (inv_pos.mpr hEb0).le hEr hEb hw0) hw0
    exact le_pow_mono hw2 (by omega) h
  -- the slice exponent
  have hQr := famTwoQr_le_power hw2 hm' hqf' (rho / 8)
  have hSamp := famPieceSamples_le_power (Qr := famTwoQr m qf) hw2 hr hrw hQr hm'
  set Sp := famPieceSamples (famTwoQr m qf) m rho
  have hqS : ((m * (Sp * qf) + 1 : Nat) : Real) ≤
      w ^ (d + ((d + d + 5 + d + 7) +
        d) + 1) := by
    have h := nat_mul_le_pow hw2 hm' (nat_mul_le_pow hw2 hSamp hqf')
    push_cast; push_cast at h
    exact add_le_pow_succ hw2 h (one_le_pow_of_two_le hw2 _)
  set S := famPieceSliceExponent (famTwoQr m qf) (famTwoEs m qf) m rho with hSdef
  have hSval : S = cubicBaseExponent (m * (Sp * qf) + 1) (rho / 4) := by
    rw [hSdef]; rfl
  have hS0 : 0 < S := by rw [hSval]; exact cubicBaseExponent_pos (Nat.succ_pos _) (by positivity)
  have hS1 : S ≤ 1 := by
    rw [hSval]
    exact cubicBaseExponent_le_one (Nat.succ_pos _) (by positivity) (by linarith only [hr1])
  have hSi : S⁻¹ ≤ w ^ (20 * d + 88) := by
    rw [hSval]
    exact le_pow_mono hw2 (by omega)
      (cubicBaseExponent_inv_le hw2 (Nat.succ_pos _) hqS (by positivity) hr4)
  -- the scale `z = ζ / A`
  set z := pieceWidthScale (familyWidthPrefactor K1) (famTwoQb m qs) ζ rho with hzdef
  have hA : familyWidthPrefactor K1 (3 * (m * qs + 1)) ≤
      w ^ (2 + (3 + (2 + (d + d + 1) + 1))) := by
    unfold familyWidthPrefactor
    rw [Nat.cast_mul, pow_add, pow_add]
    exact mul_le_mul (const_le_pow hw2 (by norm_num))
      (mul_le_mul hK hn1 (Nat.cast_nonneg _) (pow_nonneg hw0 _)) (by positivity)
      (pow_nonneg hw0 _)
  have hA1 : 1 ≤ familyWidthPrefactor K1 (3 * (m * qs + 1)) := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((K1 * (3 * (m * qs + 1) + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  have hzval : z = ζ / familyWidthPrefactor K1 (3 * (m * qs + 1)) := by
    rw [hzdef]; unfold pieceWidthScale; rw [hfloor]
  have hz0 : 0 < z := by rw [hzval]; exact div_pos hζ0 (lt_of_lt_of_le zero_lt_one hA1)
  have hz1 : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact hζ1.trans hA1
  have hzi : z⁻¹ ≤ Real.exp (w ^ (T + 1)) := by
    rw [hzval, inv_div, div_eq_mul_inv]
    have hAe : familyWidthPrefactor K1 (3 * (m * qs + 1)) ≤ Real.exp (w ^ (T)) :=
      le_exp_pow_of_le_pow (le_pow_mono hw2 (by rw [hTdef]; omega) hA)
    calc familyWidthPrefactor K1 (3 * (m * qs + 1)) * ζ⁻¹
        ≤ Real.exp (w ^ (T)) * Real.exp (w ^ (T)) :=
          mul_le_mul hAe hζw (inv_pos.mpr hζ0).le (Real.exp_pos _).le
      _ = Real.exp (w ^ (T) * 2) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (w ^ (T + 1)) := by
          rw [pow_succ]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw2 (pow_nonneg hw0 _))
  have hcap := capped_rounded_inv_le hw2 (by rw [hTdef]; omega) hL0 hLi hS0 hS1 hSi hz0 hz1 hzi
  exact hcap.trans_eq (by rw [hTdef]; congr 1; omega)

/-- The family-cover exponent of `PolyCoverAt 2` is polynomial:
`polyTwoFamExp ≥ (2/(γθρ))^(-2^130)`. -/
theorem polyTwoFamExp_inv_le_power {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hK : (K1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3)
    (hp : (p1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3) :
    (polyTwoFamExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) theta gamma rho)⁻¹ ≤
      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 130) := by
  obtain ⟨hv2, hvw, hrw⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  obtain ⟨hζ0, hζ1, hζi⟩ := section16Zeta_one_bounds hg ht
  have hm := polyTwoPieces_le_power hg hg1 ht ht1
  have hqs := polyPieceSpecCount_le_power hg hg1 ht ht1
  have hqf := polyPieceFaceCount_le_power hg hg1 ht ht1
  unfold polyTwoFamExp
  dsimp only
  set ζ := section16Zeta theta gamma 1
  set m := polyTwoPieces gamma theta
  set qs := polyPieceSpecCount theta gamma
  set qf := polyPieceFaceCount theta gamma
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w ζ m qs qf
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hm' : (m : Real) ≤ w ^ ((2 : Nat) ^ 84) :=
    le_pow_mono hw2 (by norm_num) (hm.trans (pow_le_pow_left₀ hv0 hvw _))
  have hqs' : (qs : Real) ≤ w ^ ((2 : Nat) ^ 84) := hqs.trans (pow_le_pow_left₀ hv0 hvw _)
  have hqf' : (qf : Real) ≤ w ^ ((2 : Nat) ^ 84) := hqf.trans (pow_le_pow_left₀ hv0 hvw _)
  have hζw : ζ⁻¹ ≤ Real.exp (w ^ ((2 : Nat) ^ 128)) :=
    hζi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hv0 hvw _))
  have h := famTwoWidth_inv_le_power hK1 hp1 hw2 hr hr1 hrw hm' hqs' hqf' hK hp hζ0 hζ1 hζw
  exact h.trans (pow_le_pow_right₀ hw1 (by norm_num))

/-- The width exponent of `PolyCoverAt 2`: `polyTwoEb ≥ (2/(γθρ))^(-2^132)`. -/
theorem polyTwoEb_inv_le_power {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hK : (K1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3)
    (hp : (p1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3) :
    (polyTwoEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) gamma theta rho)⁻¹ ≤
      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 132) := by
  obtain ⟨hv2, hvw, -⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  have hfam := polyTwoFamExp_inv_le_power hK1 hp1 hg hg1 ht ht1 hr hr1 hK hp
  have hfam0 := polyTwoFamExp_pos (A := familyWidthPrefactor K1) (Bq := familyWidthDivisor 1 p1)
    (theta := theta) (gamma := gamma) (familyWidthDivisor_pos hp1) hr
  have hthr := polyTwoThreshold_le_power hg hg1 ht ht1
  set v := 2 / (gamma * theta) with hv
  set w := 2 / (gamma * theta * rho) with hw
  clear_value v w
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hthr' : polyTwoThreshold theta gamma ≤ Real.exp (w ^ ((2 : Nat) ^ 45)) :=
    le_exp_pow_of_le_pow (hthr.trans (pow_le_pow_left₀ hv0 hvw _))
  unfold polyTwoEb
  exact capped_inv_le_pow hw2 hfam0 (hfam.trans (pow_le_pow_right₀ hw1 (by norm_num))) hthr'
    (by norm_num)

/-- **The width exponents of the length-six route are polynomial**:
`(sixEb A Bq l γ θ ρ)⁻¹ ≤ (2/(γθρ))^(2^132)` once `K₁, p₁ ≤ (2/(γθρ))³`. -/
theorem sixEb_inv_le_power (l : Nat) {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hK : (K1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3)
    (hp : (p1 : Real) ≤ (2 / (gamma * theta * rho)) ^ 3) :
    (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) l gamma theta rho)⁻¹ ≤
      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 132) := by
  unfold sixEb
  split_ifs
  · obtain ⟨hv2, hvw, hrw⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
    have hB := section16BaseFamilyBound_le_dyadic_power hg hg1 ht ht1
    have hB0 := section16BaseFamilyBound_pos gamma theta
    set v := 2 / (gamma * theta) with hv
    set w := 2 / (gamma * theta * rho) with hw
    clear_value v w
    have hw2 : 2 ≤ w := hv2.trans hvw
    have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
    have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
    have hB' : (section16BaseFamilyBound gamma theta : Real) ≤ w ^ ((2 : Nat) ^ 14) :=
      hB.trans (pow_le_pow_left₀ hv0 hvw _)
    show (cubicBaseExponent (section16BaseFamilyBound gamma theta) rho)⁻¹ ≤ _
    have hrw1 : rho⁻¹ ≤ w ^ 1 := by rw [pow_one]; exact hrw
    exact le_pow_mono hw2 (by norm_num) (cubicBaseExponent_inv_le hw2 hB0 hB' hr hrw1)
  · exact polyTwoEb_inv_le_power hK1 hp1 hg hg1 ht ht1 hr hr1 hK hp
end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs18LengthSixCounts
import GowersSzemeredi.Proofs18FejerIterationParameters

/-! The density of the length-six discrepancy bound is polynomial.

`length_six_function_discrepancy` gives `FunctionDiscrepancyBound 4 α β σ T`
with `β = η · β₃(y) / 4`. Here `η = singlePieceEta`, the Fejér cubic
parameter is `β₃`, and its input is `y = η/(2·10⁵)`. Every density in the
chain is bounded below by a power of `X = 2/α`:
* the budget and `θ₂/2` by `X^(-2^133)`;
* the lift density `sixC` by `RecipPowerLB X _ (2^225) (2^92)`, which means
  `(c s)⁻¹ ≤ X^(2^225) s^(-2^92)`;
* `ρ₁ = C(C(C(θ₂/2)))` by `X^(-2^412)`, the single-piece density by
  `X^(-2^601)`, and `η` by `X^(-2^602)`;
* `lsBeta_inv_le : β⁻¹ ≤ X^(2^664)`.

The trap of `Proofs18LengthSixCounts` applies here too: hypotheses with
exponents beyond `2^24` must never reach a plain `linarith`. Only
`linarith only [...]` and the power rules are used after they appear. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Reciprocal power lower bounds -/

/-- `c` maps `(0, 1]` into `(0, 1]` with `(c s)⁻¹ ≤ X^a (s⁻¹)^b`. -/
def RecipPowerLB (X : Real) (c : Real → Real) (a b : Nat) : Prop :=
  ∀ s, 0 < s → s ≤ 1 → 0 < c s ∧ c s ≤ 1 ∧ (c s)⁻¹ ≤ X ^ a * s⁻¹ ^ b

theorem RecipPowerLB.mono {X : Real} {c : Real → Real} {a b a' b' : Nat} (hX : 1 ≤ X)
    (h : RecipPowerLB X c a b) (ha : a ≤ a') (hb : b ≤ b') : RecipPowerLB X c a' b' := by
  intro s hs hs1
  obtain ⟨h0, h1, h2⟩ := h s hs hs1
  have hsi : 1 ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  refine ⟨h0, h1, h2.trans ?_⟩
  exact mul_le_mul (pow_le_pow_right₀ hX ha) (pow_le_pow_right₀ hsi hb)
    (pow_nonneg (by linarith only [hsi]) _) (pow_nonneg (by linarith only [hX]) _)

/-- One unused coordinate: `liftLastC c θ = θ/2 · c(θ/2)`. -/
theorem RecipPowerLB.liftLastC {X : Real} {c : Real → Real} {a b : Nat} (hX : 2 ≤ X)
    (h : RecipPowerLB X c a b) : RecipPowerLB X (liftLastC c) (a + b + 1) (b + 1) := by
  intro s hs hs1
  have hs2 : 0 < s / 2 := half_pos hs
  have hs21 : s / 2 ≤ 1 := by linarith only [hs1]
  obtain ⟨h0, h1, h2⟩ := h (s / 2) hs2 hs21
  have hinv2 : (s / 2)⁻¹ = 2 * s⁻¹ := by rw [inv_div, div_eq_mul_inv]
  rw [hinv2] at h2
  unfold LeanProofs.GowersSzemeredi.liftLastC
  refine ⟨mul_pos hs2 h0, ?_, ?_⟩
  · calc s / 2 * c (s / 2) ≤ 1 * 1 := mul_le_mul hs21 h1 h0.le zero_le_one
      _ = 1 := one_mul 1
  · rw [mul_inv, hinv2]
    calc 2 * s⁻¹ * (c (s / 2))⁻¹ ≤ 2 * s⁻¹ * (X ^ a * (2 * s⁻¹) ^ b) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ (b + 1) * (X ^ a * s⁻¹ ^ (b + 1)) := by ring
      _ ≤ X ^ (b + 1) * (X ^ a * s⁻¹ ^ (b + 1)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hX _) (by positivity)
      _ = X ^ (a + b + 1) * s⁻¹ ^ (b + 1) := by ring

theorem RecipPowerLB.inf {X : Real} {c1 c2 : Real → Real} {a b : Nat}
    (h1 : RecipPowerLB X c1 a b) (h2 : RecipPowerLB X c2 a b) :
    RecipPowerLB X (fun t => min (c1 t) (c2 t)) a b := by
  intro s hs hs1
  obtain ⟨p1, q1, r1⟩ := h1 s hs hs1
  obtain ⟨p2, q2, r2⟩ := h2 s hs hs1
  show 0 < min (c1 s) (c2 s) ∧ min (c1 s) (c2 s) ≤ 1 ∧
    (min (c1 s) (c2 s))⁻¹ ≤ X ^ a * s⁻¹ ^ b
  refine ⟨lt_min p1 p2, (min_le_left _ _).trans q1, ?_⟩
  rcases min_choice (c1 s) (c2 s) with h | h
  · rw [h]; exact r1
  · rw [h]; exact r2

/-- A value `v ≥ X^(-e)` is sent to `c v ≥ X^(-(a + e b))`. -/
theorem RecipPowerLB.apply_le {X : Real} {c : Real → Real} {a b e : Nat} (hX : 1 ≤ X)
    (h : RecipPowerLB X c a b) {v : Real} (hv : 0 < v) (hv1 : v ≤ 1) (hve : v⁻¹ ≤ X ^ e) :
    0 < c v ∧ c v ≤ 1 ∧ (c v)⁻¹ ≤ X ^ (a + e * b) := by
  obtain ⟨p, q, r⟩ := h v hv hv1
  refine ⟨p, q, r.trans ?_⟩
  rw [pow_add, pow_mul]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr hv).le hve b)
    (pow_nonneg (by linarith only [hX]) _)

/-! ### The base scale -/

theorem two_div_alpha_ge_four {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    4 ≤ 2 / alpha := by
  rw [le_div_iff₀ ha]; linarith only [ha2]

/-- `θ₂ = θ₂(θ₁(α, α/2, 2))` is at least `X^(-(32 + 24·2^128))`. -/
theorem lsThetaTwo_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaTwo (section16ThetaOne alpha (alpha / 2) 2) ∧
      section16ThetaTwo (section16ThetaOne alpha (alpha / 2) 2) ≤ 1 ∧
      (section16ThetaTwo (section16ThetaOne alpha (alpha / 2) 2))⁻¹ ≤
        (2 / alpha) ^ (32 + 24 * (2 : Nat) ^ 128) := by
  have ha1 : alpha ≤ 1 := by linarith only [ha2]
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) 2 ha ha1 (half_pos ha)
    (by linarith only [ha2])
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  -- the base `q = α(α/2)/4` of `θ₁`, with `q⁻¹ = 8/α² ≤ 8/α³ = X³`
  have hq0 : 0 < alpha * (alpha / 2) / 4 := by positivity
  have hq : (alpha * (alpha / 2) / 4)⁻¹ ≤ (2 / alpha) ^ 3 := by
    have e1 : (alpha * (alpha / 2) / 4)⁻¹ = 8 / alpha ^ 2 := by field_simp; ring
    have e2 : (2 / alpha) ^ 3 = 8 / alpha ^ 3 := by rw [div_pow]; norm_num
    rw [e1, e2]
    exact div_le_div_of_nonneg_left (by norm_num) (pow_pos ha 3)
      (pow_le_pow_of_le_one ha.le ha1 (by norm_num))
  refine ⟨h0, h1, ?_⟩
  set X := 2 / alpha with hX
  clear_value X
  have hXpos : 0 < X := by linarith only [hX2]
  have h1inv : (section16ThetaOne alpha (alpha / 2) 2)⁻¹ ≤ X ^ (3 * (2 : Nat) ^ 128) := by
    unfold section16ThetaOne
    rw [← inv_pow, pow_mul]
    exact pow_le_pow_left₀ (inv_pos.mpr hq0).le hq _
  have hθ1pos : 0 < section16ThetaOne alpha (alpha / 2) 2 := by
    unfold section16ThetaOne; exact pow_pos hq0 _
  unfold section16ThetaTwo
  have h32 : ((2 : Real) ^ (-(32 : Real)))⁻¹ ≤ X ^ 32 := by
    rw [Real.rpow_neg (by norm_num), inv_inv,
      show (32 : Real) = ((32 : Nat) : Real) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hX2 32
  rw [mul_inv, pow_add, ← inv_pow, show 24 * (2 : Nat) ^ 128 = 3 * (2 : Nat) ^ 128 * 8 by norm_num,
    pow_mul]
  exact mul_le_mul h32 (pow_le_pow_left₀ (inv_pos.mpr hθ1pos).le h1inv 8)
    (pow_nonneg (inv_pos.mpr hθ1pos).le _) (pow_nonneg hXpos.le _)

/-- The budget `globalBudget α (α/2) 2 = θ₂/10` is at least `X^(-2^133)`. -/
theorem lsBudget_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudget alpha (alpha / 2) 2 ∧ globalBudget alpha (alpha / 2) 2 ≤ 1 ∧
      (globalBudget alpha (alpha / 2) 2)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 133) := by
  obtain ⟨h0, h1, hi⟩ := lsThetaTwo_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have h16 : (2 * ((2 : Real) ^ 2 + 1)) ≤ (2 / alpha) ^ 4 :=
    (show (2 * ((2 : Real) ^ 2 + 1)) ≤ (2 : Real) ^ 4 by norm_num).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith only [hX4]) 4)
  unfold globalBudget
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one (by norm_num)]; linarith only [h1]
  · set X := 2 / alpha with hX
    clear_value X
    have hX1 : 1 ≤ X := by linarith only [hX4]
    rw [inv_div, div_eq_mul_inv]
    calc 2 * ((2 : Real) ^ 2 + 1) * (section16ThetaTwo (section16ThetaOne alpha (alpha / 2) 2))⁻¹
        ≤ X ^ 4 * X ^ (32 + 24 * (2 : Nat) ^ 128) :=
          mul_le_mul h16 hi (inv_pos.mpr h0).le (pow_nonneg (by linarith only [hX1]) _)
      _ = X ^ (4 + (32 + 24 * (2 : Nat) ^ 128)) := (pow_add _ _ _).symm
      _ ≤ X ^ ((2 : Nat) ^ 133) := pow_le_pow_right₀ hX1 (by norm_num)

/-- `θ₂/2 = globalTheta2 α (α/2) 2` is at least `X^(-2^133)`. -/
theorem lsT2_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < lsT2 alpha ∧ lsT2 alpha ≤ 1 ∧ (lsT2 alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 133) := by
  obtain ⟨h0, h1, hi⟩ := lsThetaTwo_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  unfold lsT2 globalTheta2
  refine ⟨by positivity, by linarith only [h1], ?_⟩
  set X := 2 / alpha with hX
  clear_value X
  have hX1 : 1 ≤ X := by linarith only [hX4]
  have h2X : (2 : Real) ≤ X ^ 1 := by rw [pow_one]; linarith only [hX4]
  rw [inv_div, div_eq_mul_inv]
  calc 2 * (section16ThetaTwo (section16ThetaOne alpha (alpha / 2) 2))⁻¹
      ≤ X ^ 1 * X ^ (32 + 24 * (2 : Nat) ^ 128) :=
        mul_le_mul h2X hi (inv_pos.mpr h0).le (pow_nonneg (by linarith only [hX1]) _)
    _ = X ^ (1 + (32 + 24 * (2 : Nat) ^ 128)) := (pow_add _ _ _).symm
    _ ≤ X ^ ((2 : Nat) ^ 133) := pow_le_pow_right₀ hX1 (by norm_num)

/-! ### The lift densities -/

/-- `2/((α/2) B (s/2)) = 4 X B⁻¹ s⁻¹` for `X = 2/α`. -/
theorem two_div_half_budget_half {alpha B s : Real} (ha : 0 < alpha) (hB : 0 < B) (hs : 0 < s) :
    2 / (alpha / 2 * B * (s / 2)) = 4 * (2 / alpha) * B⁻¹ * s⁻¹ := by
  field_simp; ring

/-- The base slice density `s ↦ (s/2)/sixQb l (α/2) B (s/2)`. -/
theorem sixBaseC_recipPowerLB (l : Nat) {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    RecipPowerLB (2 / alpha) (sixBaseC sixQb alpha l) ((2 : Nat) ^ 224) ((2 : Nat) ^ 91) := by
  obtain ⟨hB, hB1, hBi⟩ := lsBudget_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  intro s hs hs1
  have hs2 : 0 < s / 2 := half_pos hs
  have hs21 : s / 2 ≤ 1 := by linarith only [hs1]
  have hQ1 := sixQb_ge_one l (alpha / 2) (globalBudget alpha (alpha / 2) 2) (s / 2)
  have hQ := sixQb_le_power l (half_pos ha) (by linarith only [ha2]) hB hB1 hs2 hs21
  rw [two_div_half_budget_half ha hB hs] at hQ
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hsi1 : 1 ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  show 0 < s / 2 / sixQb l (alpha / 2) (globalBudget alpha (alpha / 2) 2) (s / 2) ∧
    s / 2 / sixQb l (alpha / 2) (globalBudget alpha (alpha / 2) 2) (s / 2) ≤ 1 ∧
    (s / 2 / sixQb l (alpha / 2) (globalBudget alpha (alpha / 2) 2) (s / 2))⁻¹ ≤
      (2 / alpha) ^ ((2 : Nat) ^ 224) * s⁻¹ ^ ((2 : Nat) ^ 91)
  set Q := sixQb l (alpha / 2) (globalBudget alpha (alpha / 2) 2) (s / 2)
  set B := globalBudget alpha (alpha / 2) 2
  set X := 2 / alpha with hX
  clear_value Q B X
  have hX1 : 1 ≤ X := by linarith only [hX4]
  have hXpos : 0 < X := by linarith only [hX4]
  have hQpos : 0 < Q := by linarith only [hQ1]
  refine ⟨div_pos hs2 hQpos, ?_, ?_⟩
  · rw [div_le_one hQpos]; linarith only [hs21, hQ1]
  · -- `4 X B⁻¹ ≤ X^(2^133 + 3)`
    have h4 : (4 : Real) ≤ X ^ 2 := by nlinarith only [hX4]
    have hXB : 4 * X * B⁻¹ ≤ X ^ ((2 : Nat) ^ 133 + 3) := by
      calc 4 * X * B⁻¹ ≤ X ^ 2 * X ^ 1 * X ^ ((2 : Nat) ^ 133) := by
            rw [pow_one]
            exact mul_le_mul (mul_le_mul_of_nonneg_right h4 hXpos.le) hBi
              (inv_pos.mpr hB).le (by positivity)
        _ = X ^ ((2 : Nat) ^ 133 + 3) := by rw [← pow_add, ← pow_add]; norm_num
    have hbase : 4 * X * B⁻¹ * s⁻¹ ≤ X ^ ((2 : Nat) ^ 133 + 3) * s⁻¹ :=
      mul_le_mul_of_nonneg_right hXB hsi.le
    have hpow := pow_le_pow_left₀ (by positivity) hbase ((2 : Nat) ^ 90)
    have hR : (X ^ ((2 : Nat) ^ 133 + 3) * s⁻¹) ^ ((2 : Nat) ^ 90) =
        X ^ (((2 : Nat) ^ 133 + 3) * (2 : Nat) ^ 90) * s⁻¹ ^ ((2 : Nat) ^ 90) := by
      rw [mul_pow, ← pow_mul]
    have hQ' := (hQ.trans hpow).trans (le_of_eq hR)
    have hinv : (s / 2 / Q)⁻¹ = 2 * s⁻¹ * Q := by
      rw [inv_div, div_div_eq_mul_div, div_eq_mul_inv, mul_comm Q 2]; ring
    rw [hinv]
    have h2X : (2 : Real) ≤ X := by linarith only [hX4]
    calc 2 * s⁻¹ * Q ≤ X * s⁻¹ *
          (X ^ (((2 : Nat) ^ 133 + 3) * (2 : Nat) ^ 90) * s⁻¹ ^ ((2 : Nat) ^ 90)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h2X hsi.le) hQ' hQpos.le
            (mul_nonneg hXpos.le hsi.le)
      _ = X ^ (((2 : Nat) ^ 133 + 3) * (2 : Nat) ^ 90 + 1) * s⁻¹ ^ ((2 : Nat) ^ 90 + 1) := by
          rw [pow_succ X, pow_succ s⁻¹]; ring
      _ ≤ X ^ ((2 : Nat) ^ 224) * s⁻¹ ^ ((2 : Nat) ^ 91) :=
          mul_le_mul (pow_le_pow_right₀ hX1 (by norm_num)) (pow_le_pow_right₀ hsi1 (by norm_num))
            (pow_nonneg hsi.le _) (pow_nonneg hXpos.le _)

/-- The common lift density `sixC sixQb α`. -/
theorem sixC_recipPowerLB {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    RecipPowerLB (2 / alpha) (sixC sixQb alpha) ((2 : Nat) ^ 225) ((2 : Nat) ^ 92) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have h1 := sixBaseC_recipPowerLB 1 ha ha2
  have h2 := sixBaseC_recipPowerLB 2 ha ha2
  have h1' : RecipPowerLB (2 / alpha) (liftLastC^[2] (sixBaseC sixQb alpha 1))
      ((2 : Nat) ^ 225) ((2 : Nat) ^ 92) :=
    ((h1.liftLastC hX2).liftLastC hX2).mono hX1 (by norm_num) (by norm_num)
  have h2' : RecipPowerLB (2 / alpha) (liftLastC^[1] (sixBaseC sixQb alpha 2))
      ((2 : Nat) ^ 225) ((2 : Nat) ^ 92) :=
    (h2.liftLastC hX2).mono hX1 (by norm_num) (by norm_num)
  exact RecipPowerLB.inf h1' h2'

/-- `ρ₁ = C(C(C(θ₂/2)))` is at least `X^(-2^412)`. -/
theorem lsRho1_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < lsRho1 alpha ∧ lsRho1 alpha ≤ 1 ∧ (lsRho1 alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 412) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hC := sixC_recipPowerLB ha ha2
  obtain ⟨t0, t1, ti⟩ := lsT2_bounds ha ha2
  obtain ⟨u0, u1, ui⟩ := hC.apply_le hX1 t0 t1 ti
  obtain ⟨v0, v1, vi⟩ := hC.apply_le hX1 u0 u1 ui
  obtain ⟨w0, w1, wi⟩ := hC.apply_le hX1 v0 v1 vi
  refine ⟨w0, w1, wi.trans (pow_le_pow_right₀ hX1 (by norm_num))⟩

/-! ### The single-piece density and `η` -/

theorem lsRho_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < lsRho alpha ∧ lsRho alpha ≤ 1 ∧ (lsRho alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 414) := by
  obtain ⟨r0, r1, ri⟩ := lsRho1_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hval : lsRho alpha = lsRho1 alpha ^ 2 / 8 := by
    unfold lsRho spectrumPieceRho; ring
  have hinv : (lsRho alpha)⁻¹ = 8 * (lsRho1 alpha)⁻¹ ^ 2 := by
    rw [hval, inv_div, div_eq_mul_inv, inv_pow]
  have h1 : lsRho1 alpha ^ 2 ≤ 1 := pow_le_one₀ r0.le r1
  refine ⟨by rw [hval]; positivity, by rw [hval]; linarith only [h1], ?_⟩
  rw [hinv]
  set X := 2 / alpha with hX
  clear_value X
  have hX1 : 1 ≤ X := by linarith only [hX4]
  have h8 : (8 : Real) ≤ X ^ 2 := by nlinarith only [hX4]
  calc 8 * (lsRho1 alpha)⁻¹ ^ 2 ≤ X ^ 2 * (X ^ ((2 : Nat) ^ 412)) ^ 2 :=
        mul_le_mul h8 (pow_le_pow_left₀ (inv_pos.mpr r0).le ri 2) (by positivity)
          (pow_nonneg (by linarith only [hX1]) _)
    _ = X ^ (2 + (2 : Nat) ^ 412 * 2) := by rw [pow_add, pow_mul]
    _ ≤ X ^ ((2 : Nat) ^ 414) := pow_le_pow_right₀ hX1 (by norm_num)

theorem lsThS_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < lsThS alpha ∧ lsThS alpha ≤ 1 ∧ (lsThS alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 416) := by
  obtain ⟨r0, r1, ri⟩ := lsRho_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hval : lsThS alpha = lsRho alpha ^ 3 / 4 := by
    unfold lsThS singlePieceTheta; norm_num
  have hinv : (lsThS alpha)⁻¹ = 4 * (lsRho alpha)⁻¹ ^ 3 := by
    rw [hval, inv_div, div_eq_mul_inv, inv_pow]
  have h1 : lsRho alpha ^ 3 ≤ 1 := pow_le_one₀ r0.le r1
  refine ⟨by rw [hval]; positivity, by rw [hval]; linarith only [h1], ?_⟩
  rw [hinv]
  set X := 2 / alpha with hX
  clear_value X
  have hX1 : 1 ≤ X := by linarith only [hX4]
  have h4 : (4 : Real) ≤ X ^ 2 := by nlinarith only [hX4]
  calc 4 * (lsRho alpha)⁻¹ ^ 3 ≤ X ^ 2 * (X ^ ((2 : Nat) ^ 414)) ^ 3 :=
        mul_le_mul h4 (pow_le_pow_left₀ (inv_pos.mpr r0).le ri 3) (by positivity)
          (pow_nonneg (by linarith only [hX1]) _)
    _ = X ^ (2 + (2 : Nat) ^ 414 * 3) := by rw [pow_add, pow_mul]
    _ ≤ X ^ ((2 : Nat) ^ 416) := pow_le_pow_right₀ hX1 (by norm_num)

/-- The single-piece density at `k = 2`. -/
theorem lsDensity_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < singlePieceGlobalDensity sixQb (sixC sixQb alpha) alpha (alpha / 2) 2 ∧
      singlePieceGlobalDensity sixQb (sixC sixQb alpha) alpha (alpha / 2) 2 ≤ 1 ∧
      (singlePieceGlobalDensity sixQb (sixC sixQb alpha) alpha (alpha / 2) 2)⁻¹ ≤
        (2 / alpha) ^ ((2 : Nat) ^ 601) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hD : singlePieceGlobalDensity sixQb (sixC sixQb alpha) alpha (alpha / 2) 2 =
      lsThS alpha * sixBaseC sixQb alpha 2 (sixBaseC sixQb alpha 2 (lsThS alpha)) := rfl
  rw [hD]
  have hc := sixBaseC_recipPowerLB 2 ha ha2
  obtain ⟨t0, t1, ti⟩ := lsThS_bounds ha ha2
  obtain ⟨u0, u1, ui⟩ := hc.apply_le hX1 t0 t1 ti
  obtain ⟨v0, v1, vi⟩ := hc.apply_le hX1 u0 u1 ui
  refine ⟨mul_pos t0 v0, ?_, ?_⟩
  · calc lsThS alpha * sixBaseC sixQb alpha 2 (sixBaseC sixQb alpha 2 (lsThS alpha)) ≤ 1 * 1 :=
          mul_le_mul t1 v1 v0.le zero_le_one
      _ = 1 := one_mul 1
  · rw [mul_inv]
    calc (lsThS alpha)⁻¹ * (sixBaseC sixQb alpha 2 (sixBaseC sixQb alpha 2 (lsThS alpha)))⁻¹
        ≤ (2 / alpha) ^ ((2 : Nat) ^ 416) *
            (2 / alpha) ^ ((2 : Nat) ^ 224 + ((2 : Nat) ^ 224 + (2 : Nat) ^ 416 * (2 : Nat) ^ 91) *
              (2 : Nat) ^ 91) :=
          mul_le_mul ti vi (inv_pos.mpr v0).le (pow_nonneg (by linarith only [hX1]) _)
      _ = (2 / alpha) ^ ((2 : Nat) ^ 416 + ((2 : Nat) ^ 224 +
            ((2 : Nat) ^ 224 + (2 : Nat) ^ 416 * (2 : Nat) ^ 91) * (2 : Nat) ^ 91)) :=
          (pow_add _ _ _).symm
      _ ≤ (2 / alpha) ^ ((2 : Nat) ^ 601) := pow_le_pow_right₀ hX1 (by norm_num)

/-- `η⁻¹ = 2^133 D⁻¹ α⁻²` for the single-piece eta at `k = 2`. -/
theorem singlePieceEta_two_inv {alpha D : Real} (ha : 0 < alpha) (hD : 0 < D)
    (hDdef : singlePieceGlobalDensity sixQb (sixC sixQb alpha) alpha (alpha / 2) 2 = D) :
    (singlePieceEta sixQb (sixC sixQb alpha) alpha 2)⁻¹ = 2 ^ 133 * D⁻¹ * (alpha⁻¹) ^ 2 := by
  unfold singlePieceEta
  rw [hDdef]
  rw [show (-(2 * (((2 : Nat) + 1 : Int) + 1) ^ 3) : Int) = -128 by norm_num, zpow_neg]
  have h128 : (2 : Real) ^ (128 : Int) = 2 ^ (128 : Nat) := zpow_natCast 2 128
  rw [h128]
  field_simp
  ring

/-- The scalar localization factor cannot increase a nonnegative density. -/
theorem singlePieceEta_scalar_le {D alpha : Real} {k : Nat}
    (hD : 0 ≤ D) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) *
      (D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ≤ D := by
  have hfactor : (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (by positivity))
  calc _ ≤ D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 :=
        mul_le_of_le_one_left (by positivity) hfactor
    _ ≤ D / (2 : Real) ^ (k + 1) * alpha ^ 2 := div_le_self (by positivity) (by norm_num)
    _ ≤ D / (2 : Real) ^ (k + 1) := mul_le_of_le_one_right (by positivity) (pow_le_one₀ ha ha1)
    _ ≤ D := div_le_self hD (one_le_pow₀ (by norm_num))

theorem lsEta_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < singlePieceEta sixQb (sixC sixQb alpha) alpha 2 ∧
      singlePieceEta sixQb (sixC sixQb alpha) alpha 2 ≤ 1 ∧
      (singlePieceEta sixQb (sixC sixQb alpha) alpha 2)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 602) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have ha1 : alpha ≤ 1 := by linarith only [ha2]
  have hainv : alpha⁻¹ ≤ 2 / alpha := by
    rw [div_eq_mul_inv]; linarith only [inv_pos.mpr ha]
  have h133 : (2 : Real) ^ 133 ≤ (2 / alpha) ^ 133 :=
    pow_le_pow_left₀ (by norm_num) (by linarith only [hX4]) 133
  obtain ⟨d0, d1, di⟩ := lsDensity_bounds ha ha2
  set D := singlePieceGlobalDensity sixQb (sixC sixQb alpha) alpha (alpha / 2) 2 with hDdef
  have hinv := singlePieceEta_two_inv ha d0 hDdef.symm
  have hpos : 0 < singlePieceEta sixQb (sixC sixQb alpha) alpha 2 :=
    inv_pos.mp (by rw [hinv]; positivity)
  have hle : singlePieceEta sixQb (sixC sixQb alpha) alpha 2 ≤ 1 :=
    (singlePieceEta_scalar_le (k := 2) d0.le ha.le ha1).trans d1
  refine ⟨hpos, hle, ?_⟩
  rw [hinv]
  set X := 2 / alpha with hX
  clear_value X
  have hX1 : 1 ≤ X := by linarith only [hX4]
  have hX0 : 0 ≤ X := by linarith only [hX4]
  calc (2 : Real) ^ 133 * D⁻¹ * (alpha⁻¹) ^ 2 ≤ X ^ 133 * X ^ ((2 : Nat) ^ 601) * X ^ 2 :=
        mul_le_mul (mul_le_mul h133 di (inv_pos.mpr d0).le (pow_nonneg hX0 _))
          (pow_le_pow_left₀ (inv_pos.mpr ha).le hainv 2) (by positivity)
          (mul_nonneg (pow_nonneg hX0 _) (pow_nonneg hX0 _))
    _ = X ^ (133 + (2 : Nat) ^ 601 + 2) := by rw [pow_add, pow_add]
    _ ≤ X ^ ((2 : Nat) ^ 602) := pow_le_pow_right₀ hX1 (by norm_num)

/-! ### The density `β` -/

/-- The density of the length-six discrepancy bound. -/
def lsBeta (alpha : Real) : Real :=
  singlePieceEta sixQb (sixC sixQb alpha) alpha 2 *
    fejerCubicDiscrepancyParameter (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha) / 4

theorem lsCubicInput_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < singlePieceCubicInput sixQb (sixC sixQb alpha) alpha ∧
      singlePieceCubicInput sixQb (sixC sixQb alpha) alpha ≤ 1 ∧
      2 / singlePieceCubicInput sixQb (sixC sixQb alpha) alpha ≤ (2 / alpha) ^ ((2 : Nat) ^ 603) := by
  obtain ⟨e0, e1, ei⟩ := lsEta_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hval : singlePieceCubicInput sixQb (sixC sixQb alpha) alpha =
      singlePieceEta sixQb (sixC sixQb alpha) alpha 2 / 200000 := by
    unfold singlePieceCubicInput; norm_num; ring
  rw [hval]
  refine ⟨by positivity, by rw [div_le_one (by norm_num)]; linarith only [e1], ?_⟩
  have h2y : 2 / (singlePieceEta sixQb (sixC sixQb alpha) alpha 2 / 200000) =
      400000 * (singlePieceEta sixQb (sixC sixQb alpha) alpha 2)⁻¹ := by
    field_simp; ring
  rw [h2y]
  set X := 2 / alpha with hX
  clear_value X
  have hX1 : 1 ≤ X := by linarith only [hX4]
  have hX0 : 0 ≤ X := by linarith only [hX4]
  have h19 : (400000 : Real) ≤ X ^ 19 :=
    (show (400000 : Real) ≤ 2 ^ 19 by norm_num).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith only [hX4]) 19)
  calc 400000 * (singlePieceEta sixQb (sixC sixQb alpha) alpha 2)⁻¹
      ≤ X ^ 19 * X ^ ((2 : Nat) ^ 602) :=
        mul_le_mul h19 ei (inv_pos.mpr e0).le (pow_nonneg hX0 _)
    _ = X ^ (19 + (2 : Nat) ^ 602) := (pow_add _ _ _).symm
    _ ≤ X ^ ((2 : Nat) ^ 603) := pow_le_pow_right₀ hX1 (by norm_num)

/-- **The density of the length-six bound is polynomial**: `β⁻¹ ≤ (2/α)^(2^664)`. -/
theorem lsBeta_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < lsBeta alpha ∧ lsBeta alpha ≤ 1 ∧ (lsBeta alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 664) := by
  obtain ⟨e0, e1, ei⟩ := lsEta_bounds ha ha2
  obtain ⟨y0, y1, yi⟩ := lsCubicInput_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  set y := singlePieceCubicInput sixQb (sixC sixQb alpha) alpha
  set eta := singlePieceEta sixQb (sixC sixQb alpha) alpha 2
  have hP0 := fejerCubicDiscrepancyParameter_pos y0
  have hP1 := fejerCubicDiscrepancyParameter_le_one y0 y1
  have hPi := fejer_cubic_gain_inv_le_power y0 y1
  set P := fejerCubicDiscrepancyParameter y
  have hval : lsBeta alpha = eta * P / 4 := rfl
  have hinv : (lsBeta alpha)⁻¹ = eta⁻¹ * (P / 8)⁻¹ / 2 := by
    rw [hval]; field_simp; ring
  refine ⟨by rw [hval]; positivity, ?_, ?_⟩
  · rw [hval, div_le_one (by norm_num)]
    have : eta * P ≤ 1 * 1 := mul_le_mul e1 hP1 hP0.le zero_le_one
    linarith only [this]
  · rw [hinv]
    have hP8 : 0 < (P / 8)⁻¹ := inv_pos.mpr (by positivity)
    set X := 2 / alpha with hX
    set Y := 2 / y with hY
    clear_value X Y
    have hX1 : 1 ≤ X := by linarith only [hX4]
    have hX0 : 0 ≤ X := by linarith only [hX4]
    have hY0 : 0 ≤ Y := le_trans (by positivity) (le_of_eq hY.symm)
    have hYp := pow_le_pow_left₀ hY0 yi ((2 : Nat) ^ 60)
    rw [← pow_mul] at hYp
    have hprod : eta⁻¹ * (P / 8)⁻¹ ≤ X ^ ((2 : Nat) ^ 602) * X ^ ((2 : Nat) ^ 603 * (2 : Nat) ^ 60) :=
      mul_le_mul ei (hPi.trans hYp) hP8.le (pow_nonneg hX0 _)
    rw [← pow_add] at hprod
    have hhalf : eta⁻¹ * (P / 8)⁻¹ / 2 ≤ eta⁻¹ * (P / 8)⁻¹ := by
      have : 0 < eta⁻¹ * (P / 8)⁻¹ := mul_pos (inv_pos.mpr e0) hP8
      linarith only [this]
    exact hhalf.trans (hprod.trans (pow_le_pow_right₀ hX1 (by norm_num)))

end LeanProofs.GowersSzemeredi

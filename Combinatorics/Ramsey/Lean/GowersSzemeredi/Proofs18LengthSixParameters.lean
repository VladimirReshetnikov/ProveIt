import GowersSzemeredi.Proofs18LengthSixExponents
import GowersSzemeredi.Proofs03FourFactorSymmetry
import GowersSzemeredi.Proofs05Corollary58

/-! The exponents of the length-six route are polynomial in `X = 2/α`.

With `A = familyWidthPrefactor K₁`, `Bq = familyWidthDivisor 1 p₁` and
recurrence constants `K₁, p₁, p₂ ≤ X³`, every exponent in the scale
conditions of `length_six_function_discrepancy` is at least a fixed power
`X^(-n)`:
* the nested lift exponent `lsNestExp ≥ X^(-2^455)`;
* the spectrum exponent `lsEm ≥ X^(-2^545)`, and `lsMExp ≥ X^(-2^546)`;
* the worst spectrum count satisfies `lsQM ≤ X^(2^503)`, so
  `lsB ≥ X^(-2^508)`;
* the localization exponent `lsE = lsF/8 ≥ X^(-2^644)`.

Each width exponent is `sixEb` at some `(γ, θ, ρ)`. It is evaluated by
`sixEb_inv_le_power` once `X ≤ 2/(γθρ) ≤ X^n` is known. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Width exponents at a scale bounded by a power of `X` -/

/-- `2/(γθρ) ≤ X^(1+a+b+c)` from `γ⁻¹ ≤ X^a`, `θ⁻¹ ≤ X^b`, `ρ⁻¹ ≤ X^c`. -/
theorem two_div_prod_le_pow {X gamma theta rho : Real} {a b c : Nat} (hX : 2 ≤ X)
    (hg : 0 < gamma) (ht : 0 < theta) (hr : 0 < rho)
    (hga : gamma⁻¹ ≤ X ^ a) (htb : theta⁻¹ ≤ X ^ b) (hrc : rho⁻¹ ≤ X ^ c) :
    2 / (gamma * theta * rho) ≤ X ^ (1 + a + b + c) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  rw [show 2 / (gamma * theta * rho) = 2 * gamma⁻¹ * theta⁻¹ * rho⁻¹ by field_simp,
    pow_add, pow_add, pow_add, pow_one]
  have hgi := (inv_pos.mpr hg).le
  have hti := (inv_pos.mpr ht).le
  have hri := (inv_pos.mpr hr).le
  exact mul_le_mul (mul_le_mul (mul_le_mul hX hga hgi hX0) htb hti (by positivity)) hrc hri
    (by positivity)

/-- `sixEb` at a scale `X ≤ 2/(γθρ) ≤ X^n`. -/
theorem sixEb_inv_le_of_scale (l : Nat) {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {X gamma theta rho : Real} {n : Nat} (hX : 2 ≤ X)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    (hXw : X ≤ 2 / (gamma * theta * rho)) (hwX : 2 / (gamma * theta * rho) ≤ X ^ n)
    (hK : (K1 : Real) ≤ X ^ 3) (hp : (p1 : Real) ≤ X ^ 3) :
    (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) l gamma theta rho)⁻¹ ≤
      X ^ (n * (2 : Nat) ^ 132) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  have h3 : X ^ 3 ≤ (2 / (gamma * theta * rho)) ^ 3 := pow_le_pow_left₀ hX0 hXw 3
  refine (sixEb_inv_le_power l hK1 hp1 hg hg1 ht ht1 hr hr1 (hK.trans h3) (hp.trans h3)).trans ?_
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) hwX _

/-- `X ≤ 2/((α/2) B ρ)` for `B, ρ ≤ 1`. -/
theorem le_two_div_half_alpha {alpha B rho : Real} (ha : 0 < alpha) (hB : 0 < B) (hB1 : B ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) : 2 / alpha ≤ 2 / (alpha / 2 * B * rho) := by
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have : B * rho ≤ 1 := mul_le_one₀ hB1 hr.le hr1
  nlinarith

/-- The width exponents at `(α/2, B, ρ)` with `ρ⁻¹ ≤ X^c`. -/
theorem sixEb_half_budget_inv_le (l : Nat) {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {alpha rho : Real} {c : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (hrc : rho⁻¹ ≤ (2 / alpha) ^ c)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3) :
    0 < sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) l (alpha / 2)
        (globalBudget alpha (alpha / 2) 2) rho ∧
      (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) l (alpha / 2)
        (globalBudget alpha (alpha / 2) 2) rho)⁻¹ ≤
        (2 / alpha) ^ ((1 + 1 + (2 : Nat) ^ 133 + c) * (2 : Nat) ^ 132) := by
  obtain ⟨hB, hB1, hBi⟩ := lsBudget_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hai : (alpha / 2)⁻¹ ≤ (2 / alpha) ^ 1 := by rw [inv_div, pow_one]
  refine ⟨sixEb_pos (familyWidthDivisor_pos hp1) l _ _ rho hr hr1, ?_⟩
  exact sixEb_inv_le_of_scale l hK1 hp1 hX2 (half_pos ha) (by linarith only [ha2]) hB hB1 hr hr1
    (le_two_div_half_alpha ha hB hB1 hr hr1)
    (two_div_prod_le_pow hX2 (half_pos ha) hB hr hai hBi hrc) hK hp

/-- The lift exponent `sixWExp` at a density `t` with `t⁻¹ ≤ X^e`. -/
theorem sixWExp_inv_le {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {alpha t : Real} {e : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (ht : 0 < t) (ht1 : t ≤ 1) (hte : t⁻¹ ≤ (2 / alpha) ^ e)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3) :
    0 < sixWExp (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)) alpha t ∧
      (sixWExp (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)) alpha t)⁻¹ ≤
        (2 / alpha) ^ (4 + (1 + 1 + (2 : Nat) ^ 133 + (e + 3)) * (2 : Nat) ^ 132) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  have hinv8 : (t / 2 / 2 / 2)⁻¹ ≤ (2 / alpha) ^ (e + 3) := by
    rw [show (t / 2 / 2 / 2)⁻¹ = 8 * t⁻¹ by field_simp; ring, pow_add, mul_comm]
    exact mul_le_mul hte (const_le_pow hX2 (by norm_num)) (by norm_num) (pow_nonneg hX0 _)
  have hinv4 : (t / 2 / 2)⁻¹ ≤ (2 / alpha) ^ (e + 2) := by
    rw [show (t / 2 / 2)⁻¹ = 4 * t⁻¹ by field_simp; ring, pow_add, mul_comm]
    exact mul_le_mul hte (const_le_pow hX2 (by norm_num)) (by norm_num) (pow_nonneg hX0 _)
  obtain ⟨h10, h1i⟩ := sixEb_half_budget_inv_le 1 hK1 hp1 ha ha2 (by positivity)
    (by linarith only [ht1]) hinv8 hK hp
  obtain ⟨h20, h2i⟩ := sixEb_half_budget_inv_le 2 hK1 hp1 ha ha2 (by positivity)
    (by linarith only [ht1]) hinv4 hK hp
  unfold sixWExp
  set E1 := sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) 1 (alpha / 2)
    (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2)
  set E2 := sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) 2 (alpha / 2)
    (globalBudget alpha (alpha / 2) 2) (t / 2 / 2)
  set X := 2 / alpha with hX
  clear_value X E1 E2
  refine ⟨lt_min (by positivity) (by positivity), ?_⟩
  rcases min_choice (E1 / 4 / 4) (E2 / 4) with h | h
  · rw [h, show (E1 / 4 / 4)⁻¹ = 16 * E1⁻¹ by field_simp; ring, pow_add]
    exact mul_le_mul (const_le_pow hX2 (by norm_num)) h1i (inv_pos.mpr h10).le
      (pow_nonneg hX0 _)
  · rw [h, show (E2 / 4)⁻¹ = 4 * E2⁻¹ by field_simp, pow_add]
    refine mul_le_mul ((const_le_pow (n := 2) hX2 (by norm_num)).trans
      (pow_le_pow_right₀ hX1 (by norm_num))) (h2i.trans (pow_le_pow_right₀ hX1 ?_))
      (inv_pos.mpr h20).le (pow_nonneg hX0 _)
    exact Nat.mul_le_mul_right _ (by omega)

/-! ### The densities of the nest -/

theorem lsC_T2_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (0 < lsT2 alpha ∧ lsT2 alpha ≤ 1 ∧ (lsT2 alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 133)) ∧
    (0 < lsC alpha (lsT2 alpha) ∧ lsC alpha (lsT2 alpha) ≤ 1 ∧
      (lsC alpha (lsT2 alpha))⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 226)) ∧
    (0 < lsC alpha (lsC alpha (lsT2 alpha)) ∧ lsC alpha (lsC alpha (lsT2 alpha)) ≤ 1 ∧
      (lsC alpha (lsC alpha (lsT2 alpha)))⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 319)) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hC := sixC_recipPowerLB ha ha2
  obtain ⟨t0, t1, ti⟩ := lsT2_bounds ha ha2
  obtain ⟨u0, u1, ui⟩ := hC.apply_le hX1 t0 t1 ti
  have ui' := ui.trans (pow_le_pow_right₀ hX1 (by norm_num : (2 : Nat) ^ 225 + (2 : Nat) ^ 133 *
    (2 : Nat) ^ 92 ≤ (2 : Nat) ^ 226))
  obtain ⟨v0, v1, vi⟩ := hC.apply_le hX1 u0 u1 ui'
  exact ⟨⟨t0, t1, ti⟩, ⟨u0, u1, ui'⟩, ⟨v0, v1, vi.trans (pow_le_pow_right₀ hX1 (by norm_num))⟩⟩

theorem lsNestExp_bounds {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3) :
    0 < lsNestExp (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)) (lsC alpha) alpha
        (lsT2 alpha) ∧
      lsNestExp (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)) (lsC alpha) alpha
        (lsT2 alpha) ≤ 1 ∧
      (lsNestExp (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)) (lsC alpha) alpha
        (lsT2 alpha))⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 455) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  obtain ⟨⟨t0, t1, ti⟩, ⟨u0, u1, ui⟩, ⟨v0, v1, vi⟩⟩ := lsC_T2_bounds ha ha2
  obtain ⟨a0, ai⟩ := sixWExp_inv_le hK1 hp1 ha ha2 t0 t1 ti hK hp
  obtain ⟨b0, bi⟩ := sixWExp_inv_le hK1 hp1 ha ha2 u0 u1 ui hK hp
  obtain ⟨c0, ci⟩ := sixWExp_inv_le hK1 hp1 ha ha2 v0 v1 vi hK hp
  have hE : ∀ l g u s, 0 < s → s ≤ 1 →
      0 < sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) l g u s ∧
        sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) l g u s ≤ 1 :=
    fun l g u s hs hs1 => ⟨sixEb_pos (familyWidthDivisor_pos hp1) l g u s hs hs1,
      sixEb_le_one l g u s hs hs1⟩
  have hCC := sixC_pos_le (fun l g t s _ _ => sixQb_ge_one l g t s) alpha
  refine ⟨lsNestExp_pos hE hCC t0 t1, lsNestExp_le_one hE hCC t0 t1, ?_⟩
  unfold lsNestExp
  rw [mul_inv, mul_inv]
  set X := 2 / alpha with hX
  clear_value X
  have h := mul_le_pow_add
    (inv_pos.mpr c0).le (mul_le_pow_add (inv_pos.mpr b0).le ai bi hX0) ci hX0
  exact h.trans (pow_le_pow_right₀ hX1 (by norm_num))

/-! ### The spectrum scale -/

theorem lsThetaOne_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaOne alpha (alpha / 2) 2 ∧ section16ThetaOne alpha (alpha / 2) 2 ≤ alpha / 2 ∧
      (section16ThetaOne alpha (alpha / 2) 2)⁻¹ ≤ (2 / alpha) ^ (3 * (2 : Nat) ^ 128) := by
  have ha1 : alpha ≤ 1 := by linarith only [ha2]
  have hX4 := two_div_alpha_ge_four ha ha2
  have hq0 : 0 < alpha * (alpha / 2) / 4 := by positivity
  have hq1 : alpha * (alpha / 2) / 4 ≤ 1 := by nlinarith only [ha, ha1]
  have hqa : alpha * (alpha / 2) / 4 ≤ alpha / 2 := by nlinarith only [ha, ha1]
  have hq : (alpha * (alpha / 2) / 4)⁻¹ ≤ (2 / alpha) ^ 3 := by
    have e1 : (alpha * (alpha / 2) / 4)⁻¹ = 8 / alpha ^ 2 := by field_simp; ring
    have e2 : (2 / alpha) ^ 3 = 8 / alpha ^ 3 := by rw [div_pow]; norm_num
    rw [e1, e2]
    exact div_le_div_of_nonneg_left (by norm_num) (pow_pos ha 3)
      (pow_le_pow_of_le_one ha.le ha1 (by norm_num))
  unfold section16ThetaOne
  refine ⟨pow_pos hq0 _, (pow_le_of_le_one hq0.le hq1 (by positivity)).trans hqa, ?_⟩
  rw [← inv_pow, pow_mul]
  exact pow_le_pow_left₀ (inv_pos.mpr hq0).le hq _

theorem lsDelta_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < lsDelta alpha ∧ lsDelta alpha ≤ alpha / 2 ∧
      (lsDelta alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 133) := by
  obtain ⟨h0, h1, hi⟩ := lsThetaOne_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  set t := section16ThetaOne alpha (alpha / 2) 2
  have ht1 : t ≤ 1 := by linarith only [h1, ha2]
  have hd : lsDelta alpha = section16Delta t := rfl
  rw [hd]
  have h4t1 : 1 ≤ 4 / t := by rw [le_div_iff₀ h0]; linarith only [ht1]
  have h4 : 0 < t / 4 := by positivity
  have h41 : t / 4 ≤ 1 := by linarith only [ht1]
  refine ⟨by unfold section16Delta; positivity, ?_, ?_⟩
  · unfold section16Delta
    have hr : (t / 4) ^ ((11 : Real) / 2) ≤ t / 4 := by
      calc (t / 4) ^ ((11 : Real) / 2) ≤ (t / 4) ^ (1 : Real) :=
            Real.rpow_le_rpow_of_exponent_ge h4 h41 (by norm_num)
        _ = t / 4 := Real.rpow_one _
    have h2 : (2 : Real) ^ (-(37 : Real)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    calc (2 : Real) ^ (-(37 : Real)) * (t / 4) ^ ((11 : Real) / 2) ≤ 1 * (t / 4) :=
          mul_le_mul h2 hr (Real.rpow_nonneg h4.le _) zero_le_one
      _ ≤ alpha / 2 := by linarith only [h1, h0]
  · have hval : (section16Delta t)⁻¹ = (2 : Real) ^ (37 : Real) * (4 / t) ^ ((11 : Real) / 2) := by
      unfold section16Delta
      rw [mul_inv, Real.rpow_neg (by norm_num), inv_inv, ← Real.inv_rpow (by positivity), inv_div]
    rw [hval]
    set X := 2 / alpha with hX
    clear_value X
    have hX1 : 1 ≤ X := le_trans (by norm_num) hX2
    have hX0 : 0 ≤ X := le_trans (by norm_num) hX2
    have h4tX : 4 / t ≤ X ^ (2 + 3 * (2 : Nat) ^ 128) := by
      rw [div_eq_mul_inv, pow_add]
      exact mul_le_mul (const_le_pow hX2 (by norm_num)) hi (inv_pos.mpr h0).le (pow_nonneg hX0 _)
    have h37 : (2 : Real) ^ (37 : Real) ≤ X ^ 37 := by
      rw [show (37 : Real) = ((37 : Nat) : Real) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by norm_num) hX2 37
    have h6 : (4 / t) ^ ((11 : Real) / 2) ≤ (4 / t) ^ 6 := by
      rw [show (4 / t) ^ 6 = (4 / t) ^ ((6 : Nat) : Real) by rw [Real.rpow_natCast]]
      exact Real.rpow_le_rpow_of_exponent_le h4t1 (by norm_num)
    calc (2 : Real) ^ (37 : Real) * (4 / t) ^ ((11 : Real) / 2)
        ≤ X ^ 37 * (X ^ (2 + 3 * (2 : Nat) ^ 128)) ^ 6 :=
          mul_le_mul h37 (h6.trans (pow_le_pow_left₀ (by positivity) h4tX 6))
            (Real.rpow_nonneg (by positivity) _) (pow_nonneg hX0 _)
      _ = X ^ (37 + (2 + 3 * (2 : Nat) ^ 128) * 6) := by rw [← pow_mul, ← pow_add]
      _ ≤ X ^ ((2 : Nat) ^ 133) := pow_le_pow_right₀ hX1 (by norm_num)

/-- `X ≤ 2/(δ B ρ) ≤ X^(2^414)` at the spectrum scale `ρ = ρ₁/4`. -/
theorem lsSpectrum_scale {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    2 / alpha ≤ 2 / (lsDelta alpha * globalBudget alpha (alpha / 2) 2 * (lsRho1 alpha / 2 / 2)) ∧
      2 / (lsDelta alpha * globalBudget alpha (alpha / 2) 2 * (lsRho1 alpha / 2 / 2)) ≤
        (2 / alpha) ^ ((2 : Nat) ^ 414) := by
  obtain ⟨d0, da, di⟩ := lsDelta_bounds ha ha2
  obtain ⟨b0, b1, bi⟩ := lsBudget_bounds ha ha2
  obtain ⟨r0, r1, ri⟩ := lsRho1_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  have hr4 : (lsRho1 alpha / 2 / 2)⁻¹ ≤ (2 / alpha) ^ (2 + (2 : Nat) ^ 412) := by
    rw [show (lsRho1 alpha / 2 / 2)⁻¹ = 4 * (lsRho1 alpha)⁻¹ by field_simp; ring, pow_add]
    exact mul_le_mul (const_le_pow hX2 (by norm_num)) ri (inv_pos.mpr r0).le (pow_nonneg hX0 _)
  refine ⟨?_, ?_⟩
  · apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hbr : globalBudget alpha (alpha / 2) 2 * (lsRho1 alpha / 2 / 2) ≤ 1 :=
      mul_le_one₀ b1 (by positivity) (by linarith only [r1])
    have : lsDelta alpha * (globalBudget alpha (alpha / 2) 2 * (lsRho1 alpha / 2 / 2)) ≤
        alpha / 2 * 1 := mul_le_mul da hbr (by positivity) (by positivity)
    rw [mul_assoc]; linarith only [this, ha]
  · exact (two_div_prod_le_pow hX2 d0 b0 (by positivity) di bi hr4).trans
      (pow_le_pow_right₀ hX1 (by norm_num))

theorem lsEm_bounds {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3) :
    0 < lsEm (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha ∧
      (lsEm (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha)⁻¹ ≤
        (2 / alpha) ^ ((2 : Nat) ^ 546) := by
  obtain ⟨d0, da, -⟩ := lsDelta_bounds ha ha2
  obtain ⟨b0, b1, -⟩ := lsBudget_bounds ha ha2
  obtain ⟨r0, r1, -⟩ := lsRho1_bounds ha ha2
  obtain ⟨hXw, hwX⟩ := lsSpectrum_scale ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  unfold lsEm
  refine ⟨sixEb_pos (familyWidthDivisor_pos hp1) 2 _ _ _ (by positivity) (by linarith only [r1]),
    ?_⟩
  exact (sixEb_inv_le_of_scale 2 hK1 hp1 hX2 d0 (by linarith only [da, ha2]) b0 b1
    (by positivity) (by linarith only [r1]) hXw hwX hK hp).trans
    (pow_le_pow_right₀ hX1 (by norm_num))

theorem lsMExp_bounds {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3) :
    0 < lsMExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha ∧
      (lsMExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha)⁻¹ ≤
        (2 / alpha) ^ ((2 : Nat) ^ 547) := by
  obtain ⟨n0, -, ni⟩ := lsNestExp_bounds hK1 hp1 ha ha2 hK hp
  obtain ⟨e0, ei⟩ := lsEm_bounds hK1 hp1 ha ha2 hK hp
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  unfold lsMExp
  refine ⟨mul_pos n0 (by positivity), ?_⟩
  rw [mul_inv, show (lsEm (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha / 2)⁻¹ =
    2 * (lsEm (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha)⁻¹ by field_simp]
  set X := 2 / alpha with hX
  clear_value X
  have h2 : 2 * (lsEm (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha)⁻¹ ≤
      X ^ (1 + (2 : Nat) ^ 546) := by
    rw [pow_add, pow_one]
    exact mul_le_mul hX2 ei (inv_pos.mpr e0).le hX0
  exact (mul_le_pow_add (by positivity) ni h2 hX0).trans
    (pow_le_pow_right₀ hX1 (by norm_num))


/-! ### The spectrum count and the cell exponent -/

theorem lsQM_le_power {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (lsQM alpha : Real) ≤ (2 / alpha) ^ ((2 : Nat) ^ 504) := by
  obtain ⟨d0, da, -⟩ := lsDelta_bounds ha ha2
  obtain ⟨b0, b1, -⟩ := lsBudget_bounds ha ha2
  obtain ⟨r0, r1, -⟩ := lsRho1_bounds ha ha2
  obtain ⟨-, hwX⟩ := lsSpectrum_scale ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hQ := sixQb_le_power 2 d0 (by linarith only [da, ha2]) b0 b1 (by positivity : 0 < lsRho1 alpha / 2 / 2)
    (by linarith only [r1])
  have hval : singlePieceGlobalQmax sixQb (lsC alpha) alpha (alpha / 2) 2 =
      sixQb 2 (lsDelta alpha) (globalBudget alpha (alpha / 2) 2) (lsRho1 alpha / 2 / 2) := rfl
  unfold lsQM
  rw [hval]
  refine (Nat.floor_le (le_trans zero_le_one (sixQb_ge_one _ _ _ _))).trans (hQ.trans ?_)
  rw [show (2 : Nat) ^ 504 = (2 : Nat) ^ 414 * (2 : Nat) ^ 90 by norm_num, pow_mul]
  exact pow_le_pow_left₀ (by positivity) hwX _

theorem lsB_bounds {p2 : Nat} (hp2 : 0 < p2) {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hp : (p2 : Real) ≤ (2 / alpha) ^ 3) :
    0 < lsB p2 alpha ∧ lsB p2 alpha ≤ 1 ∧ (lsB p2 alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 509) := by
  have hq := lsQM_le_power ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  have h0 := familyRecExp_pos 2 p2 (lsQM alpha) hp2
  have h1 := familyRecExp_le_one 2 p2 (lsQM alpha) hp2
  unfold lsB
  refine ⟨by positivity, by linarith only [h1], ?_⟩
  have hval : (familyRecExp 2 p2 (lsQM alpha) / 2)⁻¹ =
      4 * ((p2 : Real) * ((lsQM alpha + 1 : Nat) : Real) ^ 16) := by
    unfold familyRecExp
    rw [inv_div, div_inv_eq_mul]
    push_cast; ring
  rw [hval]
  set X := 2 / alpha with hX
  clear_value X
  have hq1 : ((lsQM alpha + 1 : Nat) : Real) ≤ X ^ ((2 : Nat) ^ 504 + 1) := by
    rw [Nat.cast_succ]
    exact add_le_pow_succ hX2 hq (one_le_pow_of_two_le hX2 _)
  have h := mul_le_pow_add (pow_nonneg (Nat.cast_nonneg _) _) hp
    (show ((lsQM alpha + 1 : Nat) : Real) ^ 16 ≤ X ^ (((2 : Nat) ^ 504 + 1) * 16) by
      rw [pow_mul]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hq1 16) hX0
  have h4 := const_mul_le_pow (c := 4) (j := 2) hX2 (by norm_num) (by norm_num) (by positivity) h
  exact h4.trans (pow_le_pow_right₀ hX1 (by norm_num))

/-! ### The slice exponents and the localization exponent -/

theorem lsEth_bounds {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3) :
    0 < lsEth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha ∧
      (lsEth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha)⁻¹ ≤
        (2 / alpha) ^ ((2 : Nat) ^ 549) := by
  obtain ⟨t0, t1, ti⟩ := lsThS_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  have hr : (lsThS alpha / 2)⁻¹ ≤ (2 / alpha) ^ (1 + (2 : Nat) ^ 416) := by
    rw [show (lsThS alpha / 2)⁻¹ = 2 * (lsThS alpha)⁻¹ by field_simp, pow_add, pow_one]
    exact mul_le_mul hX2 ti (inv_pos.mpr t0).le hX0
  obtain ⟨e0, ei⟩ := sixEb_half_budget_inv_le 2 hK1 hp1 ha ha2 (by positivity)
    (by linarith only [t1]) hr hK hp
  unfold lsEth lsBudget
  exact ⟨e0, ei.trans (pow_le_pow_right₀ hX1 (by norm_num))⟩

theorem lsCS_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < lsCS alpha ∧ lsCS alpha ≤ 1 ∧ (lsCS alpha)⁻¹ ≤ (2 / alpha) ^ ((2 : Nat) ^ 508) := by
  obtain ⟨t0, t1, ti⟩ := lsThS_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hval : lsCS alpha = sixBaseC sixQb alpha 2 (lsThS alpha) := rfl
  obtain ⟨c0, c1, ci⟩ := (sixBaseC_recipPowerLB 2 ha ha2).apply_le hX1 t0 t1 ti
  rw [hval]
  exact ⟨c0, c1, ci.trans (pow_le_pow_right₀ hX1 (by norm_num))⟩

theorem lsEc_bounds {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3) :
    0 < lsEc (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha ∧
      (lsEc (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha)⁻¹ ≤
        (2 / alpha) ^ ((2 : Nat) ^ 641) := by
  obtain ⟨c0, c1, ci⟩ := lsCS_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  have hr : (lsCS alpha / 2)⁻¹ ≤ (2 / alpha) ^ (1 + (2 : Nat) ^ 508) := by
    rw [show (lsCS alpha / 2)⁻¹ = 2 * (lsCS alpha)⁻¹ by field_simp, pow_add, pow_one]
    exact mul_le_mul hX2 ci (inv_pos.mpr c0).le hX0
  obtain ⟨e0, ei⟩ := sixEb_half_budget_inv_le 2 hK1 hp1 ha ha2 (by positivity)
    (by linarith only [c1]) hr hK hp
  unfold lsEc lsBudget
  exact ⟨e0, ei.trans (pow_le_pow_right₀ hX1 (by norm_num))⟩

theorem lsF_bounds {K1 p1 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) (hp2 : 0 < p2) {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3)
    (hq : (p2 : Real) ≤ (2 / alpha) ^ 3) :
    0 < lsF (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha ∧
      (lsF (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha)⁻¹ ≤
        (2 / alpha) ^ ((2 : Nat) ^ 642) := by
  obtain ⟨m0, mi⟩ := lsMExp_bounds hK1 hp1 ha ha2 hK hp
  obtain ⟨b0, -, bi⟩ := lsB_bounds hp2 ha ha2 hq
  obtain ⟨t0, ti⟩ := lsEth_bounds hK1 hp1 ha ha2 hK hp
  obtain ⟨c0, ci⟩ := lsEc_bounds hK1 hp1 ha ha2 hK hp
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  unfold lsF
  set M := lsMExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha
  set B := lsB p2 alpha
  set T := lsEth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha
  set C := lsEc (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha
  set X := 2 / alpha with hX
  clear_value M B T C X
  refine ⟨by positivity, ?_⟩
  rw [show (M * (B * (T * C) / 2))⁻¹ = M⁻¹ * (2 * (B⁻¹ * (T⁻¹ * C⁻¹))) by field_simp]
  have hTC := mul_le_pow_add (inv_pos.mpr c0).le ti ci hX0
  have hBTC := mul_le_pow_add (by positivity) bi hTC hX0
  have h2 : 2 * (B⁻¹ * (T⁻¹ * C⁻¹)) ≤ X ^ (1 + ((2 : Nat) ^ 509 + ((2 : Nat) ^ 549 + (2 : Nat) ^ 641))) := by
    rw [pow_add, pow_one]
    exact mul_le_mul hX2 hBTC (by positivity) hX0
  exact (mul_le_pow_add (by positivity) mi h2 hX0).trans
    (pow_le_pow_right₀ hX1 (by norm_num))

/-- **The localization exponent is polynomial**: `lsE⁻¹ ≤ (2/α)^(2^643)`. -/
theorem lsE_inv_le_power {K1 p1 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) (hp2 : 0 < p2)
    {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3)
    (hq : (p2 : Real) ≤ (2 / alpha) ^ 3) :
    0 < lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha ∧
      (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha)⁻¹ ≤
        (2 / alpha) ^ ((2 : Nat) ^ 643) := by
  obtain ⟨f0, fi⟩ := lsF_bounds hK1 hp1 hp2 ha ha2 hK hp hq
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  unfold lsE
  set F := lsF (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha
  set X := 2 / alpha with hX
  clear_value F X
  refine ⟨by positivity, ?_⟩
  rw [show (F / 8)⁻¹ = 8 * F⁻¹ by field_simp]
  exact (const_mul_le_pow (j := 3) hX2 (by norm_num) (by norm_num) (inv_pos.mpr f0).le fi).trans
    (pow_le_pow_right₀ hX1 (by norm_num))
end LeanProofs.GowersSzemeredi

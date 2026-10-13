import GowersSzemeredi.Proofs18GenericStep
import GowersSzemeredi.Proofs18ExponentialCalculus

/-! Power-of-two envelopes for the single-piece step in any dimension
(Notes L.7a, F3c).

Every quantity of the step is bounded by `X^(2^μ)` (densities, exponents) or
`exp(X^(2^μ))` (thresholds), with `X = 2/α`. Products and powers then add
log-degrees, so the final comparison is arithmetic on the exponents `μ`.
* The calculus: `pw_*` for powers, `ex_*` for single exponentials.
* The fixed parameters of dimension `k`:
  - `θ₁⁻¹ ≤ X^(2^(2^(k+5)+2))`, `θ₂⁻¹ ≤ X^(2^(2^(k+5)+6))`;
  - the budget, `θ₂/2` and `δ` above `X^(-2^(2^(k+5)+7))` (`fixDeg`);
  - the Bohr radius `ζ⁻¹ ≤ exp(X^(2^(2^(k+6)+1)))`;
  - Lemma 15.6's threshold `≤ X^(2^(2^(k+4)+3k+16))`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The power calculus -/

section Calculus

variable {X : Real}

theorem one_le_pw (hX : 2 ≤ X) (a : Nat) : 1 ≤ X ^ (2 ^ a) :=
  one_le_pow₀ (le_trans (by norm_num) hX)

theorem pw_mono (hX : 2 ≤ X) {x : Real} {a b : Nat} (h : x ≤ X ^ (2 ^ a)) (hab : a ≤ b) :
    x ≤ X ^ (2 ^ b) :=
  h.trans (pow_le_pow_right₀ (le_trans (by norm_num) hX) (Nat.pow_le_pow_right (by norm_num) hab))

theorem pw_mul (hX : 2 ≤ X) {x y : Real} {a : Nat} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ X ^ (2 ^ a)) (hy : y ≤ X ^ (2 ^ a)) : x * y ≤ X ^ (2 ^ (a + 1)) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  calc x * y ≤ X ^ (2 ^ a) * X ^ (2 ^ a) := mul_le_mul hx hy hy0 (pow_nonneg hX0 _)
    _ = X ^ (2 ^ (a + 1)) := by rw [← pow_add, pow_succ, mul_two]

theorem pw_mul' (hX : 2 ≤ X) {x y : Real} {a b : Nat} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ X ^ (2 ^ a)) (hy : y ≤ X ^ (2 ^ b)) : x * y ≤ X ^ (2 ^ (max a b + 1)) :=
  pw_mul hX hx0 hy0 (pw_mono hX hx (le_max_left a b)) (pw_mono hX hy (le_max_right a b))

theorem pw_pow (hX : 2 ≤ X) {x : Real} {a c n : Nat} (hx0 : 0 ≤ x) (hx : x ≤ X ^ (2 ^ a))
    (hn : n ≤ 2 ^ c) : x ^ n ≤ X ^ (2 ^ (a + c)) := by
  calc x ^ n ≤ (X ^ (2 ^ a)) ^ n := pow_le_pow_left₀ hx0 hx n
    _ ≤ (X ^ (2 ^ a)) ^ (2 ^ c) := pow_le_pow_right₀ (one_le_pw hX a) hn
    _ = X ^ (2 ^ (a + c)) := by rw [← pow_mul, ← pow_add]

theorem pw_const (hX : 2 ≤ X) {c : Real} {a : Nat} (hc : c ≤ 2 ^ (2 ^ a)) : c ≤ X ^ (2 ^ a) :=
  hc.trans (pow_le_pow_left₀ (by norm_num) hX _)

theorem pw_X (hX : 2 ≤ X) (a : Nat) : X ≤ X ^ (2 ^ a) := by
  calc X = X ^ 1 := (pow_one X).symm
    _ ≤ X ^ (2 ^ a) := pow_le_pow_right₀ (le_trans (by norm_num) hX) (Nat.one_le_two_pow)

/-- `X^n ≤ X^(2^a)` once `n ≤ 2^a`. -/
theorem pw_natpow (hX : 2 ≤ X) {n a : Nat} (hn : n ≤ 2 ^ a) : X ^ n ≤ X ^ (2 ^ a) :=
  pow_le_pow_right₀ (le_trans (by norm_num) hX) hn

theorem ex_of_pw {x : Real} {a : Nat} (h : x ≤ X ^ (2 ^ a)) : x ≤ Real.exp (X ^ (2 ^ a)) :=
  le_exp_pow_of_le_pow h

theorem ex_mono (hX : 2 ≤ X) {x : Real} {a b : Nat} (h : x ≤ Real.exp (X ^ (2 ^ a)))
    (hab : a ≤ b) : x ≤ Real.exp (X ^ (2 ^ b)) :=
  h.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (le_trans (by norm_num) hX)
    (Nat.pow_le_pow_right (by norm_num) hab)))

theorem ex_mul (hX : 2 ≤ X) {x y : Real} {a : Nat} (hy0 : 0 ≤ y)
    (hx : x ≤ Real.exp (X ^ (2 ^ a))) (hy : y ≤ Real.exp (X ^ (2 ^ a))) :
    x * y ≤ Real.exp (X ^ (2 ^ (a + 1))) := by
  have h := exp_mul_le hX hy0 hx hy
  refine h.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (le_trans (by norm_num) hX) ?_))
  rw [pow_succ]; have := Nat.one_le_two_pow (n := a); omega

theorem ex_mul' (hX : 2 ≤ X) {x y : Real} {a b : Nat} (hy0 : 0 ≤ y)
    (hx : x ≤ Real.exp (X ^ (2 ^ a))) (hy : y ≤ Real.exp (X ^ (2 ^ b))) :
    x * y ≤ Real.exp (X ^ (2 ^ (max a b + 1))) :=
  ex_mul hX hy0 (ex_mono hX hx (le_max_left a b)) (ex_mono hX hy (le_max_right a b))

/-- `b^e ≤ exp(X^(2^(max a c + 1)))` for `1 ≤ b ≤ exp(X^(2^a))` and `0 ≤ e ≤ X^(2^c)`. -/
theorem ex_rpow (hX : 2 ≤ X) {b e : Real} {a c : Nat} (hb1 : 1 ≤ b)
    (hb : b ≤ Real.exp (X ^ (2 ^ a))) (he0 : 0 ≤ e) (he : e ≤ X ^ (2 ^ c)) :
    b ^ e ≤ Real.exp (X ^ (2 ^ (max a c + 1))) := by
  have h := rpow_le_exp_pow hX hb1 hb he0 he
  refine h.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (le_trans (by norm_num) hX) ?_))
  have h1 : 2 ^ a ≤ 2 ^ max a c := Nat.pow_le_pow_right (by norm_num) (le_max_left a c)
  have h2 : 2 ^ c ≤ 2 ^ max a c := Nat.pow_le_pow_right (by norm_num) (le_max_right a c)
  rw [pow_succ]; omega

end Calculus

/-! ### The fixed parameters of dimension `k` -/

section Fixed

variable {alpha : Real}

theorem two_div_ge_two (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) : 2 ≤ 2 / alpha := by
  have := two_div_alpha_ge_four ha ha2; linarith

/-- `(α(α/2)/4)⁻¹ = 8/α² ≤ X³`. -/
theorem quarter_base_inv_le (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (alpha * (alpha / 2) / 4)⁻¹ ≤ (2 / alpha) ^ 3 := by
  have ha1 : alpha ≤ 1 := by linarith
  have e1 : (alpha * (alpha / 2) / 4)⁻¹ = 8 / alpha ^ 2 := by field_simp; ring
  have e2 : (2 / alpha) ^ 3 = 8 / alpha ^ 3 := by rw [div_pow]; norm_num
  rw [e1, e2]
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos ha 3)
    (pow_le_pow_of_le_one ha.le ha1 (by norm_num))

theorem thetaOne_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaOne alpha (alpha / 2) k ∧ section16ThetaOne alpha (alpha / 2) k ≤ 1 ∧
      (section16ThetaOne alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2)) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨h0, h1, -, -⟩ := section16_theta_delta_bounds k ha ha1 (half_pos ha) (by linarith)
  have hX := two_div_ge_two ha ha2
  have hq0 : 0 < alpha * (alpha / 2) / 4 := by positivity
  refine ⟨h0, h1, ?_⟩
  unfold section16ThetaOne
  rw [← inv_pow]
  have hq := quarter_base_inv_le ha ha2
  calc (alpha * (alpha / 2) / 4)⁻¹ ^ (2 ^ 2 ^ (k + 5)) ≤ ((2 / alpha) ^ 3) ^ (2 ^ 2 ^ (k + 5)) :=
        pow_le_pow_left₀ (inv_pos.mpr hq0).le hq _
    _ = (2 / alpha) ^ (3 * 2 ^ 2 ^ (k + 5)) := by rw [← pow_mul]
    _ ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2)) := by
        apply pow_le_pow_right₀ (le_trans (by norm_num) hX)
        have h : 2 ^ (2 ^ (k + 5) + 2) = 2 ^ (2 ^ (k + 5)) * 4 := by rw [pow_add]; norm_num
        omega

theorem thetaTwo_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaTwo (section16ThetaOne alpha (alpha / 2) k) ∧
      section16ThetaTwo (section16ThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16ThetaTwo (section16ThetaOne alpha (alpha / 2) k))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 6)) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) k ha ha1 (half_pos ha)
    (by linarith)
  obtain ⟨t0, -, ti⟩ := thetaOne_gen_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  have hX0 : (0 : Real) ≤ 2 / alpha := by linarith
  refine ⟨h0, h1, ?_⟩
  unfold section16ThetaTwo
  have h32 : ((2 : Real) ^ (-(32 : Real)))⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2)) := by
    rw [Real.rpow_neg (by norm_num), inv_inv,
      show (32 : Real) = ((32 : Nat) : Real) by norm_num, Real.rpow_natCast]
    refine (pow_le_pow_left₀ (by norm_num) hX 32).trans (pw_natpow hX ?_)
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (2 ^ (k + 5) + 2) := Nat.pow_le_pow_right (by norm_num) (by
          have : 5 ≤ 2 ^ (k + 5) := by
            calc 5 ≤ 2 ^ 5 := by norm_num
              _ ≤ 2 ^ (k + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega)
  have h8 : ((section16ThetaOne alpha (alpha / 2) k) ^ 8)⁻¹ ≤
      (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2 + 3)) := by
    rw [← inv_pow]
    exact pw_pow hX (inv_pos.mpr t0).le ti (by norm_num)
  rw [mul_inv]
  have := pw_mul hX (by positivity) (by positivity) (pw_mono hX h32 (by omega)) h8
  exact pw_mono hX this (by omega)

/-- The log-degree of the fixed parameters of dimension `k`. -/
def fixDeg (k : Nat) : Nat := 2 ^ (k + 5) + 7

theorem budget_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudget alpha (alpha / 2) k ∧ globalBudget alpha (alpha / 2) k ≤ 1 ∧
      (globalBudget alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  obtain ⟨h0, h1, hi⟩ := thetaTwo_gen_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  have hden : (1 : Real) ≤ 2 * (2 ^ k + 1) := by
    have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  unfold globalBudget
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · rw [inv_div, div_eq_mul_inv]
    have hc : 2 * ((2 : Real) ^ k + 1) ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 6)) := by
      have h1 : 2 * ((2 : Real) ^ k + 1) ≤ 2 ^ (k + 2) := by
        have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        rw [pow_add]; norm_num; linarith
      refine h1.trans ((pow_le_pow_left₀ (by norm_num) hX _).trans (pw_natpow hX ?_))
      calc k + 2 ≤ 2 ^ (k + 2) := Nat.lt_two_pow_self.le
        _ ≤ 2 ^ (2 ^ (k + 5) + 6) := Nat.pow_le_pow_right (by norm_num) (by
            have : k + 2 ≤ 2 ^ (k + 5) := by
              have := Nat.lt_two_pow_self (n := k + 5); omega
            omega)
    have := pw_mul hX (by positivity) (inv_pos.mpr h0).le hc hi
    unfold fixDeg; exact this

theorem T2_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalTheta2 alpha (alpha / 2) k ∧ globalTheta2 alpha (alpha / 2) k ≤ 1 ∧
      (globalTheta2 alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  obtain ⟨h0, h1, hi⟩ := thetaTwo_gen_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  unfold globalTheta2
  refine ⟨by positivity, by linarith, ?_⟩
  rw [inv_div, div_eq_mul_inv]
  have h2 : (2 : Real) ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 6)) :=
    hX.trans (pw_X hX _)
  have := pw_mul hX (by norm_num) (inv_pos.mpr h0).le h2 hi
  unfold fixDeg
  exact pw_mono hX this (by omega)

theorem delta_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Delta (section16ThetaOne alpha (alpha / 2) k) ∧
      section16Delta (section16ThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16Delta (section16ThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨-, -, d0, d1⟩ := section16_theta_delta_bounds k ha ha1 (half_pos ha) (by linarith)
  obtain ⟨t0, t1, ti⟩ := thetaOne_gen_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  refine ⟨d0, d1, ?_⟩
  set t := section16ThetaOne alpha (alpha / 2) k with htdef
  have hq0 : 0 < t / 4 := by positivity
  have hq1 : t / 4 ≤ 1 := by linarith
  -- `(t/4)^(11/2) ≥ (t/4)^6`
  have h6 : (t / 4) ^ (6 : Nat) ≤ (t / 4) ^ ((11 : Real) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (by norm_num)
  unfold section16Delta
  have h37 : ((2 : Real) ^ (-(37 : Real)))⁻¹ = 2 ^ (37 : Nat) := by
    rw [Real.rpow_neg (by norm_num), inv_inv,
      show (37 : Real) = ((37 : Nat) : Real) by norm_num, Real.rpow_natCast]
  rw [mul_inv, h37]
  have hinv6 : ((t / 4) ^ ((11 : Real) / 2))⁻¹ ≤ ((t / 4) ^ (6 : Nat))⁻¹ :=
    inv_anti₀ (pow_pos hq0 _) h6
  have hq : ((t / 4) ^ (6 : Nat))⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2 + 1 + 3)) := by
    rw [← inv_pow, inv_div]
    have h4t : 4 / t ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2 + 1)) := by
      rw [div_eq_mul_inv]
      have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2)) :=
        (show (4 : Real) ≤ 2 ^ 2 by norm_num).trans
          ((pow_le_pow_left₀ (by norm_num) hX 2).trans (pw_natpow hX (by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (2 ^ (k + 5) + 2) := Nat.pow_le_pow_right (by norm_num) (by
                  have := Nat.one_le_two_pow (n := k + 5); omega))))
      exact pw_mul hX (by norm_num) (inv_pos.mpr t0).le h4 ti
    exact pw_pow hX (by positivity) h4t (by norm_num)
  have h2 : (2 : Real) ^ (37 : Nat) ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2 + 1 + 3)) :=
    (pow_le_pow_left₀ (by norm_num) hX 37).trans (pw_natpow hX (by
      calc 37 ≤ 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 ^ (k + 5) + 2 + 1 + 3) := Nat.pow_le_pow_right (by norm_num) (by
            have := Nat.one_le_two_pow (n := k + 5); omega)))
  have := pw_mul hX (by positivity) (by positivity) h2 (hinv6.trans hq)
  unfold fixDeg
  exact pw_mono hX this (by omega)

/-- **The Bohr radius**: `ζ⁻¹ = 2^(multipleS) ≤ exp(X^(2^(2^(k+6)+1)))`. -/
theorem zeta_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Zeta alpha (alpha / 2) k ∧
      (section16Zeta alpha (alpha / 2) k)⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ (2 ^ (k + 6) + 1))) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨hz, -⟩ := section16Zeta_pos_le_half k ha ha1 (half_pos ha) (by linarith)
  have hX := two_div_ge_two ha ha2
  refine ⟨hz, ?_⟩
  have hS : multipleS alpha (alpha / 2) k = ((2 / alpha) ^ 2) ^ (2 ^ 2 ^ (k + 6)) := by
    unfold multipleS
    congr 1
    field_simp
  have hS0 : 0 ≤ multipleS alpha (alpha / 2) k := by rw [hS]; positivity
  unfold section16Zeta
  rw [Real.rpow_neg (by norm_num), inv_inv]
  refine (two_rpow_le_exp hS0).trans (Real.exp_le_exp.mpr ?_)
  rw [hS, ← pow_mul]
  apply pow_le_pow_right₀ (le_trans (by norm_num) hX)
  exact le_of_eq (by ring)

end Fixed

end LeanProofs.GowersSzemeredi

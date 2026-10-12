import GowersSzemeredi.Proofs18GenericThresholds
import GowersSzemeredi.Proofs18DoubleExponentialBounds
import GowersSzemeredi.Proofs18FejerIterationParameters
import GowersSzemeredi.Proofs05RefinementConstantBounds

/-! Discrepancy bounds in every degree, with power-of-two envelopes
(Notes L.7a, F3d).

`EnvBound d μ`: for every `α ∈ (0, 1/2]` there is a degree-`d` discrepancy
bound `FunctionDiscrepancyBound d α β σ T` with
`β⁻¹ ≤ X^(2^μ)`, `σ⁻¹ ≤ exp(X^(2^μ))` and `T ≤ exp(exp(X^(2^μ)))`, `X = 2/α`.
* `envBound_three`: degree three at `μ = 62`, from the Fejér cubic bound.
* `envBound_step`: the single-piece step in dimension `k` takes
  `EnvBound (k+1) μ` to `EnvBound (k+2) (envStep k μD μ₀ μK μ)`, given
  uniform covers in dimensions `≤ k` and the recurrence profile in
  dimension `k`.
* The fixed constants: `polyPartConst_le`, `s5_one_le`.

The step costs `envStep − μ ≈ densDeg k μD μ₀`, dominated by the nest:
`(μD + 1)·(2^k − 1)` (Notes L.7a). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Degree-`d` discrepancy bounds with power-of-two envelopes.** -/
def EnvBound (d μ : Nat) : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ beta sigma T : Real, FunctionDiscrepancyBound d alpha beta sigma T ∧
      0 < beta ∧ beta ≤ 1 ∧ 0 < sigma ∧ sigma ≤ 16 ∧
      beta⁻¹ ≤ (2 / alpha) ^ (2 ^ μ) ∧ sigma⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ μ)) ∧
      T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ μ)))

theorem EnvBound.mono {d μ μ' : Nat} (h : EnvBound d μ) (hμ : μ ≤ μ') : EnvBound d μ' := by
  intro alpha ha ha2
  obtain ⟨b, s, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := h alpha ha ha2
  have hX := two_div_ge_two ha ha2
  refine ⟨b, s, T, hB, b0, b1, s0, s16, pw_mono hX bi hμ, ex_mono hX si hμ, ?_⟩
  refine Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
    (pow_le_pow_right₀ (le_trans (by norm_num) hX) (Nat.pow_le_pow_right (by norm_num) hμ))))

/-- **Degree three**, from the Fejér cubic bound. -/
theorem envBound_three : EnvBound 3 62 := by
  intro alpha ha ha2
  have ha1 : alpha ≤ 1 := by linarith
  have hX := two_div_ge_two ha ha2
  have hb0 := fejerCubicDiscrepancyParameter_pos ha
  have hb1 := fejerCubicDiscrepancyParameter_le_one ha ha1
  have hs0 := fejerCubicDiscrepancyExponent_pos ha ha1
  refine ⟨fejerCubicDiscrepancyParameter alpha, min (fejerCubicDiscrepancyExponent alpha) 16,
    fejerCubicInverseThreshold alpha,
    (fejer_cubic_function_discrepancy_bound ha ha1).mono le_rfl le_rfl (min_le_left _ _) le_rfl,
    hb0, hb1, lt_min hs0 (by norm_num), min_le_right _ _, ?_, ?_, ?_⟩
  · have h8 : (fejerCubicDiscrepancyParameter alpha)⁻¹ ≤ (fejerCubicDiscrepancyParameter alpha / 8)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith only [hb0])
    have hg := fejer_cubic_gain_inv_le_power ha ha1
    exact (h8.trans hg).trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  · have hs := fejerCubicDiscrepancyExponent_inv_le_exp ha ha1
    rcases min_choice (fejerCubicDiscrepancyExponent alpha) 16 with h | h
    · rw [h]; exact ex_mono hX hs (by norm_num)
    · rw [h]
      exact (show ((16 : Real))⁻¹ ≤ 1 by norm_num).trans (Real.one_le_exp (by positivity))
  · exact (fejerCubicInverseThreshold_le_double_exp ha ha1).trans (le_of_eq rfl)

/-! ### The fixed constants -/

theorem polyPartConst_le (d : Nat) : polynomialPartitionConstant d ≤ 2 ^ (4 * (d + 1) ^ 2) := by
  unfold polynomialPartitionConstant
  have hf : d.factorial ≤ 2 ^ (d * d) := by
    calc d.factorial ≤ d ^ d := Nat.factorial_le_pow d
      _ ≤ (2 ^ d) ^ d := Nat.pow_le_pow_left Nat.lt_two_pow_self.le d
      _ = 2 ^ (d * d) := by rw [← pow_mul]
  have hf2 : d.factorial ^ 2 ≤ 2 ^ (2 * (d * d)) := by
    calc d.factorial ^ 2 ≤ (2 ^ (d * d)) ^ 2 := Nat.pow_le_pow_left hf 2
      _ = 2 ^ (2 * (d * d)) := by rw [← pow_mul]; ring_nf
  calc d.factorial ^ 2 * 2 ^ ((d + 1) ^ 2) ≤ 2 ^ (2 * (d * d)) * 2 ^ ((d + 1) ^ 2) :=
        Nat.mul_le_mul_right _ hf2
    _ = 2 ^ (2 * (d * d) + (d + 1) ^ 2) := by rw [← pow_add]
    _ ≤ 2 ^ (4 * (d + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- The refinement constant at scale one in degree `d ≥ 1`. -/
theorem s5_one_le {d : Nat} (hd : 1 ≤ d) :
    section5LocalRefinementConstant d 1 ≤ (2 : Real) ^ (2 ^ (40 * d ^ 3 + 2)) := by
  have hK := polyPartConst_le d
  set K := polynomialPartitionConstant d
  have hKe : 4 * K ≤ 2 ^ (40 * d ^ 3 + 1) := by
    have h1 : 4 * K ≤ 2 ^ (4 * (d + 1) ^ 2 + 2) := by
      rw [pow_add]; nlinarith
    refine h1.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    have hd3 : d ≤ d ^ 3 := by
      calc d = d ^ 1 := (pow_one d).symm
        _ ≤ d ^ 3 := Nat.pow_le_pow_right hd (by norm_num)
    have hd2 : d * d ≤ d ^ 3 := by
      calc d * d = d ^ 2 := by ring
        _ ≤ d ^ 3 := Nat.pow_le_pow_right hd (by norm_num)
    nlinarith
  set W := (2 : Real) ^ (2 ^ (40 * d ^ 3 + 1))
  have hW : (polynomialPartitionThreshold d : Real) ≤ W := by
    simp only [polynomialPartitionThreshold, weylThreshold, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, show 2 ^ (40 * d ^ 3) * 2 = 2 ^ (40 * d ^ 3 + 1) by ring]
  have h16 : (16 : Real) ^ K ≤ W := by
    calc (16 : Real) ^ K = 2 ^ (4 * K) := by
          rw [show (16 : Real) = 2 ^ (4 : Nat) by norm_num, ← pow_mul]
      _ ≤ W := pow_le_pow_right₀ (by norm_num) hKe
  have hpi : (4 * Real.pi / 1) ^ K ≤ W := by
    refine le_trans ?_ h16
    apply pow_le_pow_left₀ (by positivity)
    have hp := Real.pi_lt_four
    linarith only [hp]
  have hmax : section5LocalRefinementConstant d 1 ≤ W + 4 := by
    unfold section5LocalRefinementConstant
    exact add_le_add (max_le (max_le hW hpi)
      ((pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 4) (by norm_num : (4 : Real) ≤ 16) _).trans
        h16)) le_rfl
  have h4 : (4 : Real) ≤ W := by
    calc (4 : Real) = 2 ^ (2 : Nat) := by norm_num
      _ ≤ W := pow_le_pow_right₀ (by norm_num) (by
          have := Nat.lt_two_pow_self (n := 40 * d ^ 3 + 1); omega)
  calc section5LocalRefinementConstant d 1 ≤ W + 4 := hmax
    _ ≤ W + W := add_le_add le_rfl h4
    _ = (2 : Real) ^ (2 ^ (40 * d ^ 3 + 1) + 1) := by rw [pow_succ, ← two_mul, mul_comm]
    _ ≤ (2 : Real) ^ (2 ^ (40 * d ^ 3 + 2)) := pow_le_pow_right₀ (by norm_num) (by
        rw [show 40 * d ^ 3 + 2 = (40 * d ^ 3 + 1) + 1 by ring, pow_succ]
        have := Nat.one_le_two_pow (n := 40 * d ^ 3 + 1); omega)

/-! ### Double exponentials -/

section DoubleExp

variable {X : Real}

/-- `exp(exp(X^(2^a)))` is monotone in `a`. -/
theorem dex_mono (hX : 2 ≤ X) {x : Real} {a b : Nat}
    (h : x ≤ Real.exp (Real.exp (X ^ (2 ^ a)))) (hab : a ≤ b) :
    x ≤ Real.exp (Real.exp (X ^ (2 ^ b))) :=
  h.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (pow_le_pow_right₀ (le_trans (by norm_num) hX)
    (Nat.pow_le_pow_right (by norm_num) hab))))

/-- `1 + X^(2^a) + X^(2^b) ≤ X^(2^(max a b + 2))`. -/
theorem one_add_pw_add_pw_le (hX : 2 ≤ X) (a b : Nat) :
    1 + X ^ (2 ^ a) + X ^ (2 ^ b) ≤ X ^ (2 ^ (max a b + 2)) := by
  have ha := pw_mono hX (le_refl (X ^ (2 ^ a))) (le_max_left a b)
  have hb := pw_mono hX (le_refl (X ^ (2 ^ b))) (le_max_right a b)
  have hY : 2 ≤ X ^ (2 ^ max a b) := hX.trans (pw_X hX _)
  have hY0 : 0 ≤ X ^ (2 ^ max a b) := by linarith
  have h1 := pw_mul hX hY0 hY0 (le_refl (X ^ (2 ^ max a b))) (le_refl _)
  have h2 := pw_mul hX (mul_nonneg hY0 hY0) (mul_nonneg hY0 hY0) h1 h1
  have h3 : 1 + X ^ (2 ^ a) + X ^ (2 ^ b) ≤
      (X ^ (2 ^ max a b) * X ^ (2 ^ max a b)) * (X ^ (2 ^ max a b) * X ^ (2 ^ max a b)) := by
    have key : ∀ Y : Real, 2 ≤ Y → 1 + Y + Y ≤ Y * Y * (Y * Y) := by
      intro Y hY
      have h4 : 4 ≤ Y * Y := by nlinarith
      have h16 : 4 * (Y * Y) ≤ Y * Y * (Y * Y) := mul_le_mul_of_nonneg_right h4 (by positivity)
      nlinarith
    have := key _ hY
    linarith
  exact h3.trans h2

end DoubleExp

/-! ### The pieces of the step -/

/-- The input scale: `(2/y)^(2^μ) ≤ X^(2^(dd+1+μ))` when `y⁻¹ ≤ X^(2^dd)`. -/
theorem input_scale_le {alpha y : Real} {dd μ : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hy0 : 0 < y) (hyi : y⁻¹ ≤ (2 / alpha) ^ (2 ^ dd)) :
    2 / y ≤ (2 / alpha) ^ (2 ^ (dd + 1)) ∧
      (2 / y) ^ (2 ^ μ) ≤ (2 / alpha) ^ (2 ^ (dd + 1 + μ)) := by
  have hX := two_div_ge_two ha ha2
  have h2 : 2 / y ≤ (2 / alpha) ^ (2 ^ (dd + 1)) := by
    rw [div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hy0).le (hX.trans (pw_X hX _)) hyi
  exact ⟨h2, pw_pow hX (by positivity) h2 le_rfl⟩

theorem polyPartConst_pos (d : Nat) : 0 < polynomialPartitionConstant d := by
  unfold polynomialPartitionConstant; positivity

/-- The new exponent `σ′ = e·(σ/16)/(2P)`. -/
theorem sigma_step {d : Nat} {e s : Real} (he0 : 0 < e) (he : e ≤ 1 / 2) (hs0 : 0 < s)
    (hs16 : s ≤ 16) :
    0 < inverseStepExponent d e s ∧ inverseStepExponent d e s ≤ 16 ∧
      (inverseStepExponent d e s)⁻¹ =
        32 * (polynomialPartitionConstant (d + 1) : Real) * e⁻¹ * s⁻¹ := by
  have hP : (1 : Real) ≤ polynomialPartitionConstant (d + 1) := by
    exact_mod_cast polyPartConst_pos (d + 1)
  unfold inverseStepExponent phaseInverseExponent
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have : e * (s / 16) ≤ 1 := by
      have h1 : s / 16 ≤ 1 := by linarith
      calc e * (s / 16) ≤ 1 * 1 := mul_le_mul (by linarith) h1 (by positivity) zero_le_one
        _ = 1 := one_mul 1
    nlinarith
  · field_simp; ring

/-- **The short-localization threshold.** -/
theorem short_thr_le {X : Real} (hX : 2 ≤ X) {d : Nat} {e c T Tl : Real} {m a t j : Nat}
    (he0 : 0 < e) (heI : e⁻¹ ≤ X ^ (2 ^ a)) (hc0 : 0 ≤ c) (hc : c ≤ 2 ^ (2 ^ j))
    (hT : T ≤ Real.exp (Real.exp (X ^ (2 ^ m)))) (hTl : Tl ≤ Real.exp (X ^ (2 ^ t)))
    (hd : (((d + 2 : Nat) : Real) ^ (2 : Nat)) ≤ 2 ^ (2 ^ j)) :
    shortLocalizationThreshold d e c T Tl ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max m j) (max a t) + 2)))) := by
  set M := max (max m j) (max a t)
  have hX0 : (0 : Real) ≤ X := by linarith
  have hcE : c ≤ Real.exp (Real.exp (X ^ (2 ^ max m j))) :=
    le_exp_exp_of_le_exp (ex_of_pw (pw_mono hX (pw_const hX hc) (le_max_right _ _)))
  have hTE : T ≤ Real.exp (Real.exp (X ^ (2 ^ max m j))) := dex_mono hX hT (le_max_left _ _)
  have h2E : (2 : Real) ≤ Real.exp (Real.exp (X ^ (2 ^ max m j))) :=
    le_exp_exp_of_le_exp (ex_of_pw (hX.trans (pw_X hX _)))
  have hC : c * max 2 T ≤ Real.exp (Real.exp (X ^ (2 ^ max m j) + 1)) :=
    (mul_le_mul hcE (max_le h2E hTE) (le_trans zero_le_two (le_max_left _ _))
      (Real.exp_pos _).le).trans exp_exp_sq_le
  have hP := positivePowerThreshold_one_le_double_exp he0.le hC (ex_of_pw heI)
  have hsum : X ^ (2 ^ max m j) + 1 + X ^ (2 ^ a) ≤ X ^ (2 ^ (M + 2)) := by
    have h := one_add_pw_add_pw_le hX (max m j) a
    have hle : max (max m j) a + 2 ≤ M + 2 := by
      have : max (max m j) a ≤ M := max_le (le_max_left _ _) ((le_max_left a t).trans (le_max_right _ _))
      omega
    refine le_trans (by linarith) (h.trans (pow_le_pow_right₀ (le_trans (by norm_num) hX)
      (Nat.pow_le_pow_right (by norm_num) hle)))
  unfold shortLocalizationThreshold
  apply max_le
  · exact le_exp_exp_of_le_exp (ex_mono hX hTl (by omega))
  apply max_le
  · exact le_exp_exp_of_le_exp (ex_of_pw (pw_mono hX (pw_const hX hd) (by omega)))
  · exact hP.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hsum))

/-- `a + b ≤ X^(2^(m+1))` for `a, b ≤ X^(2^m)`. -/
theorem pw_add {X : Real} (hX : 2 ≤ X) {a b : Real} {m : Nat} (ha : a ≤ X ^ (2 ^ m))
    (hb : b ≤ X ^ (2 ^ m)) : a + b ≤ X ^ (2 ^ (m + 1)) := by
  have hY : 2 ≤ X ^ (2 ^ m) := hX.trans (pw_X hX _)
  have h := pw_mul hX (by linarith) (by linarith) (le_refl (X ^ (2 ^ m))) (le_refl (X ^ (2 ^ m)))
  nlinarith

/-- A small natural number `c ≤ 6(k+3)` is below `X^(2^(k+3))`. -/
theorem small_nat_le_pw {X : Real} (hX : 2 ≤ X) {k c : Nat} (hc : c ≤ 6 * (k + 3)) :
    (c : Real) ≤ X ^ (2 ^ (k + 3)) := by
  have hk := Nat.lt_two_pow_self (n := k)
  have h1 : c ≤ 2 ^ (k + 6) := by
    have : 2 ^ (k + 6) = 64 * 2 ^ k := by rw [pow_add]; ring
    omega
  have h2 : k + 6 ≤ 2 ^ (k + 3) := by
    have : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
    omega
  calc (c : Real) ≤ 2 ^ (k + 6) := by exact_mod_cast h1
    _ ≤ X ^ (k + 6) := pow_le_pow_left₀ (by norm_num) hX _
    _ ≤ X ^ (2 ^ (k + 3)) := pw_natpow hX h2

/-- **The phase-refinement threshold.** -/
theorem inv_thr_le {X : Real} (hX : 2 ≤ X) {k : Nat} {η β e σ : Real} {M s : Nat}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hηi : η⁻¹ ≤ X ^ (2 ^ M)) (hβi : β⁻¹ ≤ X ^ (2 ^ M)) (hs0 : 0 < σ) (hs16 : σ ≤ 16)
    (hσ'0 : 0 < inverseStepExponent (k + 1) e σ)
    (hσ' : (inverseStepExponent (k + 1) e σ)⁻¹ ≤ Real.exp (X ^ (2 ^ s))) :
    inverseStepThreshold (k + 1) η β e (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max (40 * (k + 2) ^ 3 + 1090)
        (M + 4 * (k + 3) ^ 2 + 10)) s + 1)))) := by
  set Q := max (40 * (k + 2) ^ 3 + 1090) (M + 4 * (k + 3) ^ 2 + 10) with hQdef
  -- the refinement constant at `b = ηβ/2`
  have hb : 0 < η * β / 2 := by positivity
  have hbi : (η * β / 2)⁻¹ ≤ X ^ (2 ^ (M + 2)) := by
    rw [show (η * β / 2)⁻¹ = 2 * (η⁻¹ * β⁻¹) by field_simp]
    have h1 := pw_mul hX (inv_pos.mpr hη0).le (inv_pos.mpr hβ0).le hηi hβi
    exact pw_mul' hX (by norm_num) (by positivity) (hX.trans (pw_X hX M)) h1 |>.trans
      (pw_mono hX le_rfl (by omega))
  have hb1 : 1 ≤ (η * β / 2)⁻¹ := by
    rw [one_le_inv₀ hb]
    have : η * β ≤ 1 := mul_le_one₀ hη1 hβ0.le hβ1
    linarith
  have hscaled := section5LocalRefinementConstant_le_scaled (k + 1 + 1) (η * β / 2)
    (η * β / 2)⁻¹ hb hb1 le_rfl
  have hs5 : section5LocalRefinementConstant (k + 1 + 1) 1 ≤ X ^ (2 ^ (40 * (k + 1 + 1) ^ 3 + 2)) :=
    (s5_one_le (d := k + 1 + 1) (by omega)).trans (pow_le_pow_left₀ (by norm_num) hX _)
  have hpow : ((η * β / 2)⁻¹) ^ polynomialPartitionConstant (k + 1 + 1) ≤
      X ^ (2 ^ (M + 2 + 4 * (k + 1 + 1 + 1) ^ 2)) :=
    pw_pow hX (inv_pos.mpr hb).le hbi (polyPartConst_le (k + 1 + 1))
  have hR : section5LocalRefinementConstant (k + 1 + 1) (η * β / 2) ≤ X ^ (2 ^ (Q - 1)) := by
    refine hscaled.trans ?_
    have := pw_mul' hX (le_trans (by norm_num) (section5LocalRefinementConstant_ge_four _ _))
      (pow_nonneg (inv_pos.mpr hb).le _) hs5 hpow
    refine this.trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) ?_))
    have e1 : k + 1 + 1 = k + 2 := by ring
    have e2 : k + 1 + 1 + 1 = k + 3 := by ring
    rw [e1, e2]
    rw [hQdef]
    omega
  -- the count constant
  have hσ16 : σ / 16 ≤ 1 := by linarith
  have hσ16' : 0 ≤ σ / 16 := by positivity
  have hr1 : (1 : Real) ≤ 2 * ((k + 1 + 2 : Nat) : Real) := by push_cast; linarith
  have hc1 : (1 : Real) ≤ 6 * ((k + 1 : Nat) : Real) := by push_cast; linarith
  have hrpow : (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16) ≤ 2 * ((k + 1 + 2 : Nat) : Real) := by
    calc (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16) ≤
          (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
      _ = _ := Real.rpow_one _
  have hcpow : (6 * ((k + 1 : Nat) : Real)) ^ (σ / 16) ≤ 6 * ((k + 1 : Nat) : Real) := by
    calc (6 * ((k + 1 : Nat) : Real)) ^ (σ / 16) ≤ (6 * ((k + 1 : Nat) : Real)) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hc1 hσ16
      _ = _ := Real.rpow_one _
  have hB0 : 0 ≤ boundaryRefinementConstant (1 / 16) := (section5LocalRefinementConstant_pos _ _).le
  have hr : 2 * ((k + 1 + 2 : Nat) : Real) ≤ X ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw hX (k := k) (c := 2 * (k + 1 + 2)) (by omega)
    push_cast at this ⊢; linarith
  have hc : 6 * ((k + 1 : Nat) : Real) ≤ X ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw hX (k := k) (c := 6 * (k + 1)) (by omega)
    push_cast at this ⊢; linarith
  have h2B : 2 * boundaryRefinementConstant (1 / 16) ≤ X ^ (2 ^ (1083 + 1)) :=
    pw_mul hX (by norm_num) hB0 (hX.trans (pw_X hX _)) (pw_const hX cubic_boundary_refinement_constant_upper)
  have hD : inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ ≤
      X ^ (2 ^ (max (1083 + 1) (k + 3) + 1 + 1 + 1)) := by
    unfold inverseStepCountConstant localInverseAssemblyConstant
    have hmax : max 1 (2 * boundaryRefinementConstant (1 / 16) *
        (2 * ((k + 1 + 2 : Nat) : Real)) ^ (1 - σ / 16)) ≤
        X ^ (2 ^ (max (1083 + 1) (k + 3) + 1)) :=
      max_le (one_le_pw hX _) (pw_mul' hX (mul_nonneg (by norm_num) hB0)
        (Real.rpow_nonneg (by linarith) _) h2B (hrpow.trans hr))
    have := pw_mul' hX (le_trans zero_le_one (le_max_left _ _)) (Real.rpow_nonneg (by linarith) _) hmax
      (hcpow.trans hc)
    exact this.trans (pw_mono hX le_rfl (by omega))
  have hD1 : 1 ≤ inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ := by
    unfold inverseStepCountConstant localInverseAssemblyConstant
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hc1 hσ16')
  have hP1 : (1 : Real) ≤ polynomialPartitionConstant (k + 1 + 1) := by
    exact_mod_cast polyPartConst_pos (k + 1 + 1)
  have hDp : (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ^
      ((polynomialPartitionConstant (k + 1 + 1) : Real))⁻¹ ≤
      inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ := by
    calc _ ≤ (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hD1 (inv_le_one_of_one_le₀ hP1)
      _ = _ := Real.rpow_one _
  have hPIC : phaseInverseConstant (k + 1 + 1) (η * β / 2)
      (inverseStepCountConstant (k + 1) (6 * ((k + 1 : Nat) : Real)) σ) ≤ X ^ (2 ^ Q) := by
    unfold phaseInverseConstant
    have := pw_mul' hX (le_trans zero_le_one (section5LocalRefinementConstant_ge_four _ _ |>.trans'
      (by norm_num))) (Real.rpow_nonneg (le_trans zero_le_one hD1) _) hR (hDp.trans hD)
    refine this.trans (pw_mono hX le_rfl ?_)
    have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
    rw [hQdef]; omega
  unfold inverseStepThreshold
  have hppt := positivePowerThreshold_one_le_double_exp hσ'0.le
    (le_exp_exp_of_le_exp (ex_of_pw hPIC)) hσ'
  refine hppt.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_))
  exact pw_add hX (pw_mono hX le_rfl (le_max_left Q s)) (pw_mono hX le_rfl (le_max_right Q s))

/-! ### The step -/

/-- The log-degree after one step. -/
def envStep (k μD μ0 μK μ : Nat) : Nat :=
  max (GenParams.densDeg k μD μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (GenParams.threshDeg k μD μ0 μK + 3) (40 * (k + 2) ^ 3 + 1095))

/-- **The single-piece step in dimension `k`, with envelopes.** -/
theorem envBound_step {V : Real} {D k K p μV μD μ0 μK μ : Nat}
    (H : GenParams.StdHyp V D k K p μV μD μ0 μK) (hk : 1 ≤ k) (hcov : UniformCovers k V D)
    (hrec : Section16RecurrenceProfileWith k (familyRecThr k K p) (familyRecExp k p))
    (hlow : EnvBound (k + 1) μ) : EnvBound (k + 2) (envStep k μD μ0 μK μ) := by
  intro alpha ha ha2
  obtain ⟨hV, hVμ, hμ0, hD, hkD, hk0, hK, hKμ, hp, hpμ⟩ := H
  have hX := two_div_ge_two ha ha2
  set E := GenParams.expDeg k μD μ0 μK with hEdef
  set Th := GenParams.threshDeg k μD μ0 μK with hThdef
  set dd := GenParams.densDeg k μD μ0 with hdddef
  set M1 := dd + 1 + μ with hM1def
  have hETh : E + 4 ≤ Th := by rw [hThdef]; unfold GenParams.threshDeg; exact le_max_left _ _
  have hk3 : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  -- the input parameter and the lower-degree bound
  obtain ⟨he0, he8, hei, hy0, hyle, hyi⟩ :=
    GenParams.yIn_bounds (K := K) (p := p) ha ha2 hV hVμ hμ0 hD hkD hk0
  have hy2 : (GenParams.std V D k K p μ0).yIn alpha ≤ 1 / 2 := hyle.trans ha2
  obtain ⟨β, σ, T, hB, b0, b1, s0, s16, bi, si, Ti⟩ := hlow _ hy0 hy2
  obtain ⟨-, hYμ⟩ := input_scale_le (μ := μ) ha ha2 hy0 hyi
  have bi' : β⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) := bi.trans hYμ
  have si' : σ⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ M1)) := si.trans (Real.exp_le_exp.mpr hYμ)
  have Ti' : T ≤ Real.exp (Real.exp ((2 / alpha) ^ (2 ^ M1))) :=
    Ti.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYμ))
  have hei' : ((GenParams.std V D k K p μ0).eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ M1) :=
    pw_mono hX hei (by rw [hM1def, hdddef]; unfold GenParams.densDeg; omega)
  have heta1 : (GenParams.std V D k K p μ0).eta alpha ≤ 1 := by linarith
  -- the step
  have hstep := (GenParams.std V D k K p μ0).inverse_step hV hK hp hk hcov hrec ha ha2
    (GenParams.std_lift ha ha2 hV hVμ hμ0) hB b0 s0 s16
  -- the localization exponent and `σ′`
  obtain ⟨hEl0, hEli⟩ := GenParams.Eloc_inv_le (K := K) ha ha2 hV hVμ hμ0 hD hkD hk0 hp hpμ
  obtain ⟨-, hEl2, -⟩ := (GenParams.std V D k K p μ0).Eloc_pos_le hV hp ha ha2
  obtain ⟨σ0', σ16', σeq⟩ := sigma_step (d := k + 1) hEl0 hEl2 s0 s16
  have h32P : 32 * (polynomialPartitionConstant (k + 1 + 1) : Real) ≤
      (2 / alpha) ^ (2 ^ (4 * (k + 3) ^ 2 + 4)) := by
    refine pw_const hX ?_
    have hP := polyPartConst_le (k + 1 + 1)
    rw [show k + 1 + 1 + 1 = k + 3 by ring] at hP
    have hn : 4 * (k + 3) ^ 2 + 5 ≤ 2 ^ (4 * (k + 3) ^ 2 + 4) :=
      Nat.lt_two_pow_self (n := 4 * (k + 3) ^ 2 + 4)
    have hnat : 32 * polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ (2 ^ (4 * (k + 3) ^ 2 + 4)) := by
      calc 32 * polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ 5 * 2 ^ (4 * (k + 3) ^ 2) :=
            Nat.mul_le_mul (by norm_num) hP
        _ = 2 ^ (4 * (k + 3) ^ 2 + 5) := by rw [← pow_add]; ring_nf
        _ ≤ 2 ^ (2 ^ (4 * (k + 3) ^ 2 + 4)) := Nat.pow_le_pow_right (by norm_num) hn
    exact_mod_cast hnat
  set S := max (max (4 * (k + 3) ^ 2 + 4) (E + 3) + 1) M1 + 1 with hSdef
  have hσ' : (inverseStepExponent (k + 1) ((GenParams.std V D k K p μ0).Eloc alpha) σ)⁻¹ ≤
      Real.exp ((2 / alpha) ^ (2 ^ S)) := by
    rw [σeq]
    have h1 := pw_mul' hX (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (inv_pos.mpr hEl0).le h32P hEli
    exact ex_mul' hX (inv_pos.mpr s0).le (ex_of_pw h1) si'
  -- the thresholds
  have hTl := GenParams.Tloc_le_exp ⟨hV, hVμ, hμ0, hD, hkD, hk0, hK, hKμ, hp, hpμ⟩ hk ha ha2
  have hc : 6 * ((k + 1 : Nat) : Real) ≤ 2 ^ (2 ^ (k + 3)) := by
    have := small_nat_le_pw (le_refl (2 : Real)) (k := k) (c := 6 * (k + 1)) (by omega)
    push_cast at this ⊢; linarith
  have hd : (((k + 1 + 2 : Nat) : Real) ^ (2 : Nat)) ≤ 2 ^ (2 ^ (k + 3)) := by
    have h1 : k + 1 + 2 ≤ 2 ^ (k + 3) := by
      have := Nat.lt_two_pow_self (n := k + 3); omega
    have h2 : 2 * (k + 3) ≤ 2 ^ (k + 3) := by
      have := Nat.lt_two_pow_self (n := k + 2); rw [pow_succ]; omega
    have hnat : (k + 1 + 2) ^ 2 ≤ 2 ^ (2 ^ (k + 3)) :=
      calc (k + 1 + 2) ^ 2 ≤ (2 ^ (k + 3)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 2 ^ (2 * (k + 3)) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ (2 ^ (k + 3)) := Nat.pow_le_pow_right (by norm_num) h2
    exact_mod_cast hnat
  have hshort := short_thr_le hX (d := k + 1) (j := k + 3) hEl0 hEli (by positivity) hc Ti' hTl hd
  have hinv := inv_thr_le hX (k := k) he0 heta1 b0 b1 hei' bi' s0 s16 σ0' hσ'
  -- assemble
  refine ⟨(GenParams.std V D k K p μ0).eta alpha * β / 4, _, _, hstep,
    div_pos (mul_pos he0 b0) (by norm_num), ?_, σ0', σ16',
    ?_, ex_mono hX hσ' ?_, ?_⟩
  · have : (GenParams.std V D k K p μ0).eta alpha * β ≤ 1 := mul_le_one₀ heta1 b0.le b1
    linarith
  · rw [show ((GenParams.std V D k K p μ0).eta alpha * β / 4)⁻¹ =
      4 * (((GenParams.std V D k K p μ0).eta alpha)⁻¹ * β⁻¹) by field_simp]
    have h1 := pw_mul hX (inv_pos.mpr he0).le (inv_pos.mpr b0).le hei' bi'
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ (M1 + 1)) :=
      (four_le_pw_one hX).trans (pw_mono hX le_rfl (by omega))
    refine (pw_mul hX (by norm_num) (mul_nonneg (inv_pos.mpr he0).le (inv_pos.mpr b0).le) h4 h1).trans
      (pw_mono hX le_rfl ?_)
    unfold envStep; rw [← hdddef]; omega
  · unfold envStep; rw [← hdddef, ← hThdef]; omega
  · refine max_le (dex_mono hX hshort ?_) (dex_mono hX hinv ?_)
    · unfold envStep; rw [← hdddef, ← hThdef]; omega
    · unfold envStep; rw [← hdddef, ← hThdef]; omega

end LeanProofs.GowersSzemeredi

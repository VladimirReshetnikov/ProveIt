import GowersSzemeredi.Proofs18GenericEnvelopeBase
import GowersSzemeredi.Proofs18DoubleExponentialBounds
import GowersSzemeredi.Proofs18FejerIterationParameters
import GowersSzemeredi.Proofs05RefinementConstantBounds
import GowersSzemeredi.Proofs18ShortLocalizationInverse

/-! Shared discrepancy envelopes and numerical bounds for the inverse step.

`EnvBound` records power-of-two controls of the discrepancy parameters and
threshold. The degree-three base, power estimates and localization thresholds
are shared by the generic iteration and the final proof routes.

`envBound_three` and `polyPartConst_mul32_le_pw` are in
`Proofs18EnvelopeBoundsSide`, outside the final route. -/
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
  have hKe : 4 * polynomialPartitionConstant d ≤ 2 ^ (40 * d ^ 3 + 1) := by
    refine (Nat.mul_le_mul_left 4 (polyPartConst_le d)).trans ?_
    rw [show 4 * 2 ^ (4 * (d + 1) ^ 2) = 2 ^ (4 * (d + 1) ^ 2 + 2) by ring]
    exact Nat.pow_le_pow_right (by norm_num) (by
      nlinarith [Nat.pow_le_pow_right hd (show 1 ≤ 3 by norm_num),
        Nat.pow_le_pow_right hd (show 2 ≤ 3 by norm_num)])
  have hT : (polynomialPartitionThreshold d : Real) = 2 ^ (2 ^ (40 * d ^ 3 + 1)) := by
    simp only [polynomialPartitionThreshold, weylThreshold, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, ← pow_succ]
  have h16 : (16 : Real) ^ polynomialPartitionConstant d ≤ 2 ^ (2 ^ (40 * d ^ 3 + 1)) := by
    rw [show (16 : Real) = 2 ^ 4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hKe
  have h4 : (4 : Real) ^ polynomialPartitionConstant d ≤ 2 ^ (2 ^ (40 * d ^ 3 + 1)) :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) _).trans h16
  have hpi : (4 * Real.pi / 1) ^ polynomialPartitionConstant d ≤ 2 ^ (2 ^ (40 * d ^ 3 + 1)) :=
    (pow_le_pow_left₀ (by positivity) (by linarith [Real.pi_lt_four]) _).trans h16
  have hK4 := le_self_pow₀ (by norm_num : (1 : Real) ≤ 4) (cor57_partition_constant_pos d).ne'
  unfold section5LocalRefinementConstant
  rw [show 40 * d ^ 3 + 2 = 40 * d ^ 3 + 1 + 1 by omega, pow_succ 2 (40 * d ^ 3 + 1), pow_mul]
  generalize (2 : Real) ^ 2 ^ (40 * d ^ 3 + 1) = W at hT h4 hpi ⊢
  nlinarith [max_le (max_le hT.le hpi) h4, hK4.trans h4]

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
  have h1 := pw_mul hX hY0 (le_refl (X ^ (2 ^ max a b))) (le_refl _)
  have h2 := pw_mul hX (mul_nonneg hY0 hY0) h1 h1
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
    exact pw_mul hX (inv_pos.mpr hy0).le (hX.trans (pw_X hX _)) hyi
  exact ⟨h2, pw_pow hX (by positivity) h2 le_rfl⟩

alias polyPartConst_pos := cor57_partition_constant_pos

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
    (he0 : 0 < e) (heI : e⁻¹ ≤ X ^ (2 ^ a)) (hc : c ≤ 2 ^ (2 ^ j))
    (hT : T ≤ Real.exp (Real.exp (X ^ (2 ^ m)))) (hTl : Tl ≤ Real.exp (X ^ (2 ^ t)))
    (hd : (((d + 2 : Nat) : Real) ^ (2 : Nat)) ≤ 2 ^ (2 ^ j)) :
    shortLocalizationThreshold d e c T Tl ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max m j) (max a t) + 2)))) := by
  set M := max (max m j) (max a t)
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
    have hle : max (max m j) a + 2 ≤ M + 2 := by omega
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
  have h := pw_mul hX (by linarith) (le_refl (X ^ (2 ^ m))) (le_refl (X ^ (2 ^ m)))
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

/-- The short-localization threshold at a single-piece step: both geometric
constants fit the level `k + 3`. -/
theorem short_thr_step_le {X : Real} (hX : 2 ≤ X) {k : Nat} {e T Tl : Real} {m a t : Nat}
    (he0 : 0 < e) (heI : e⁻¹ ≤ X ^ (2 ^ a))
    (hT : T ≤ Real.exp (Real.exp (X ^ (2 ^ m)))) (hTl : Tl ≤ Real.exp (X ^ (2 ^ t))) :
    shortLocalizationThreshold (k + 1) e (6 * ((k + 1 : Nat) : Real)) T Tl ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max m (k + 3)) (max a t) + 2)))) := by
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
  exact short_thr_le hX (d := k + 1) (j := k + 3) he0 heI hc hT hTl hd

end LeanProofs.GowersSzemeredi

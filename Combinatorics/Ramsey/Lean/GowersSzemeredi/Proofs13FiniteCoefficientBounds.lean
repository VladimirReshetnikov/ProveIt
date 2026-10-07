import GowersSzemeredi.Proofs13UniformDensityParameters

/-! Explicit coefficient reserves for the finite row-scale construction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_spectrum_bound_formula {alpha : Real} (ha : 0 < alpha) :
    section10SpectrumBound (alpha ^ 32 / 16) = section13K alpha := by
  unfold section10SpectrumBound section13K
  rw [Real.div_rpow (pow_nonneg ha.le _) (by norm_num),
    ← Real.rpow_natCast_mul ha.le]
  norm_num only [Nat.cast_ofNat, mul_neg, mul_zero, mul_one]
  norm_num [Real.rpow_neg_ofNat]
  ring

theorem section13_K_large {alpha : Real} (ha : 0 < alpha) (haone : alpha ≤ 1) :
    (2 : Real) ^ (114 : Nat) ≤ section13K alpha := by
  unfold section13K
  apply le_mul_of_one_le_right (by positivity)
  change 1 ≤ (alpha ^ (320 : Nat))⁻¹
  exact (one_le_inv₀ (pow_pos ha _)).mpr (pow_le_one₀ ha.le haone)

theorem section13_initial_coefficient_lower {alpha : Real} (ha : 0 < alpha)
    (haone : alpha ≤ 1) :
    (2 : Real) ^ (-(672418 : Real)) * alpha ^ (2011584 : Real) ≤
      section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) := by
  have htheta := section13_lambda_lower ha haone
  have ht := section13ThetaOne_mono (by positivity) htheta
  have hformula : section13ThetaOne ((2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real)) =
      (2 : Real) ^ (-(672410 : Real)) * alpha ^ (2011584 : Real) := by
    unfold section13ThetaOne
    rw [← Real.rpow_natCast, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2), ← Real.rpow_mul ha.le,
      ← Real.rpow_intCast, ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
    congr 1 <;> norm_num
  rw [hformula] at ht
  have hpi : 64 * Real.pi ≤ (2 : Real) ^ (8 : Nat) := by
    have := Real.pi_lt_four
    norm_num
    linarith
  have hden : (0 : Real) < 64 * Real.pi := by positivity
  calc
    _ = ((2 : Real) ^ (-(672410 : Real)) * alpha ^ (2011584 : Real)) /
        (2 : Real) ^ (8 : Nat) := by
      rw [← Real.rpow_natCast, ← div_mul_eq_mul_div, ← Real.rpow_sub (by norm_num)]
      congr 1
      norm_num
    _ ≤ ((2 : Real) ^ (-(672410 : Real)) * alpha ^ (2011584 : Real)) / (64 * Real.pi) :=
      div_le_div_of_nonneg_left (by positivity) hden hpi
    _ ≤ _ := div_le_div_of_nonneg_right ht hden.le

theorem add_one_le_two_rpow_twice {x : Real} (hx : 0 ≤ x) :
    x + 1 ≤ (2 : Real) ^ (2 * x) := by
  have hlog : (1 : Real) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have he := Real.add_one_le_exp (Real.log 2 * (2 * x))
  rw [Real.rpow_def_of_pos (by norm_num)]
  nlinarith only [he, mul_nonneg hx (by linarith only [hlog] : 0 ≤ 2 * Real.log 2 - 1)]

theorem section13_bohr_radius_lower {alpha : Real} (ha : 0 < alpha)
    (haone : alpha ≤ 1) :
    (2 : Real) ^ (-(229 * section13K alpha + 227)) *
        alpha ^ (576 * section13K alpha + 576) ≤
      section10Zeta (alpha ^ 32 / 16) := by
  let K := section13K alpha
  let a := alpha ^ 32 / 16
  let k := section10SpectrumParameter a
  have hK : 0 ≤ K := by dsimp [K, section13K]; positivity
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    have hp := pow_le_one₀ ha.le haone (n := 32)
    dsimp [a]
    linarith only [hp]
  have hkpos : 0 < k := by
    apply Nat.one_le_ceil_iff.mpr
    rw [section13_spectrum_bound_formula ha]
    dsimp [section13K]
    positivity
  have hkbound : (k : Real) ≤ K + 1 := by
    dsimp [k, section10SpectrumParameter, a]
    rw [section13_spectrum_bound_formula ha]
    exact (Nat.ceil_lt_add_one hK).le
  have hkexp : (k : Real) ≤ (2 : Real) ^ (2 * K) :=
    hkbound.trans (add_one_le_two_rpow_twice hK)
  let B := (2 : Real) ^ (-(155 * (K + 1))) * a ^ (18 * (K + 1))
  have hnum : B ≤ (2 : Real) ^ (-(155 : Real) * k) * a ^ (18 * k : Real) := by
    apply mul_le_mul
    · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hkbound])
    · exact Real.rpow_le_rpow_of_exponent_ge ha0 ha1 (by linarith only [hkbound])
    · positivity
    · positivity
  have hquot : B / (2 : Real) ^ (2 * K) ≤ section10Zeta a := by
    change _ ≤ ((2 : Real) ^ (-(155 : Real) * k) * a ^ (18 * k)) / k
    rw [← Real.rpow_natCast]
    push_cast
    calc
      _ ≤ B / (k : Real) := div_le_div_of_nonneg_left (by dsimp [B]; positivity)
        (by exact_mod_cast hkpos) hkexp
      _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)
  have hformula : B / (2 : Real) ^ (2 * K) =
      (2 : Real) ^ (-(229 * K + 227)) * alpha ^ (576 * K + 576) := by
    dsimp [B, a]
    rw [Real.div_rpow (pow_nonneg ha.le _) (by norm_num),
      ← Real.rpow_natCast_mul ha.le,
      show (16 : Real) = (2 : Real) ^ (4 : Nat) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : Real) ≤ 2)]
    rw [mul_div_assoc, div_div, ← Real.rpow_add (by norm_num : (0 : Real) < 2),
      ← mul_div_assoc, mul_div_right_comm, ← Real.rpow_sub (by norm_num : (0 : Real) < 2)]
    congr 1 <;> ring
  rw [hformula] at hquot
  exact hquot

theorem section13Zeta_square (alpha : Real) (ha : 0 ≤ alpha) :
    section13Zeta alpha ^ 2 =
      (2 : Real) ^ (-(456 * section13K alpha)) * alpha ^ (1152 * section13K alpha) := by
  unfold section13Zeta
  rw [mul_pow, ← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 2),
    ← Real.rpow_mul_natCast ha]
  congr 1 <;> congr 1 <;> ring

theorem section13_finite_coefficient_reserves {alpha : Real} (ha : 0 < alpha)
    (haone : alpha ≤ 1) :
    let c := section13Zeta alpha / 2
    let d := section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi)
    let z := section10Zeta (alpha ^ 32 / 16)
    12 * c ^ 2 ≤ d ∧ 4 * c ^ 2 ≤ z * d := by
  dsimp only
  let K := section13K alpha
  let B := (2 : Real) ^ (-(672418 : Real)) * alpha ^ (2011584 : Real)
  let A := (2 : Real) ^ (-(229 * K + 227)) * alpha ^ (576 * K + 576)
  have hK : (1000000 : Real) ≤ K :=
    (by norm_num : (1000000 : Real) ≤ 2 ^ (114 : Nat)).trans (section13_K_large ha haone)
  have hB := section13_initial_coefficient_lower ha haone
  have hA := section13_bohr_radius_lower ha haone
  have hrec : 4 * section13Zeta alpha ^ 2 ≤ B := by
    rw [section13Zeta_square alpha ha.le]
    have heq : 4 * ((2 : Real) ^ (-(456 * K)) * alpha ^ (1152 * K)) =
        (2 : Real) ^ (2 - 456 * K) * alpha ^ (1152 * K) := by
      rw [show (4 : Real) = (2 : Real) ^ (2 : Real) by norm_num,
        ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
      rfl
    change 4 * ((2 : Real) ^ (-(456 * K)) * alpha ^ (1152 * K)) ≤ B
    rw [heq]
    apply mul_le_mul
    · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hK])
    · exact Real.rpow_le_rpow_of_exponent_ge ha haone (by linarith only [hK])
    · positivity
    · positivity
  have hbohr : section13Zeta alpha ^ 2 ≤ A * B := by
    have heq : A * B = (2 : Real) ^ (-(229 * K + 672645)) *
        alpha ^ (576 * K + 2012160) := by
      dsimp [A, B]
      rw [mul_mul_mul_comm, ← Real.rpow_add (by norm_num : (0 : Real) < 2),
        ← Real.rpow_add ha]
      congr 1 <;> congr 1 <;> ring
    rw [section13Zeta_square alpha ha.le, heq]
    apply mul_le_mul
    · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by change -(456 * K) ≤ _; linarith only [hK])
    · exact Real.rpow_le_rpow_of_exponent_ge ha haone (by change _ ≤ 1152 * K; linarith only [hK])
    · positivity
    · positivity
  constructor
  · calc
      _ ≤ 4 * section13Zeta alpha ^ 2 := by nlinarith only [sq_nonneg (section13Zeta alpha)]
      _ ≤ B := hrec
      _ ≤ _ := hB
  · calc
      _ = section13Zeta alpha ^ 2 := by ring
      _ ≤ A * B := hbohr
      _ ≤ _ := mul_le_mul hA hB (by dsimp [B]; positivity) (by
        unfold section10Zeta
        positivity)

theorem section13_initial_coefficient_le_one {alpha : Real} (ha : 0 < alpha)
    (haone : alpha ≤ 1) :
    section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) ≤ 1 := by
  have ht : section10Lambda (alpha ^ 32 / 16) ≤ 1 := by
    rw [section13_lambda_formula ha]
    calc
      _ ≤ (2 : Real) ^ (-(59 : Int)) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ ha.le haone) (by positivity)
      _ ≤ 1 := by norm_num
  have ht0 : 0 ≤ section10Lambda (alpha ^ 32 / 16) := by unfold section10Lambda; positivity
  have hOne : section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ≤ 1 := by
    apply mul_le_one₀ _ (pow_nonneg ht0 _) (pow_le_one₀ ht0 ht)
    rw [← Real.rpow_intCast]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  apply (div_le_one (by positivity : (0 : Real) < 64 * Real.pi)).mpr
  apply hOne.trans
  have := Real.pi_gt_three
  linarith

end LeanProofs.GowersSzemeredi

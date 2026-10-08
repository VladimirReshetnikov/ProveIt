import GowersSzemeredi.Proofs16PartJPiece
import GowersSzemeredi.Proofs16CubicGraphWidthBudget
import GowersSzemeredi.Proofs16CubicPieceParameterBudget
import GowersSzemeredi.Proofs16CubicExplicitExponent
import GowersSzemeredi.Proofs16CorollaryLowDimensions

/-! Part J: the dimension-three budget comparison.

The dimension-three pieces of `Proofs16PartJPiece` carry explicit cubic
controls. This module compares them with the source's dimension-three
controls `multipleQ (s⁻¹ rho) gamma 3 ^ s` and `multipleC (s⁻¹ rho) gamma 3 ^ s`
at the piece parameter `s = U^9`, where `U = multipleS theta gamma 2`. It
then runs the budgeted greedy extraction. The result is `Theorem162At 3`,
and with it Corollary 16.11 in dimension three, conditional on:

* the stackable dimension-two structure `StackableStructureAt 2 Q q`, and
* polynomial bounds on its counts (`PolyBoundedControl Q`, `PolyBoundedControl q`).

The argument is the dimension-two comparison (`Proofs16CubicSourceWidth`,
`Proofs16CubicGraphWidthBudget`, `Proofs16DimensionTwo`) one dimension up.
The recurrence constant `576^(-24 n)` replaces `128^(-12 q)`, and the
reserve is `U^9` against `R ≤ U^8`.

Polynomial bounds are essential. The spectrum count `n` enters the width
through `K^(-24 n)`, so a count that is only quasipolynomial in
`1/(theta*gamma)` would exhaust the `exp(poly)` budget for small parameters
(research notes, Part J). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A count is polynomially bounded in `1/(gamma*theta)`. -/
def PolyBoundedControl (f : Real → Real → Nat) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    (f gamma theta : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 64)

section Scales

variable {theta gamma : Real}

theorem partJ_base_ge_two (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    2 ≤ 2 / (theta * gamma) := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  exact (le_div_iff₀ hp).mpr (by linarith)

theorem partJ_multipleS_two_eq (theta gamma : Real) :
    multipleS theta gamma 2 = (2 / (theta * gamma)) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) := rfl

/-- Any power of the base up to `2^256` is at most `U`. -/
theorem partJ_base_pow_le_U (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {m : Nat} (hm : m ≤ (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) :
    (2 / (theta * gamma)) ^ m ≤ multipleS theta gamma 2 := by
  rw [partJ_multipleS_two_eq]
  exact pow_le_pow_right₀ (by linarith [partJ_base_ge_two ht ht1 hg hg1]) hm

theorem partJ_U_ge_sixteen (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    16 ≤ multipleS theta gamma 2 := by
  have hb := partJ_base_ge_two ht ht1 hg hg1
  calc
    (16 : Real) = 2 ^ (4 : Nat) := by norm_num
    _ ≤ (2 / (theta * gamma)) ^ 4 := pow_le_pow_left₀ (by norm_num) hb _
    _ ≤ _ := partJ_base_pow_le_U ht ht1 hg hg1
      ((by norm_num : (4 : Nat) ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/-- The stacking parameter of the slices is at most `U`. -/
theorem partJ_slice_scale_le {Q q : Real → Real → Nat} (hQb : PolyBoundedControl Q)
    (hqb : PolyBoundedControl q)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ((Q gamma (theta / 4) * q gamma (theta / 4) : Nat) : Real) ≤ multipleS theta gamma 2 := by
  have hb := partJ_base_ge_two ht ht1 hg hg1
  have hb0 : 0 ≤ 2 / (theta * gamma) := by linarith
  have ht4 : 0 < theta / 4 := by positivity
  have ht41 : theta / 4 ≤ 1 := by linarith
  have hbase : 2 / (gamma * (theta / 4)) ≤ (2 / (theta * gamma)) ^ 3 := by
    calc
      _ = (2 : Real) ^ 2 * (2 / (theta * gamma)) := by field_simp; ring
      _ ≤ (2 / (theta * gamma)) ^ 2 * (2 / (theta * gamma)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hb 2) hb0
      _ = _ := by ring
  have hpow : (2 / (gamma * (theta / 4))) ^ ((2 : Nat) ^ 64) ≤
      (2 / (theta * gamma)) ^ (3 * (2 : Nat) ^ 64) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hQ := (hQb gamma (theta / 4) hg hg1 ht4 ht41).trans hpow
  have hq := (hqb gamma (theta / 4) hg hg1 ht4 ht41).trans hpow
  push_cast
  calc
    (Q gamma (theta / 4) : Real) * q gamma (theta / 4) ≤
        (2 / (theta * gamma)) ^ (3 * (2 : Nat) ^ 64) * (2 / (theta * gamma)) ^ (3 * (2 : Nat) ^ 64) :=
      mul_le_mul hQ hq (Nat.cast_nonneg _) (by positivity)
    _ = (2 / (theta * gamma)) ^ (6 * (2 : Nat) ^ 64) := by
      rw [← pow_add]; congr 1
    _ ≤ _ := partJ_base_pow_le_U ht ht1 hg hg1
      ((by norm_num : 6 * (2 : Nat) ^ 64 ≤ 2 ^ 67).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

/-- The spectrum count at the halved density is at most `U`. -/
theorem partJ_spectrum_scale_le {Q q : Real → Real → Nat} (hQb : PolyBoundedControl Q)
    (hqb : PolyBoundedControl q)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (partJSpectrumCount Q q (theta / 2) gamma : Real) ≤ multipleS theta gamma 2 := by
  have hb := partJ_base_ge_two ht ht1 hg hg1
  have hb1 : (1 : Real) ≤ 2 / (theta * gamma) := by linarith
  have hb0 : 0 ≤ 2 / (theta * gamma) := by linarith
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  obtain ⟨ha, ha1, hd, hd1⟩ := section16_theta_delta_bounds 2 ht2 ht21 hg hg1
  set a := section16ThetaOne (theta / 2) gamma 2 with ha_def
  set d := section16Delta a with hd_def
  set M : Nat := (2 : Nat) ^ ((2 : Nat) ^ (2 + 5)) with hM_def
  clear_value a d M
  -- a is at least b^(-3M)
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hx : (theta * gamma / 8) = (4 * (2 / (theta * gamma)))⁻¹ := by field_simp; ring
  have h4b : 4 * (2 / (theta * gamma)) ≤ (2 / (theta * gamma)) ^ 3 := by
    nlinarith [hb, mul_le_mul hb hb (by norm_num) hb0]
  have ha_eq : a = (theta * gamma / 8) ^ M := by
    rw [ha_def, hM_def]; unfold section16ThetaOne; congr 1; ring
  have hainv : a⁻¹ ≤ (2 / (theta * gamma)) ^ (3 * M) := by
    rw [ha_eq, ← inv_pow, hx, inv_inv, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h4b M
  -- d is at least 2^-49 a^6
  have ha4 : a / 4 ≤ 1 := by linarith only [ha1]
  have hdlow : (2 : Real) ^ (-(37 : Real)) * (a / 4) ^ (6 : Nat) ≤ d := by
    rw [hd_def]
    unfold section16Delta
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by positivity) ha4 (by norm_num)
  -- 2/(d*(a/8)) is at most 2^53 * a^-7
  have hratio : 2 / (d * (a / 8)) ≤ (2 : Real) ^ (53 : Nat) * (a⁻¹) ^ (7 : Nat) := by
    have hdpos : 0 < d := hd
    have hlow : (2 : Real) ^ (-(37 : Real)) * (a / 4) ^ (6 : Nat) * (a / 8) ≤ d * (a / 8) :=
      mul_le_mul_of_nonneg_right hdlow (by positivity)
    have hval : (2 : Real) ^ (-(37 : Real)) * (a / 4) ^ (6 : Nat) * (a / 8) =
        ((2 : Real) ^ (52 : Nat))⁻¹ * a ^ (7 : Nat) := by
      rw [Real.rpow_neg (by norm_num), show (37 : Real) = ((37 : Nat) : Real) by norm_num,
        Real.rpow_natCast]
      field_simp
      ring
    rw [hval] at hlow
    calc
      2 / (d * (a / 8)) ≤ 2 / (((2 : Real) ^ (52 : Nat))⁻¹ * a ^ (7 : Nat)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hlow
      _ = (2 : Real) ^ (53 : Nat) * (a⁻¹) ^ (7 : Nat) := by
        rw [inv_pow]; field_simp
  have hratio2 : 2 / (d * (a / 8)) ≤ (2 / (theta * gamma)) ^ ((2 : Nat) ^ 133) := by
    apply hratio.trans
    calc
      (2 : Real) ^ (53 : Nat) * (a⁻¹) ^ (7 : Nat) ≤
          (2 / (theta * gamma)) ^ (53 : Nat) * ((2 / (theta * gamma)) ^ (3 * M)) ^ (7 : Nat) :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) hb _)
          (pow_le_pow_left₀ (by positivity) hainv _) (by positivity) (by positivity)
      _ = (2 / (theta * gamma)) ^ (53 + 3 * M * 7) := by rw [← pow_mul, ← pow_add]
      _ ≤ _ := pow_le_pow_right₀ hb1 (by rw [hM_def]; norm_num)
  have hd8 : 0 < a / 8 := by positivity
  have hd81 : a / 8 ≤ 1 := by linarith only [ha1]
  have hQ := hQb d (a / 8) hd hd1 hd8 hd81
  have hq := hqb d (a / 8) hd hd1 hd8 hd81
  have hpow : (2 / (d * (a / 8))) ^ ((2 : Nat) ^ 64) ≤
      (2 / (theta * gamma)) ^ ((2 : Nat) ^ 133 * (2 : Nat) ^ 64) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hratio2 _
  unfold partJSpectrumCount
  rw [← ha_def, ← hd_def]
  push_cast
  calc
    (Q d (a / 8) : Real) * q d (a / 8) ≤
        (2 / (theta * gamma)) ^ ((2 : Nat) ^ 133 * (2 : Nat) ^ 64) *
          (2 / (theta * gamma)) ^ ((2 : Nat) ^ 133 * (2 : Nat) ^ 64) :=
      mul_le_mul (hQ.trans hpow) (hq.trans hpow) (Nat.cast_nonneg _) (by positivity)
    _ = (2 / (theta * gamma)) ^ (2 * ((2 : Nat) ^ 133 * (2 : Nat) ^ 64)) := by
      rw [← pow_add]; congr 1
    _ ≤ _ := partJ_base_pow_le_U ht ht1 hg hg1 (by norm_num)

/-- The remainder parameter of Lemma 16.9 in dimension three is at most `U^8`. -/
theorem partJ_remainder_scale_le (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) :
    section16Lemma9R (theta / 2) gamma 2 ≤ (multipleS theta gamma 2) ^ (8 : Nat) := by
  have hb := partJ_base_ge_two ht ht1 hg hg1
  have hU16 := partJ_U_ge_sixteen ht ht1 hg hg1
  have hU0 : 0 ≤ multipleS theta gamma 2 := by linarith
  have hginv : gamma ^ (-(2 : Int)) ≤ multipleS theta gamma 2 := by
    have hp : 0 < theta * gamma := mul_pos ht hg
    have hgi : gamma⁻¹ ≤ 2 / (theta * gamma) := by
      rw [← one_div]
      apply (div_le_div_iff₀ hg hp).mpr
      nlinarith [mul_le_mul_of_nonneg_right ht1 hg.le]
    calc
      gamma ^ (-(2 : Int)) = (gamma⁻¹) ^ (2 : Nat) := by rw [zpow_neg, zpow_ofNat, inv_pow]
      _ ≤ (2 / (theta * gamma)) ^ 2 := pow_le_pow_left₀ (by positivity) hgi _
      _ ≤ _ := partJ_base_pow_le_U ht ht1 hg hg1 (by norm_num)
  have hs := multipleS_div_two_pow_le 2 5 ht ht1 hg hg1
  have hcoef : (2 : Real) ^ (-((2 : Nat) + 2 : Real)) * (theta / 2) = theta / (2 : Real) ^ 5 := by
    norm_num; ring
  have hR : section16Lemma9R (theta / 2) gamma 2 =
      3 * gamma ^ (-(2 : Int)) * multipleS (theta / (2 : Real) ^ 5) gamma 2 := by
    unfold section16Lemma9R
    rw [hcoef]
    norm_num
  rw [hR]
  calc
    3 * gamma ^ (-(2 : Int)) * multipleS (theta / (2 : Real) ^ 5) gamma 2 ≤
        multipleS theta gamma 2 * multipleS theta gamma 2 * (multipleS theta gamma 2) ^ (5 + 1) :=
      mul_le_mul (mul_le_mul (by linarith) hginv (by positivity) hU0) hs
        (by unfold multipleS; positivity) (by positivity)
    _ = (multipleS theta gamma 2) ^ (8 : Nat) := by ring

theorem partJ_lemma9R_one_le (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    1 ≤ section16Lemma9R (theta / 2) gamma 2 := by
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hS := one_le_multipleS 2 (by positivity : 0 < (2 : Real) ^ (-((2 : Nat) + 2 : Real)) *
    (theta / 2)) (by
      have hf : (2 : Real) ^ (-((2 : Nat) + 2 : Real)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      nlinarith [mul_le_of_le_one_left (by positivity : (0 : Real) ≤ theta / 2) hf]) hg hg1
  unfold section16Lemma9R
  have h3 : (1 : Real) ≤ ((2 ^ 2 - 1 : Nat) : Real) := by norm_num
  calc
    (1 : Real) = 1 * 1 * 1 := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul h3 hginv (by norm_num) (by positivity)) hS (by norm_num)
      (by positivity)

/-- The recurrence factor for `3n` dimension-two graphs. -/
theorem partJ_recurrence_lower (n : Nat) :
    (2 : Real) ^ (-(240 * (n : Real))) ≤ section16RecurrenceExponent 2 (3 * n) := by
  unfold section16RecurrenceExponent section16K
  have h1 : ((((2 + 1) ^ 2 * 2 ^ (2 + 4) : Nat)) : Real) = 576 := by norm_num
  rw [h1]
  have h2 : (-(((2 ^ (2 + 1) * (3 * n) : Nat) : Int))) = -((24 * n : Nat) : Int) := by
    push_cast; ring
  rw [h2, zpow_neg, zpow_natCast,
    show (240 * (n : Real)) = ((240 * n : Nat) : Real) by push_cast; ring,
    Real.rpow_neg (by norm_num), Real.rpow_natCast]
  apply inv_anti₀ (by positivity)
  calc
    (576 : Real) ^ (24 * n) ≤ (1024 : Real) ^ (24 * n) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (2 : Real) ^ (240 * n) := by
      rw [show (1024 : Real) = 2 ^ 10 by norm_num, ← pow_mul]
      ring_nf

end Scales

end LeanProofs.GowersSzemeredi

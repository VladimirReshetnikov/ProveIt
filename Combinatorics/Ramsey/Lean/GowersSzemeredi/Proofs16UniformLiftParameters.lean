import GowersSzemeredi.Proofs16PackagedExplicitCover
import GowersSzemeredi.Proofs16CoverParameterMonotonicity
import GowersSzemeredi.Proofs16RoundedPowerWidth

/-! Uniform quantitative controls for the affine lift. The constants depend
only on the input parameters, rather than on locally selected graph counts,
the parent box, or its modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16LineWidthExponent (q k : Nat) (sigma theta gamma : Real) : Real :=
  let delta := section16Delta (section16ThetaOne theta gamma k)
  let r := section16Lemma9R theta gamma k
  let t := section16T delta (section16ThetaOne theta gamma k) k
  ((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r *
    (multipleC (sigma / (2 * t)) delta k) ^ t) /
    (2 * (section16K k : Real) ^ ((2 : Nat) ^ (k + 1) * q))

theorem section16Lemma9Width_eq_power (m q k : Nat) (sigma theta gamma : Real) :
    section16Lemma9Width m q k sigma theta gamma
      (section16Delta (section16ThetaOne theta gamma k))
      (section16ThetaOne theta gamma k) (section16Zeta theta gamma k) =
      (section16Zeta theta gamma k / 2) *
        (m : Real) ^ section16LineWidthExponent q k sigma theta gamma := rfl

theorem section16LineWidthExponent_pos {k : Nat} (hk : 0 < k)
    {sigma theta gamma : Real} (hσ : 0 < sigma)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (q : Nat) :
    0 < section16LineWidthExponent q k sigma theta gamma := by
  obtain ⟨htheta, htheta1, hd, hd1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  have hr : 0 < section16Lemma9R theta gamma k := by
    have htwo : 1 < (2 : Nat) ^ k := one_lt_pow₀ (by norm_num) hk.ne'
    have hn : (0 : Real) < ((2 ^ k - 1 : Nat) : Real) := by exact_mod_cast (show 0 < 2 ^ k - 1 by omega)
    unfold section16Lemma9R multipleS
    positivity
  have hT := zero_lt_one.trans_le (section16T_one_le k hd hd1 htheta htheta1)
  have hK : (0 : Real) < section16K k := by unfold section16K; positivity
  unfold section16LineWidthExponent multipleC
  dsimp only
  positivity

/-- Padding the delta-side count decreases the exponent, independently of
the input width. -/
theorem section16LineWidthExponent_antitone (k : Nat) (sigma theta gamma : Real) :
    Antitone (fun q => section16LineWidthExponent q k sigma theta gamma) := by
  intro q q' hq
  have hK : (1 : Real) ≤ section16K k := by
    exact_mod_cast (show 0 < section16K k by unfold section16K; positivity)
  have hC (a g : Real) (d : Nat) : 0 ≤ multipleC a g d :=
    (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (d + 8) ≠ 0)).pow_nonneg _
  unfold section16LineWidthExponent
  dsimp only
  apply div_le_div_of_nonneg_left (mul_nonneg (Real.rpow_nonneg (hC _ _ _) _) (Real.rpow_nonneg (hC _ _ _) _))
    (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK (Nat.mul_le_mul_left _ hq)) (by norm_num)

def section16UniformDeltaCount (sigma theta gamma : Real) (k : Nat) : Nat :=
  Nat.ceil (section16Lemma9DeltaQBound sigma (section16Delta (section16ThetaOne theta gamma k))
    (section16ThetaOne theta gamma k) k)

def section16UniformSampleCount (sigma theta gamma : Real) (k : Nat) : Nat :=
  Nat.ceil (6 * max 1 (section16Lemma9QBound sigma theta gamma k) / sigma)

def section16UniformSliceExponent (sigma theta gamma s : Real) (k : Nat) : Real :=
  let p := (section16UniformSampleCount sigma theta gamma k : Real) * s
  (multipleC (p⁻¹ * sigma) gamma k) ^ p

def section16UniformLiftGraphBudget (sigma theta gamma s : Real) (k : Nat) : Real :=
  let r := section16UniformSampleCount sigma theta gamma k
  let b := (multipleQ (((r : Real) * s)⁻¹ * sigma) gamma k) ^ ((r : Real) * s)
  max b ((r.choose 2 : Real) * b * b)

def section16UniformLiftExponent (sigma theta gamma s : Real) (k : Nat) : Real :=
  section16LineWidthExponent (section16UniformDeltaCount sigma theta gamma k) k sigma theta gamma *
    section16UniformSliceExponent sigma theta gamma s k / 4

def section16UniformLiftExponentThreshold (sigma theta gamma s : Real) (k : Nat) (b : Real) : Real :=
  section16RoundedExponentThreshold (section16Zeta theta gamma k / 2)
    (section16LineWidthExponent (section16UniformDeltaCount sigma theta gamma k) k sigma theta gamma)
    (section16UniformSliceExponent sigma theta gamma s k) b

def section16UniformLiftThreshold (sigma theta gamma s : Real) (k : Nat) : Real :=
  section16RoundedPowerThreshold (section16Zeta theta gamma k / 2)
    (section16LineWidthExponent (section16UniformDeltaCount sigma theta gamma k) k sigma theta gamma)
    (section16UniformSliceExponent sigma theta gamma s k)

theorem section16UniformSampleCount_pos {sigma theta gamma : Real} (k : Nat) (hσ : 0 < sigma) :
    0 < section16UniformSampleCount sigma theta gamma k := by
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_left _ _))) hσ

theorem section16UniformSliceExponent_pos {sigma theta gamma s : Real} (k : Nat)
    (hσ : 0 < sigma) (hg : 0 < gamma) (hs : 0 < s) :
    0 < section16UniformSliceExponent sigma theta gamma s k := by
  have hr : (0 : Real) < section16UniformSampleCount sigma theta gamma k :=
    Nat.cast_pos.mpr (section16UniformSampleCount_pos k hσ)
  unfold section16UniformSliceExponent multipleC
  positivity

theorem section16UniformLiftExponent_pos {k : Nat} (hk : 0 < k)
    {sigma theta gamma s : Real} (hσ : 0 < sigma)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 0 < s) :
    0 < section16UniformLiftExponent sigma theta gamma s k :=
  div_pos (mul_pos (section16LineWidthExponent_pos hk hσ ht ht1 hg hg1 _)
    (section16UniformSliceExponent_pos k hσ hg hs)) (by norm_num)

theorem section16UniformLiftThreshold_one_le (sigma theta gamma s : Real) (k : Nat) :
    1 ≤ section16UniformLiftThreshold sigma theta gamma s k :=
  (positivePowerThreshold_one_le _ _ _).trans (le_max_left _ _)

end LeanProofs.GowersSzemeredi

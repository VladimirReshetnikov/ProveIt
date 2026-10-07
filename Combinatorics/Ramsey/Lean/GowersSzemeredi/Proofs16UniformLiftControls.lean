import GowersSzemeredi.Proofs16UniformLiftParameters

/-! Replace the graph counts selected inside Lemma 16.9 by uniform ceilings
without losing control of the interpolation budget or width exponent. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_sample_count_le_uniform {q k : Nat} {sigma theta gamma : Real}
    (hσ : 0 < sigma) (hq : (q : Real) ≤ section16Lemma9QBound sigma theta gamma k) :
    Nat.ceil (6 * (max 1 q : Real) / sigma) ≤ section16UniformSampleCount sigma theta gamma k := by
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (max_le_max le_rfl hq) (by norm_num)) hσ.le

/-- Increasing to the uniform sample count decreases the slice exponent
and increases the complete number of interpolated candidate graphs. -/
theorem section16_uniform_lift_controls {q k : Nat} {sigma theta gamma s : Real}
    (hσ : 0 < sigma) (hσ1 : sigma ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 1 ≤ s)
    (hq : (q : Real) ≤ section16Lemma9QBound sigma theta gamma k) :
    let r := Nat.ceil (6 * (max 1 q : Real) / sigma)
    let b := (multipleQ (((r : Real) * s)⁻¹ * sigma) gamma k) ^ ((r : Real) * s)
    section16UniformSliceExponent sigma theta gamma s k ≤
      (multipleC (((r : Real) * s)⁻¹ * sigma) gamma k) ^ ((r : Real) * s) ∧
    max b ((r.choose 2 : Real) * b * b) ≤ section16UniformLiftGraphBudget sigma theta gamma s k := by
  let r := Nat.ceil (6 * (max 1 q : Real) / sigma)
  let R := section16UniformSampleCount sigma theta gamma k
  have hr : 0 < r := Nat.ceil_pos.mpr
    (div_pos (mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_left _ _))) hσ)
  have hr1 : (1 : Real) ≤ r := by exact_mod_cast hr
  have hrR : r ≤ R := section16_sample_count_le_uniform hσ hq
  have hrR' : (r : Real) ≤ R := by exact_mod_cast hrR
  have hparam : (r : Real) * s ≤ (R : Real) * s :=
    mul_le_mul_of_nonneg_right hrR' (zero_le_one.trans hs)
  obtain ⟨ha, hb⟩ := multipleCover_controls_mono k hg hg1 hσ hσ1
    (one_le_mul_of_one_le_of_one_le hr1 hs) hparam
  refine ⟨ha, ?_⟩
  let b := (multipleQ (((r : Real) * s)⁻¹ * sigma) gamma k) ^ ((r : Real) * s)
  let B := (multipleQ (((R : Real) * s)⁻¹ * sigma) gamma k) ^ ((R : Real) * s)
  have hb0 : 0 ≤ b := (zero_le_one.trans
    (section16_slice_control_ranges (k := k) hr hs hg hg1 hσ hσ1).2.2)
  exact section16_compressed_budget_mono hrR hb0 hb

/-- The line-width bound is uniform over every allowable delta-side count. -/
theorem section16_uniform_line_width {m q k : Nat} {sigma theta gamma : Real}
    (hm : 1 ≤ m)
    (hq : (q : Real) ≤ section16Lemma9DeltaQBound sigma
      (section16Delta (section16ThetaOne theta gamma k)) (section16ThetaOne theta gamma k) k) :
    (section16Zeta theta gamma k / 2) * (m : Real) ^
        section16LineWidthExponent (section16UniformDeltaCount sigma theta gamma k) k sigma theta gamma ≤
      section16Lemma9Width m q k sigma theta gamma
        (section16Delta (section16ThetaOne theta gamma k))
        (section16ThetaOne theta gamma k) (section16Zeta theta gamma k) := by
  have hq' : q ≤ section16UniformDeltaCount sigma theta gamma k := by
    have h : (q : Real) ≤ section16UniformDeltaCount sigma theta gamma k := hq.trans (Nat.le_ceil _)
    exact_mod_cast h
  rw [section16Lemma9Width_eq_power]
  apply mul_le_mul_of_nonneg_left _ (by unfold section16Zeta; positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm)
    (section16LineWidthExponent_antitone k sigma theta gamma hq')

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16UniformLiftControls

/-! The canonical affine lift realizes the unordered-pair graph budget,
strictly improving the previously proved count without any geometric loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16UniformSampleCount_two_le {sigma theta gamma : Real} (k : Nat)
    (hσ : 0 < sigma) (hσ1 : sigma ≤ 1) :
    2 ≤ section16UniformSampleCount sigma theta gamma k := by
  have hceil : 6 * max 1 (section16Lemma9QBound sigma theta gamma k) ≤
      (section16UniformSampleCount sigma theta gamma k : Real) * sigma :=
    (div_le_iff₀ hσ).mp (Nat.le_ceil _)
  have hR : (6 : Real) ≤ section16UniformSampleCount sigma theta gamma k := by
    calc
      6 ≤ 6 * max 1 (section16Lemma9QBound sigma theta gamma k) := by
        have h := le_max_left (1 : Real) (section16Lemma9QBound sigma theta gamma k)
        linarith only [h]
      _ ≤ _ := hceil
      _ ≤ _ := mul_le_of_le_one_right (Nat.cast_nonneg _) hσ1
  have hR' : 6 ≤ section16UniformSampleCount sigma theta gamma k := by exact_mod_cast hR
  omega

/-- In the actual parameter range the fallback does not enlarge the count:
the uniform budget is exactly choose(R,2)*b^2. -/
theorem section16UniformLiftGraphBudget_eq_pairs {sigma theta gamma s : Real} (k : Nat)
    (hσ : 0 < sigma) (hσ1 : sigma ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 1 ≤ s) :
    let R := section16UniformSampleCount sigma theta gamma k
    let b := (multipleQ (((R : Real) * s)⁻¹ * sigma) gamma k) ^ ((R : Real) * s)
    section16UniformLiftGraphBudget sigma theta gamma s k = (R.choose 2 : Real) * b * b := by
  have hr := section16UniformSampleCount_pos (theta := theta) (gamma := gamma) k hσ
  exact section16_compressed_budget_eq (section16UniformSampleCount_two_le k hσ hσ1)
    (section16_slice_control_ranges (k := k) hr hs hg hg1 hσ hσ1).2.2

/-- This is a strict improvement of the complete uniform candidate budget,
including the degenerate sampling case. All width and mass parameters in
the lifted cover retain their existing definitions. -/
theorem section16UniformLiftGraphBudget_lt_previous {sigma theta gamma s : Real} (k : Nat)
    (hσ : 0 < sigma) (hσ1 : sigma ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 1 ≤ s) :
    let R := section16UniformSampleCount sigma theta gamma k
    let b := (multipleQ (((R : Real) * s)⁻¹ * sigma) gamma k) ^ ((R : Real) * s)
    section16UniformLiftGraphBudget sigma theta gamma s k <
      (R : Real) * b + (R : Real) * R * b * b := by
  have hr := section16UniformSampleCount_pos (theta := theta) (gamma := gamma) k hσ
  exact section16_compressed_budget_lt_old hr
    (section16_slice_control_ranges (k := k) hr hs hg hg1 hσ hσ1).2.2

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16ExplicitConstantBounds
import GowersSzemeredi.Proofs16VarietyShapeMatch
import GowersSzemeredi.Proofs16VarietyPieceBudget
import GowersSzemeredi.Proofs16VarietyLossBound
import GowersSzemeredi.Proofs16VarietyScaleBounds

/-! The variety route's pieces at the source's piece budget.

At the named constants, every relation piece of the variety route
(`polynomialVarietyRelationPieceAt_explicit`) is `MultiplyLinear γ s` with the
explicit parameter
`s = section16VarietyThreeParameter D θ γ = 18r/γ + 64 + L`. Here `r` is the
Lemma 16.9 scale and `L` is the larger of the two logarithmic losses of the
ceiling-free controls (`MultiplyLinearWith.variety_three_multiplyLinear`).

The width coefficient, the count and the losses are written with the exact
arguments of `section16VarietyThreeCeilingFreeExponent`, so the shape
equalities of `Proofs16VarietyShapeMatch` apply by unfolding. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The variety count of the dimension-three pieces. -/
def section16VarietyThreeCount (D : Nat) (theta gamma : Real) : Nat :=
  section16VarietyExtractionCount D gamma (theta / 4)

/-- The `ρ`-free width coefficient of the dimension-three pieces. -/
def section16VarietyThreeWidthCoeff (D : Nat) (theta gamma : Real) : Real :=
  section16VarietyCeilingFreeWidthCoeff explicitLiftK explicitLiftP explicitVarietyK
    explicitVarietyP D (section16VarietyExtractionCount D gamma (theta / 4))
    (9 * section16VarietySpectrumCount D (theta / 2) gamma)
    (section16VarietyExtractionDensity gamma (theta / 4)) theta gamma
    (section16PolynomialJointVarietyExponent explicitVarietyK explicitVarietyP
      (section16VarietySpectrumCount D (theta / 2) gamma) D
      (section16VarietySpectrumDensity (theta / 2) gamma))

/-- The logarithmic loss of the dimension-three pieces. -/
def section16VarietyThreeLoss (D : Nat) (theta gamma : Real) : Real :=
  max (Real.log (section16VarietyThreeWidthCoeff D theta gamma)⁻¹)
    (Real.log (81 * 7 ^ 4 * ((section16VarietyThreeCount D theta gamma : Nat) : Real) ^ 2 + 27))

/-- The piece parameter of the dimension-three pieces. -/
def section16VarietyThreeParameter (D : Nat) (theta gamma : Real) : Real :=
  18 * section16Lemma9R (theta / 2) gamma 2 / gamma + 64 + section16VarietyThreeLoss D theta gamma

theorem section16VarietyThreeLoss_nonneg (D : Nat) (theta gamma : Real) :
    0 ≤ section16VarietyThreeLoss D theta gamma := by
  unfold section16VarietyThreeLoss
  refine le_trans (Real.log_nonneg ?_) (le_max_right _ _)
  have : (0 : Real) ≤ 81 * 7 ^ 4 * ((section16VarietyThreeCount D theta gamma : Nat) : Real) ^ 2 :=
    by positivity
  linarith

/-- The Lemma 16.9 scale is at least one. -/
theorem one_le_section16Lemma9R_half_two {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) : 1 ≤ section16Lemma9R (theta / 2) gamma 2 := by
  rw [section16Lemma9R_half_two_eq ht hg]
  have hx := two_le_two_div ht ht1 hg hg1
  have hgi : 1 ≤ gamma⁻¹ := (one_le_inv₀ hg).mpr hg1
  generalize 2 / (theta * gamma) = x at hx ⊢
  have h1 : (1 : Real) ≤ (32 * x) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) :=
    one_le_pow₀ (by linarith)
  have h2 : (1 : Real) ≤ gamma⁻¹ ^ 2 := one_le_pow₀ hgi
  calc (1 : Real) ≤ 3 * 1 * 1 := by norm_num
    _ ≤ 3 * gamma⁻¹ ^ 2 * (32 * x) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h1 (by norm_num) (by positivity)

/-- **Variety pieces are the source's multiple multilinearity at the explicit parameter.** -/
theorem MultiplyLinearWith.variety_three_multiplyLinear {N D : Nat} [NeZero N]
    {theta gamma : Real} {Piece : Finset (Point N 3 × ZMod N)}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hW : 0 < section16VarietyThreeWidthCoeff D theta gamma)
    (h : MultiplyLinearWith (section16VarietyThreeGraphBound D theta gamma)
      (section16VarietyThreePieceExponent explicitLiftK explicitLiftP explicitVarietyK
        explicitVarietyP explicitVarietyK explicitVarietyP D theta gamma) Piece) :
    MultiplyLinear gamma (section16VarietyThreeParameter D theta gamma) Piece := by
  have hcf := h.variety_three_ceiling_free two_le_explicitLiftK explicitLiftP_pos
    two_le_explicitVarietyK explicitVarietyP_pos two_le_explicitVarietyK explicitVarietyP_pos
    ht ht1 hg hg1
  have hr := one_le_section16Lemma9R_half_two ht ht1 hg hg1
  have hr0 : 0 < section16Lemma9R (theta / 2) gamma 2 := by linarith
  unfold section16VarietyThreeParameter
  refine hcf.multiplyLinear_of_variety_shape (k := 3)
    (Q := ((section16VarietyThreeCount D theta gamma : Nat) : Real))
    hg hg1 hr hW (Nat.cast_nonneg _) (section16VarietyThreeLoss_nonneg D theta gamma)
    (le_max_left _ _) (le_max_right _ _) ?_ ?_
  · intro rho hrho _
    unfold section16VarietyThreeCeilingFreeExponent
    rw [section16VarietyCeilingFreeExponent_eq_shape _ _ _ _ _ _ _ hr0 hrho hg]
    rfl
  · intro rho hrho _
    unfold section16VarietyThreeCeilingFreeGraphBound
    rw [section16VarietyCeilingFreeGraphBound_eq_shape _ hr0 hrho hg]
    rfl

end LeanProofs.GowersSzemeredi

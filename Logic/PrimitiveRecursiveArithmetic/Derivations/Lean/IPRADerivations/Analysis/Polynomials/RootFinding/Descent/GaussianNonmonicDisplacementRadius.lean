import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianNonmonicRD

/-!
# The actual displacement stays inside its computed starting radius

The positive-residual displacement is constructed in a selected smaller
circle, whose denominator is 2^(E+2h). Its radius is therefore at most the
actual starting radius with denominator 2^E. The zero-residual branch
returns the actual zero displacement and the starting radius is zero.
These facts require no shape or nonconstant premise: every coefficient
list, degree and query point is an internal numerical input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNonmonicDisplacementRadius

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalTranslation (translated)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianDescentClock (residualNumerator)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def startingNumerator (C N z : PTm n) : PTm n :=
  GaussianBalancedRadius.radiusNumerator (translated C N z) N
def startingDenominator (C N z : PTm n) : PTm n :=
  GaussianBalancedRadius.radiusDenominator (translated C N z) N
def startingRadius (C N z : PTm n) : PTm n :=
  GaussianBalancedRadius.radius (translated C N z) N

ipra_subst startingNumerator
ipra_subst startingDenominator
ipra_subst startingRadius

theorem starting_denominator_positive (C N z : PTm n) : Γ ⊢[PRAAx]
    le one (startingDenominator C N z) := GaussianBalancedRadius.denominator_positive _ _

theorem translated_residual (C N z : PTm n) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.numerator (translated C N z) N zero ≐ residualNumerator C z :=
  GaussianTranslatedBalancedRadius.residual_identity C N z

theorem starting_numerator_zero (C N z : PTm n) (h0 : Γ ⊢[PRAAx] residualNumerator C z ≐ zero) :
    Γ ⊢[PRAAx] startingNumerator C N z ≐ zero :=
  GaussianBalancedRadius.numerator_zero _ _ ((translated_residual C N z).eqTrans h0)

theorem starting_radius_zero (C N z : PTm n) (h0 : Γ ⊢[PRAAx] residualNumerator C z ≐ zero) :
    Γ ⊢[PRAAx] startingRadius C N z ≐ fraction zero one :=
  GaussianBalancedRadius.radius_zero _ _ ((translated_residual C N z).eqTrans h0)

/-- The genuine computed scale only increases the starting denominator. -/
theorem center_denominator_ge (C N h : PTm n) : Γ ⊢[PRAAx]
    le (GaussianBalancedRadius.radiusDenominator C N)
      (unit (GaussianDominantRadiusValues.scaleExponent C N h)) :=
  GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one)
    (le_add_right (GaussianBalancedRadiusHeight.E C N) (two*h))

theorem center_radius_cross (C N h : PTm n)
    (hPositive : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N zero)) : Γ ⊢[PRAAx]
    le (GaussianOffDominantTerms.radiusNumerator C N*GaussianBalancedRadius.radiusDenominator C N)
      (GaussianBalancedRadius.radiusNumerator C N*unit (GaussianDominantRadiusValues.scaleExponent C N h)) :=
  le_congr (.eqRefl _) (congrMul (GaussianBalancedRadius.numerator_positive C N hPositive).eqSymm (.eqRefl _))
    (le_congr (mul_comm _ _) (mul_comm _ _)
      (mul_le_mul_right (GaussianOffDominantTerms.radiusNumerator C N) (center_denominator_ge C N h)))

theorem center_radius_bound (C N h : PTm n)
    (hPositive : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N zero)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianDominantRadiusValues.radius C N h) (GaussianBalancedRadius.radius C N) :=
  GaussianEuclideanDistanceName.fraction_order _ _ _ _ (unit_positive _) (GaussianBalancedRadius.denominator_positive C N)
    (le_congr (mul_comm _ _) (.eqRefl _) (center_radius_cross C N h hPositive))

theorem positive_delta_radius (C N z : PTm n)
    (hPositive : Γ ⊢[PRAAx] le one (residualNumerator C z)) : Γ ⊢[PRAAx]
    bounded (GaussianMonicPositiveDecrease.positiveDelta N C z) (startingNumerator C N z) (startingDenominator C N z) := by
  have actualPositive := le_congr (.eqRefl _) (translated_residual C N z).eqSymm hPositive
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianMonicPositiveDecrease.radius_denominator_positive N C z) (starting_denominator_positive C N z)
    (center_radius_cross (translated C N z) N (GaussianDominantPlateau.center (translated C N z) N) actualPositive)
    (GaussianMonicPositiveDecrease.positive_delta_radius N C z)

theorem delta_zero (C N z : PTm n) (h0 : Γ ⊢[PRAAx] residualNumerator C z ≐ zero) : Γ ⊢[PRAAx]
    GaussianNonmonicRD.delta N C z ≐ qzero := GaussianMonicDescentBranch.branch_zero _ _ _ _ h0

theorem delta_positive (C N z : PTm n) (hPositive : Γ ⊢[PRAAx] le one (residualNumerator C z)) : Γ ⊢[PRAAx]
    GaussianNonmonicRD.delta N C z ≐ GaussianMonicPositiveDecrease.positiveDelta N C z :=
  (GaussianMonicDescentBranch.branch_positive _ _ _ _ hPositive).eqTrans
    (GaussianMonicPositiveDecrease.positive_delta_at N C z)

/-- This is unconditional, including degree zero and the zero polynomial. -/
theorem delta_radius (C N z : PTm n) : Γ ⊢[PRAAx]
    bounded (GaussianNonmonicRD.delta N C z) (startingNumerator C N z) (startingDenominator C N z) := by
  refine .orE (zero_or_succ (residualNumerator C z)) ?_ ?_
  · exact GaussianRationalReciprocal.bound_congr (delta_zero C N z Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianMonicResidualRadius.zero_bounded _ _ (starting_denominator_positive C N z))
  · have positive : (residualNumerator C z ≐ succ (PTm.pred (residualNumerator C z)))::Γ ⊢[PRAAx]
        le one (residualNumerator C z) := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact GaussianRationalReciprocal.bound_congr (delta_positive C N z positive).eqSymm (.eqRefl _) (.eqRefl _)
      (positive_delta_radius C N z positive)

theorem monic_delta_radius (C N z : PTm n) : Γ ⊢[PRAAx]
    bounded (GaussianMonicRD.delta N C z) (startingNumerator C N z) (startingDenominator C N z) := delta_radius C N z

def deltaF : PR 3 := GaussianMonicDescentBranch.branchDeltaF GaussianMonicRD.descent
theorem delta_program_at (N C z : PTm n) : Γ ⊢[PRAAx]
    ap3 deltaF N C z ≐ GaussianNonmonicRD.delta N C z := GaussianMonicDescentBranch.branch_at _ _ _ _
theorem program_delta_radius (C N z : PTm n) : Γ ⊢[PRAAx]
    bounded (ap3 deltaF N C z) (startingNumerator C N z) (startingDenominator C N z) :=
  GaussianRationalReciprocal.bound_congr (delta_program_at N C z).eqSymm (.eqRefl _) (.eqRefl _) (delta_radius C N z)

theorem advance_at (N C z : PTm n) : Γ ⊢[PRAAx]
    GaussianDescentClock.advance GaussianNonmonicRD.step N C z ≐ qadd z (ap3 deltaF N C z) :=
  (GaussianNonmonicRD.advance_at N C z).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (delta_program_at N C z).eqSymm)

theorem step_program_at (N C z : PTm n) : Γ ⊢[PRAAx]
    ap3 GaussianNonmonicRD.step N C z ≐ qadd z (ap3 deltaF N C z) :=
  (GaussianNonmonicRD.program_at N C z).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (delta_program_at N C z).eqSymm)

theorem actual_center_radius_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (GaussianBalancedRadiusSyntax.numerator (var 0) (var 1) zero) ⟶
      RationalArgmin.rationalLE (GaussianDominantRadiusValues.radius (var 0) (var 1) (var 2))
        (GaussianBalancedRadius.radius (var 0) (var 1))) :=
  closeUniv 3 (.impI (center_radius_bound _ _ _ Prf.hyp0))

theorem actual_starting_radius_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (bounded (GaussianNonmonicRD.delta (var 1) (var 0) (var 2))
      (startingNumerator (var 0) (var 1) (var 2)) (startingDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (delta_radius _ _ _)

theorem actual_starting_zero_branch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (residualNumerator (var 0) (var 2) ≐ zero ⟶
      ((GaussianNonmonicRD.delta (var 1) (var 0) (var 2) ≐ qzero) ⋏
        (startingNumerator (var 0) (var 1) (var 2) ≐ zero ⋏
          startingRadius (var 0) (var 1) (var 2) ≐ fraction zero one))) :=
  closeUniv 3 (.impI (.andI (delta_zero _ _ _ Prf.hyp0)
    (.andI (starting_numerator_zero _ _ _ Prf.hyp0) (starting_radius_zero _ _ _ Prf.hyp0))))

theorem actual_starting_radius_positive_denominator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (startingDenominator (var 0) (var 1) (var 2))) := closeUniv 3 (starting_denominator_positive _ _ _)

theorem actual_displacement_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 deltaF (var 0) (var 1) (var 2) ≐ GaussianNonmonicRD.delta (var 0) (var 1) (var 2)) ⋏
      ((ap3 GaussianNonmonicRD.step (var 0) (var 1) (var 2) ≐
          qadd (var 2) (ap3 deltaF (var 0) (var 1) (var 2))) ⋏
        (GaussianDescentClock.advance GaussianNonmonicRD.step (var 0) (var 1) (var 2) ≐
          qadd (var 2) (ap3 deltaF (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (delta_program_at _ _ _) (.andI (step_program_at _ _ _) (advance_at _ _ _)))

theorem actual_program_starting_radius_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (bounded (ap3 deltaF (var 1) (var 0) (var 2))
      (startingNumerator (var 0) (var 1) (var 2)) (startingDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (program_delta_radius _ _ _)

end LeanProofs.IPRA.Analysis.GaussianNonmonicDisplacementRadius

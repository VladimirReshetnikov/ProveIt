import GowersSzemeredi.Proofs18QuadraticDiscrepancy
import GowersSzemeredi.Proofs18BoundaryRefinement
import GowersSzemeredi.Proofs05Downstream

/-! Cubic inverse parameters retaining the stronger Fejer exponents 53 and 42.

`fejer_cubic_twisted_count_power` is in `Proofs18FejerCubicParametersSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Fraction of ambient mass retained when selecting cubic localization cells. -/
def fejerCubicLocalizedMassParameter (alpha : Real) : Real :=
  (2 : Real) ^ (-(59 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42)

/-- Common quadratic parameter in all the selected comparable prime models. -/
def fejerCubicLocalQuadraticParameter (alpha : Real) : Real :=
  (2 : Real) ^ (-(71 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42)

theorem fejerCubicLocalQuadraticParameter_pos {alpha : Real} (hα : 0 < alpha) :
    0 < fejerCubicLocalQuadraticParameter alpha := by
  unfold fejerCubicLocalQuadraticParameter
  positivity

theorem fejerCubicLocalQuadraticParameter_le_one {alpha : Real}
    (hα : 0 ≤ alpha) (hαone : alpha ≤ 1) : fejerCubicLocalQuadraticParameter alpha ≤ 1 := by
  have hs : alpha ^ 2 ≤ 1 := pow_le_one₀ hα hαone
  have hp : (alpha / 2) ^ ((2 : Nat) ^ 42) ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith)
  have hc : (2 : Real) ^ (-(71 : Int)) ≤ 1 := by norm_num
  exact (mul_le_mul (mul_le_mul hc hs (by positivity) zero_le_one) hp
    (by positivity) (by positivity)).trans (by norm_num)

def fejerCubicLocalizationExponent (alpha : Real) : Real :=
  (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))

def fejerCubicLocalCountExponent (alpha : Real) : Real :=
  quadraticDiscrepancyExponent (fejerCubicLocalQuadraticParameter alpha) / 16

def fejerCubicLocalCountConstant (alpha : Real) : Real :=
  max 1 (2 * boundaryRefinementConstant (1 / 16) * (8 : Real) ^ (1 - fejerCubicLocalCountExponent alpha))

def fejerCubicTwistedDiscrepancyParameter (alpha : Real) : Real :=
  fejerCubicLocalizedMassParameter alpha * quadraticDiscrepancyParameter (fejerCubicLocalQuadraticParameter alpha)

theorem fejerCubicLocalCountExponent_bounds {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < fejerCubicLocalCountExponent alpha ∧ fejerCubicLocalCountExponent alpha ≤ 1 := by
  have ha := fejerCubicLocalQuadraticParameter_pos hα
  have haone := fejerCubicLocalQuadraticParameter_le_one hα.le hαone
  obtain ⟨he, heone⟩ := quadratic_frequency_exponent_bounds ha haone
  dsimp [fejerCubicLocalCountExponent, quadraticDiscrepancyExponent]
  constructor <;> linarith

def fejerCubicDiscrepancyExponent (alpha : Real) : Real :=
  fejerCubicLocalizationExponent alpha * fejerCubicLocalCountExponent alpha /
    (2 * (polynomialPartitionConstant 3 : Real))

def fejerCubicDiscrepancyParameter (alpha : Real) : Real :=
  fejerCubicTwistedDiscrepancyParameter alpha / 2

def fejerCubicTwistedCountConstant (alpha : Real) : Real :=
  fejerCubicLocalCountConstant alpha * (12 : Real) ^ fejerCubicLocalCountExponent alpha

def fejerCubicPhaseRefinementConstant (alpha : Real) : Real :=
  section5LocalRefinementConstant 3 (fejerCubicTwistedDiscrepancyParameter alpha) *
    (fejerCubicTwistedCountConstant alpha) ^ (polynomialPartitionConstant 3 : Real)⁻¹

theorem fejerCubicDiscrepancyExponent_pos {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < fejerCubicDiscrepancyExponent alpha := by
  have ht := (fejerCubicLocalCountExponent_bounds hα hαone).1
  unfold fejerCubicDiscrepancyExponent fejerCubicLocalizationExponent polynomialPartitionConstant
  positivity

theorem fejerCubicDiscrepancyParameter_pos {alpha : Real} (hα : 0 < alpha) :
    0 < fejerCubicDiscrepancyParameter alpha := by
  have ha := fejerCubicLocalQuadraticParameter_pos hα
  unfold fejerCubicDiscrepancyParameter fejerCubicTwistedDiscrepancyParameter
    fejerCubicLocalizedMassParameter quadraticDiscrepancyParameter
  positivity

end LeanProofs.GowersSzemeredi

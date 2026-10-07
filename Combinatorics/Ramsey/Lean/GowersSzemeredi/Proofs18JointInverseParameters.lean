import GowersSzemeredi.Proofs17JointPowerLocalization
import GowersSzemeredi.Proofs18StructuralInverseParameters

/-! Recursive inverse parameters for the joint-cover localization route.
The current structural dimension is replaced by its preceding dimensions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Parameter passed to the lower-degree inverse theorem after localization. -/
def jointStructuralInverseLowerInput (alpha : Real) (k : Nat) : Real :=
  (jointPowerLocalizationParameter (structuralInverseInput alpha) k / 2) /
    (2 * (k + 3 : Nat) : Real) ^ (k + 3)

theorem jointStructuralInverseLowerInput_pos {alpha : Real} (hα : 0 < alpha) (k : Nat) :
    0 < jointStructuralInverseLowerInput alpha k := by
  have hp := jointPowerLocalizationParameter_pos (structuralInverseInput_pos hα) k
  unfold jointStructuralInverseLowerInput
  positivity

/-- Index n corresponds to uniformity degree n+2. All losses in discrepancy
are retained; the two base cases are the explicit quadratic and improved cubic bounds. -/
def jointStructuralInverseParameter : Nat → Real → Real
  | 0, alpha => quadraticDiscrepancyParameter (structuralInverseInput alpha)
  | 1, alpha => fejerCubicDiscrepancyParameter (structuralInverseInput alpha)
  | n + 2, alpha =>
      jointPowerLocalizationParameter (structuralInverseInput alpha) (n + 2) *
        jointStructuralInverseParameter (n + 1) (jointStructuralInverseLowerInput alpha (n + 2)) / 4

/-- The power of N retained by the recursive partition. Capping at one
ensures every induction step satisfies the local assembly's exponent range. -/
def jointStructuralInverseExponent : Nat → Real → Real
  | 0, alpha => min (quadraticDiscrepancyExponent (structuralInverseInput alpha)) 1
  | 1, alpha => min (fejerCubicDiscrepancyExponent (structuralInverseInput alpha)) 1
  | n + 2, alpha => min
      (inverseStepExponent (n + 3) (jointPowerLocalizationExponent (structuralInverseInput alpha) (n + 2))
        (jointStructuralInverseExponent (n + 1) (jointStructuralInverseLowerInput alpha (n + 2)))) 1

theorem jointStructuralInverseParameter_pos (n : Nat) {alpha : Real} (hα : 0 < alpha) :
    0 < jointStructuralInverseParameter n alpha := by
  induction n generalizing alpha with
  | zero =>
      have hp := structuralInverseInput_pos hα
      dsimp [jointStructuralInverseParameter, quadraticDiscrepancyParameter]
      positivity
  | succ n ih =>
    cases n with
    | zero => exact fejerCubicDiscrepancyParameter_pos (structuralInverseInput_pos hα)
    | succ n =>
      have hp := jointPowerLocalizationParameter_pos (structuralInverseInput_pos hα) (n + 2)
      have hb := ih (jointStructuralInverseLowerInput_pos hα (n + 2))
      simpa only [jointStructuralInverseParameter] using div_pos (mul_pos hp hb) (by norm_num : (0 : Real) < 4)

theorem jointStructuralInverseExponent_pos (n : Nat) {alpha : Real} (hα : 0 < alpha) :
    0 < jointStructuralInverseExponent n alpha := by
  induction n generalizing alpha with
  | zero =>
      have he := (quadratic_frequency_exponent_bounds (structuralInverseInput_pos hα)
        ((min_le_right _ _).trans (by norm_num : (1 : Real) / 2 ≤ 1))).1
      exact lt_min (div_pos he (by norm_num)) zero_lt_one
  | succ n ih =>
    cases n with
    | zero =>
      exact lt_min (fejerCubicDiscrepancyExponent_pos (structuralInverseInput_pos hα)
        ((min_le_right _ _).trans (by norm_num : (1 : Real) / 2 ≤ 1))) zero_lt_one
    | succ n =>
      have hs := ih (jointStructuralInverseLowerInput_pos hα (n + 2))
      have he := jointPowerLocalizationExponent_pos (by omega : 0 < n + 2) (structuralInverseInput_pos hα) (min_le_right _ _)
      have hK : (0 : Real) < polynomialPartitionConstant (n + 3 + 1) := by
        unfold polynomialPartitionConstant
        positivity
      apply lt_min _ zero_lt_one
      dsimp [inverseStepExponent, phaseInverseExponent]
      positivity

theorem jointStructuralInverseExponent_le_one (n : Nat) (alpha : Real) :
    jointStructuralInverseExponent n alpha ≤ 1 := by
  cases n with
  | zero => exact min_le_right _ _
  | succ n => cases n <;> exact min_le_right _ _

end LeanProofs.GowersSzemeredi

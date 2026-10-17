import GowersSzemeredi.Proofs13UniformSquareExtraction
import GowersSzemeredi.Proofs13FejerFrequencyGraph

/-! Propagate the purified frequency density into square extraction.
The explicit exponent comparison is performed in the next module.

`theorem_13_12_fejer_extraction_explicit` and
`theorem_13_12_with_fejer_extraction_exponent` are in
`Proofs13FejerFourierExtractionSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The purified density implies a stronger Fourier-set density bound. -/
theorem section13_fejer_square_density {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (alpha / 2) ^ ((2 : Nat) ^ 42) ≤
      (2 : Real) ^ (-(137 : Int)) * ((alpha / 2) ^ (4207554485 : Nat)) ^ 704 := by
  let a := alpha / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hahalf : a ≤ 1 / 2 := by dsimp [a]; linarith only [hαone]
  have haone : a ≤ 1 := hahalf.trans (by norm_num)
  have hc : a ^ 137 ≤ (2 : Real) ^ (-(137 : Int)) := by
    calc
      _ ≤ (1 / 2 : Real) ^ 137 := pow_le_pow_left₀ ha.le hahalf _
      _ = _ := by norm_num
  calc
    _ ≤ a ^ (137 + (4207554485 : Nat) * 704) :=
      pow_le_pow_of_le_one ha.le haone (by norm_num)
    _ = a ^ 137 * (a ^ (4207554485 : Nat)) ^ 704 := by rw [pow_add, pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

def section13FourierThreshold (alpha : Real) : Real :=
  max (section13FrequencyGraphThreshold alpha)
    (section13GeometricThreshold ((alpha / 2) ^ (4207554485 : Nat)))

end LeanProofs.GowersSzemeredi

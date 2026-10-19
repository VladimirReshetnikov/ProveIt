import GowersSzemeredi.Proofs13SquareScale
import GowersSzemeredi.Proofs13AllDensityExtraction

/-! A direct large-N common-step bilinear square theorem from the original
Section 13 context, retaining an explicit positive power of N.

`section13_complete_square_extraction_all_densities` is in
`Proofs13CompleteSquareExtractionSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
open Filter
namespace LeanProofs.GowersSzemeredi

/-- The explicit exponent retained by the complete square construction. -/
def section13SquareExponent (alpha : Real) : Real :=
  ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) *
    ((2 : Real) ^ (-(100 : Int)) * alpha ^ 448) *
    cor711Exponent ((2 : Real) ^ (-(135 : Int)) * alpha ^ 704) 1 / 4

set_option exponentiation.threshold 512 in
/-- Closed form of the positive power retained after all floor and square
losses, with the corrected upstream coefficient exponents. -/
theorem section13SquareExponent_formula (alpha : Real) :
    section13SquareExponent alpha =
      (2 : Real) ^ (-(386 : Int)) * alpha ^ 1856 /
        (2 : Real) ^ (13 * section13Q alpha) := by
  unfold section13SquareExponent
  rw [stage139_partition_exponent]
  norm_num [zpow_neg]
  ring

end LeanProofs.GowersSzemeredi

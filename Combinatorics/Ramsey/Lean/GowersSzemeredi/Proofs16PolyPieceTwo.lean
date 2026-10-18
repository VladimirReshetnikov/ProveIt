import GowersSzemeredi.Proofs16PolyPieceTwoInputs
import GowersSzemeredi.Proofs16PieceCoverWithRemainder
import GowersSzemeredi.Proofs16RoundedPowerWidth

/-! This module keeps `appendCoordinate_init_add`; the rest of the development, with
its description, is in `Proofs16PolyPieceTwoSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem appendCoordinate_init_add {N : Nat} (z : Point N 2) (x0 : Point N 1) :
    appendCoordinate (section16Init z + x0) (section16Last z) = z + appendCoordinate x0 0 := by
  conv_rhs => rw [← appendCoordinate_init_last z]
  rw [appendCoordinate_add, add_zero]

end LeanProofs.GowersSzemeredi

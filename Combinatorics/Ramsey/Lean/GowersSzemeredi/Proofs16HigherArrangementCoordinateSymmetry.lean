import GowersSzemeredi.Proofs16HigherArrangementGenerators

/-! Every endpoint can occupy the first position through a bijective
reparametrization preserving the higher-arrangement equation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementCoordinateSymmetry (N : Nat) (i : Fin 16) : HigherArrangementSymmetry N :=
  ![(HigherArrangementSymmetry.refl N),
    (higherArrangementReverse N),
    (higherArrangementAdjacent N),
    ((higherArrangementAdjacent N).trans (higherArrangementReverse N)),
    (higherArrangementHalf N),
    ((higherArrangementHalf N).trans (higherArrangementReverse N)),
    ((higherArrangementHalf N).trans (higherArrangementAdjacent N)),
    (((higherArrangementHalf N).trans (higherArrangementAdjacent N)).trans (higherArrangementReverse N)),
    (higherArrangementSides N),
    ((higherArrangementSides N).trans (higherArrangementReverse N)),
    ((higherArrangementSides N).trans (higherArrangementAdjacent N)),
    (((higherArrangementSides N).trans (higherArrangementAdjacent N)).trans (higherArrangementReverse N)),
    ((higherArrangementSides N).trans (higherArrangementHalf N)),
    (((higherArrangementSides N).trans (higherArrangementHalf N)).trans (higherArrangementReverse N)),
    (((higherArrangementSides N).trans (higherArrangementHalf N)).trans (higherArrangementAdjacent N)),
    ((((higherArrangementSides N).trans (higherArrangementHalf N)).trans (higherArrangementAdjacent N)).trans (higherArrangementReverse N))] i

theorem higherArrangementCoordinateSymmetry_zero (N : Nat) (i : Fin 16) :
    (higherArrangementCoordinateSymmetry N i).coordinates 0 = i := by
  fin_cases i <;> rfl

end LeanProofs.GowersSzemeredi

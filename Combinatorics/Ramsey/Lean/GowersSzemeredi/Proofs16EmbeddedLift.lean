import GowersSzemeredi.Proofs16PrefixLift
import GowersSzemeredi.Proofs16PermutedCovers
import Mathlib.Logic.Equiv.Fintype

/-! Extension from any embedded set of coordinate directions. Permutation
invariance turns the iterated prefix extension into an ambient face cover.

`MultiplyLinearFunction.lift_embedding` is in `Proofs16EmbeddedLiftSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def selectedCoordinates {N l d : Nat} (f : Fin l ↪ Fin d) (z : Point N d) : Point N l :=
  fun i => z (f i)

def selectedDomain {N l d : Nat} [NeZero N] (f : Fin l ↪ Fin d)
    (B : Finset (Point N l)) : Finset (Point N d) :=
  Finset.univ.filter (fun z => selectedCoordinates f z ∈ B)

@[simp] theorem mem_selectedDomain {N l d : Nat} [NeZero N]
    (f : Fin l ↪ Fin d) (B : Finset (Point N l)) (z : Point N d) :
    z ∈ selectedDomain f B ↔ selectedCoordinates f z ∈ B := by
  simp [selectedDomain]

end LeanProofs.GowersSzemeredi

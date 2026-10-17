import GowersSzemeredi.Definitions

/-! Iterated extension across unused final coordinates. The zero-dimensional
case uses a constant graph, so the result includes every proper face dimension.

`MultiplyLinearFunction.lift_prefix` is in `Proofs16PrefixLiftSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coordinatePrefix {N l d : Nat} (h : l ≤ d) (z : Point N d) : Point N l :=
  fun i => z (i.castLE h)

@[simp] theorem coordinatePrefix_self {N d : Nat} (h : d ≤ d) (z : Point N d) :
    coordinatePrefix h z = z := by
  funext i
  rfl

def prefixDomain {N l d : Nat} [NeZero N] (h : l ≤ d) (B : Finset (Point N l)) :
    Finset (Point N d) := Finset.univ.filter (fun z => coordinatePrefix h z ∈ B)

@[simp] theorem mem_prefixDomain {N l d : Nat} [NeZero N]
    (h : l ≤ d) (B : Finset (Point N l)) (z : Point N d) :
    z ∈ prefixDomain h B ↔ coordinatePrefix h z ∈ B := by
  simp [prefixDomain]

end LeanProofs.GowersSzemeredi

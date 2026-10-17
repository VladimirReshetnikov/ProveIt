import GowersSzemeredi.Definitions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Dist
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.Coprime.Lemmas

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

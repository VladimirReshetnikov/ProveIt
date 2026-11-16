import KIFC.GraphBlueprint
import IPRADerivations.Geometry.TriangleFormulas

/-!
# Adapter examples for inherited checked algebraic derivations
-/

namespace LeanProofs.KIFC.Examples

open LeanProofs.ConciseIPRA
open LeanProofs.KIFC
open LeanProofs.IPRA
open scoped Fm

namespace TF := LeanProofs.IPRA.Geometry.TriangleFormulas

/-- The checked open two-square derivation packaged as a KIFC local rule. -/
def twoSquaresRule : KernelRule 8 where
  premises := []
  conclusion := TF.twoSquaresFormula
  sound := TF.twoSquares_open

/-- Public theorem recovered from the rule. -/
theorem twoSquaresFromRule :
    ([] : List (Fm PTm 8)) ⊢[PRAAx] TF.twoSquaresFormula :=
  twoSquaresRule.sound

/-- The checked open coordinate Heron derivation packaged as a local rule. -/
def heronRule : KernelRule 12 where
  premises := []
  conclusion := TF.heronFormula
  sound := by
    unfold TF.heronFormula TF.D TF.A TF.B TF.C
    ipra_ring

end LeanProofs.KIFC.Examples

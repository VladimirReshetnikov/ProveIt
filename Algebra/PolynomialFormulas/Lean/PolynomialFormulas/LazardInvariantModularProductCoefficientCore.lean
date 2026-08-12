import PolynomialFormulas.LazardInvariantModularProductBridgeCore
import Mathlib.Tactic

/-! Lightweight executable coefficient formula for product-row shards. -/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open scoped BigOperators
open Finset
open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

def subsetExponent (t : Finset (Fin 6)) : Exponent :=
  fun i => if i ∈ t then 1 else 0

/-- Coefficient of a target exponent in `e_d` times a cyclic orbit sum,
expressed only with executable finite data and plain function equality. -/
def semanticProductCoefficient (source : Exponent) (d : ℕ)
    (target : Exponent) : F3 :=
  ∑ a ∈ cyclicOrbitSupport source,
    ∑ t ∈ powersetCard d (univ : Finset (Fin 6)),
      if addExponent (subsetExponent t) a = target then 1 else 0

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

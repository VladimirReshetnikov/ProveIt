import PolynomialFormulas.LazardInvariantModularOrbitCoordinates
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic

/-! Shared definitions for separately compiled modular product-row certificates. -/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open scoped BigOperators
open Finset MvPolynomial
open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

noncomputable section

/-- The actual elementary-symmetric product represented by source row `i`. -/
def degreeSevenLiteralProduct (i : Fin 159) :
    MvPolynomial (Fin 6) F3 :=
  MvPolynomial.esymm (Fin 6) F3 (degreeSevenProductSource i).1 *
    cyclicOrbitPolynomial (degreeSevenProductSource i).2

/-- The polynomial obtained by interpreting every entry of encoded row `i`
as a coefficient of the corresponding cyclic orbit sum. -/
def degreeSevenEncodedProduct (i : Fin 159) :
    MvPolynomial (Fin 6) F3 :=
  ∑ j : Fin 132,
    (degreeSevenProductRow i j) • degreeSevenOrbitPolynomial j

/-- The executable finite-sum encoding agrees with the abstract coordinate
linear map. -/
theorem degreeSevenEncodedProduct_eq_coordinateMap (i : Fin 159) :
    degreeSevenEncodedProduct i =
      degreeSevenOrbitCoordinateMap (degreeSevenProductRow i) := by
  rw [degreeSevenOrbitCoordinateMap, Fintype.linearCombination_apply]
  rfl

/-! ## Shared orbit-module definitions

These definitions live in the proof-free product core so that the semantic
cyclic-invariant reconstruction can be compiled before the finite product-row
certificates. -/

/-- Canonical orbit representatives in a specified degree, packaged with
their membership proof. -/
abbrev OrbitRepresentative (degree : ℕ) :=
  {a : Exponent // a ∈ (orbitRepresentatives degree).toFinset}

/-- The subspace spanned by all cyclic orbit sums in a specified degree. -/
def cyclicOrbitSumSubspace (degree : ℕ) :
    Submodule F3 (MvPolynomial (Fin 6) F3) :=
  Submodule.span F3
    (Set.range fun a : OrbitRepresentative degree =>
      cyclicOrbitPolynomial a.1)

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

import PolynomialFormulas.LazardInvariantModularCounterexampleData
import Mathlib.Tactic

/-!
# Core definitions for the modular C6 orbit coordinates

This module contains the shared definitions used by the separately compiled
finite separation certificates.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularOrbitCoordinates

open scoped BigOperators
open Finset MvPolynomial
open LazardInvariantModularCounterexample

set_option autoImplicit false

noncomputable section

/-- The finite support of the cyclic orbit of an exponent vector. -/
def cyclicOrbitSupport (a : Exponent) : Finset Exponent :=
  (cyclicOrbit a).toFinset

/-- The literal polynomial obtained by summing all distinct monomials in one
cyclic orbit. -/
def cyclicOrbitPolynomial (a : Exponent) :
    MvPolynomial (Fin 6) F3 :=
  ∑ d ∈ cyclicOrbitSupport a,
    monomial (Finsupp.equivFunOnFinite.symm d) 1

theorem coeff_cyclicOrbitPolynomial (a d : Exponent) :
    (cyclicOrbitPolynomial a).coeff
        (Finsupp.equivFunOnFinite.symm d) =
      if d ∈ cyclicOrbitSupport a then 1 else 0 := by
  classical
  simp [cyclicOrbitPolynomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]

def degreeSevenRepresentativeList : List Exponent := [
  ![7, 0, 0, 0, 0, 0],
  ![1, 6, 0, 0, 0, 0],
  ![2, 5, 0, 0, 0, 0],
  ![3, 4, 0, 0, 0, 0],
  ![4, 3, 0, 0, 0, 0],
  ![5, 2, 0, 0, 0, 0],
  ![6, 1, 0, 0, 0, 0],
  ![1, 0, 6, 0, 0, 0],
  ![1, 1, 5, 0, 0, 0],
  ![1, 2, 4, 0, 0, 0],
  ![1, 3, 3, 0, 0, 0],
  ![1, 4, 2, 0, 0, 0],
  ![1, 5, 1, 0, 0, 0],
  ![2, 0, 5, 0, 0, 0],
  ![2, 1, 4, 0, 0, 0],
  ![2, 2, 3, 0, 0, 0],
  ![2, 3, 2, 0, 0, 0],
  ![2, 4, 1, 0, 0, 0],
  ![3, 0, 4, 0, 0, 0],
  ![3, 1, 3, 0, 0, 0],
  ![3, 2, 2, 0, 0, 0],
  ![3, 3, 1, 0, 0, 0],
  ![4, 0, 3, 0, 0, 0],
  ![4, 1, 2, 0, 0, 0],
  ![4, 2, 1, 0, 0, 0],
  ![5, 0, 2, 0, 0, 0],
  ![5, 1, 1, 0, 0, 0],
  ![6, 0, 1, 0, 0, 0],
  ![6, 0, 0, 1, 0, 0],
  ![1, 0, 1, 5, 0, 0],
  ![1, 0, 2, 4, 0, 0],
  ![1, 0, 3, 3, 0, 0],
  ![1, 0, 4, 2, 0, 0],
  ![1, 0, 5, 1, 0, 0],
  ![1, 1, 0, 5, 0, 0],
  ![1, 1, 1, 4, 0, 0],
  ![1, 1, 2, 3, 0, 0],
  ![1, 1, 3, 2, 0, 0],
  ![1, 1, 4, 1, 0, 0],
  ![1, 2, 0, 4, 0, 0],
  ![1, 2, 1, 3, 0, 0],
  ![1, 2, 2, 2, 0, 0],
  ![1, 2, 3, 1, 0, 0],
  ![1, 3, 0, 3, 0, 0],
  ![1, 3, 1, 2, 0, 0],
  ![1, 3, 2, 1, 0, 0],
  ![1, 4, 0, 2, 0, 0],
  ![1, 4, 1, 1, 0, 0],
  ![1, 5, 0, 1, 0, 0],
  ![5, 0, 0, 2, 0, 0],
  ![2, 0, 1, 4, 0, 0],
  ![2, 0, 2, 3, 0, 0],
  ![2, 0, 3, 2, 0, 0],
  ![2, 0, 4, 1, 0, 0],
  ![2, 1, 0, 4, 0, 0],
  ![2, 1, 1, 3, 0, 0],
  ![2, 1, 2, 2, 0, 0],
  ![2, 1, 3, 1, 0, 0],
  ![2, 2, 0, 3, 0, 0],
  ![2, 2, 1, 2, 0, 0],
  ![2, 2, 2, 1, 0, 0],
  ![2, 3, 0, 2, 0, 0],
  ![2, 3, 1, 1, 0, 0],
  ![2, 4, 0, 1, 0, 0],
  ![4, 0, 0, 3, 0, 0],
  ![3, 0, 1, 3, 0, 0],
  ![3, 0, 2, 2, 0, 0],
  ![3, 0, 3, 1, 0, 0],
  ![3, 1, 0, 3, 0, 0],
  ![3, 1, 1, 2, 0, 0],
  ![3, 1, 2, 1, 0, 0],
  ![3, 2, 0, 2, 0, 0],
  ![3, 2, 1, 1, 0, 0],
  ![3, 3, 0, 1, 0, 0],
  ![4, 0, 1, 2, 0, 0],
  ![4, 0, 2, 1, 0, 0],
  ![4, 1, 0, 2, 0, 0],
  ![4, 1, 1, 1, 0, 0],
  ![4, 2, 0, 1, 0, 0],
  ![5, 0, 1, 1, 0, 0],
  ![5, 1, 0, 1, 0, 0],
  ![5, 0, 1, 0, 1, 0],
  ![1, 1, 4, 0, 1, 0],
  ![1, 2, 3, 0, 1, 0],
  ![1, 3, 2, 0, 1, 0],
  ![1, 4, 1, 0, 1, 0],
  ![2, 0, 4, 0, 1, 0],
  ![2, 1, 3, 0, 1, 0],
  ![2, 2, 2, 0, 1, 0],
  ![2, 3, 1, 0, 1, 0],
  ![3, 0, 3, 0, 1, 0],
  ![3, 1, 2, 0, 1, 0],
  ![3, 2, 1, 0, 1, 0],
  ![4, 0, 2, 0, 1, 0],
  ![4, 1, 1, 0, 1, 0],
  ![1, 4, 0, 1, 1, 0],
  ![2, 3, 0, 1, 1, 0],
  ![3, 2, 0, 1, 1, 0],
  ![4, 1, 0, 1, 1, 0],
  ![4, 0, 1, 1, 1, 0],
  ![1, 1, 1, 1, 3, 0],
  ![1, 1, 1, 2, 2, 0],
  ![1, 1, 1, 3, 1, 0],
  ![3, 0, 1, 1, 2, 0],
  ![1, 1, 2, 1, 2, 0],
  ![1, 1, 2, 2, 1, 0],
  ![1, 1, 3, 0, 2, 0],
  ![1, 1, 3, 1, 1, 0],
  ![1, 3, 0, 1, 2, 0],
  ![2, 2, 0, 1, 2, 0],
  ![1, 2, 0, 3, 1, 0],
  ![3, 0, 1, 2, 1, 0],
  ![1, 2, 1, 1, 2, 0],
  ![1, 2, 1, 2, 1, 0],
  ![1, 2, 2, 0, 2, 0],
  ![1, 2, 2, 1, 1, 0],
  ![1, 3, 0, 2, 1, 0],
  ![2, 0, 1, 3, 1, 0],
  ![1, 3, 1, 1, 1, 0],
  ![3, 0, 2, 0, 2, 0],
  ![2, 1, 2, 0, 2, 0],
  ![2, 0, 2, 2, 1, 0],
  ![2, 0, 3, 1, 1, 0],
  ![2, 2, 0, 2, 1, 0],
  ![3, 1, 0, 2, 1, 0],
  ![3, 0, 2, 1, 1, 0],
  ![2, 1, 1, 1, 2, 0],
  ![2, 1, 1, 2, 1, 0],
  ![2, 1, 2, 1, 1, 0],
  ![2, 2, 1, 1, 1, 0],
  ![3, 1, 1, 1, 1, 0],
  ![2, 1, 1, 1, 1, 1]
]

/-- The `i`th canonical representative in the exact order used by the
degree-seven dual certificate.  A separately compiled bridge identifies this
literal list with `orbitRepresentatives 7`. -/
def degreeSevenRepresentative (i : Fin 132) : Exponent :=
  degreeSevenRepresentativeList.getD i.1 (fun _ => 0)

/-- The actual orbit-sum polynomial represented by coordinate `i`. -/
def degreeSevenOrbitPolynomial (i : Fin 132) :
    MvPolynomial (Fin 6) F3 :=
  cyclicOrbitPolynomial (degreeSevenRepresentative i)

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularOrbitCoordinates

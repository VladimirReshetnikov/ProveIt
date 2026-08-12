import PolynomialFormulas.LazardInvariantModularCyclicInvariants
import Mathlib.Tactic

/-! Coefficientwise reconstruction of fixed homogeneous degree-seven polynomials. -/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants

open scoped BigOperators
open Finset MvPolynomial
open LazardInvariantModularCounterexample
open LazardInvariantModularOrbitCoordinates
open LazardInvariantModularProductBridge

set_option autoImplicit false

noncomputable section

def degreeSevenOrbitReconstruction (p : MvPolynomial (Fin 6) F3) :
    MvPolynomial (Fin 6) F3 :=
  ∑ r : OrbitRepresentative 7,
    p.coeff (Finsupp.equivFunOnFinite.symm r.1) •
      cyclicOrbitPolynomial r.1

theorem degreeSevenOrbitReconstruction_eq
    (p : MvPolynomial (Fin 6) F3)
    (hhomogeneous : p.IsHomogeneous 7)
    (hfixed : cycleSixRenameLinear p = p) :
    degreeSevenOrbitReconstruction p = p := by
  change orbitReconstruction 7 p = p
  exact orbitReconstruction_eq (7 : Fin 8) p hhomogeneous hfixed

end


end LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants

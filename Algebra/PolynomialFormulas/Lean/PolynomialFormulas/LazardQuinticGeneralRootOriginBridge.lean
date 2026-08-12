import PolynomialFormulas.LazardQuinticGeneralSolvabilityTransport
import PolynomialFormulas.LazardQuinticRootOriginBridge

/-!
# Root-origin invariants for a general rational quintic

The affine Tschirnhaus and irreducibility transport is provided independently
by `LazardQuinticGeneralSolvabilityTransport`.  This module composes it with
the depressed root-origin construction for an arbitrary general rational
quintic.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open ComputableDummitCoefficients

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

/-- Root-origin Lazard invariants for an arbitrary irreducible rational
quintic with nonzero leading coefficient.  The roots are those of its monic
depressed translate, the polynomial to which Lazard's formula applies. -/
theorem exists_depressed_rootOrdering_and_rational_invariants
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial)
    (hq : ∃ q : ℚ, (resolventPolynomial (depress c)).IsRoot q) :
    ∃ (x : Fin 5 → (depress c).polynomial.SplittingField)
        (j : Invariants ℚ),
      Function.Injective x ∧
      elementaryTuple x = depressedElementary
        ((depress c).map
          (algebraMap ℚ (depress c).polynomial.SplittingField)) ∧
      InvariantRelations (depress c) j ∧
      j.map (algebraMap ℚ (depress c).polynomial.SplittingField) =
        rootInvariants x ∧
      ∀ omega : FifthRootOfUnity (depress c).polynomial.SplittingField,
        rootEpsilon omega x ≠ 0 := by
  exact exists_rootOrdering_and_rational_invariants (depress c)
    ((irreducible_polynomial_iff_depress_polynomial c ha).mp hp) hq

end

end LeanProofs.PolynomialFormulas.LazardQuintic

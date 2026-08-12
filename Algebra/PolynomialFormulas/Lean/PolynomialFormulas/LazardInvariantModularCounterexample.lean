import PolynomialFormulas.LazardInvariantModularOrbitCount
import PolynomialFormulas.LazardInvariantNonmodularBasis

/-!
# The modular obstruction to Lazard's unrestricted Theorem 2

Lazard states the invariant-module theorem without excluding modular
characteristics.  This file constructs the literal finite data used for a
small obstruction in characteristic three.  Let the regular cyclic group
`C₆` rotate six variables.  There are 132 degree-seven cyclic monomial
orbits and 159 products `eᵢ · (lower-degree orbit sum)`.

The executable eliminator below returns 115 pivots, hence the diagnostic
number `132 - 115 = 17`; those expensive executable checks live in the
non-library diagnostic file
`Tools/LazardInvariantModularCounterexampleDiagnostics.lean`.  Those two
computations alone are deliberately not called a theorem about matrix rank:
this file does not prove correctness of the eliminator.  The separate file
`LazardInvariantModularDualCertificate` supplies the rigorous statement
actually needed later, by exhibiting 17 independent quotient classes without
using the eliminator at all.

A graded free module over `𝔽₃[e₁,…,e₆]` with the Hilbert series of these
permutation invariants would instead have exactly 16 degree-seven basis
generators.

The imported lightweight `LazardInvariantNonmodularBasis` module gives the
uniform repair used by the formalization: if the subgroup order is nonzero
(equivalently invertible) in the ground field, Reynolds averaging constructs
the claimed basis.  This is a sufficient hypothesis, not a claim of
necessity for every individual modular action.  Characteristic zero is a
convenient sufficient specialization, but is not logically necessary.
-/

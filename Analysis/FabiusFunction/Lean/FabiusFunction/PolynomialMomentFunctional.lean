import FabiusFunction.FinitePolynomialFunctional

/-!
# Compatibility import for finite polynomial moment functionals

The canonical implementation now lives in `FinitePolynomialFunctional`,
which combines its arbitrary-selected-coefficient and constant-coefficient
API with the degree-valued top-moment and strict-annihilation API originally
introduced through this module.  This compatibility import preserves the
module path for clients while keeping a single source of theorem proofs.
-/

set_option autoImplicit false

import PolynomialFormulas.LazardInvariantModularCounterexampleData
import Mathlib.Tactic

/-!
# The finite degree-seven orbit count

This module isolates the expensive kernel reduction used by the modular
counterexample.  Downstream algebraic modules can depend on its checked
theorem without recompiling the computation when the lightweight wrapper or
the independent nonmodular repair changes.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularCounterexample

open scoped BigOperators
open Finset MvPolynomial

set_option autoImplicit false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem cyclicSix_degreeSeven_orbit_count :
    invariantOrbitCount 7 = 132 := by decide

end LeanProofs.PolynomialFormulas.LazardInvariantModularCounterexample

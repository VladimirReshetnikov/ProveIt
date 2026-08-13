import PolynomialFormulas.LazardInvariantModularOrbitCount
import Mathlib.Tactic

/-!
# Low-degree orbit counts for the modular homogeneous-basis obstruction

These closed kernel computations are isolated because the degree-six count
is substantially more expensive than the semantic Hilbert-series arguments
which consume it.  Compiling this module once prevents every edit to those
arguments from replaying the same finite enumeration.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularHomogeneousBasisObstruction

open LeanProofs.PolynomialFormulas.LazardInvariantModularCounterexample

set_option autoImplicit false

@[simp]
theorem invariantOrbitCount_zero : invariantOrbitCount 0 = 1 := by decide

@[simp]
theorem invariantOrbitCount_one : invariantOrbitCount 1 = 1 := by decide

@[simp]
theorem invariantOrbitCount_two : invariantOrbitCount 2 = 4 := by decide

@[simp]
theorem invariantOrbitCount_three : invariantOrbitCount 3 = 10 := by decide

@[simp]
theorem invariantOrbitCount_four : invariantOrbitCount 4 = 22 := by decide

@[simp]
theorem invariantOrbitCount_five : invariantOrbitCount 5 = 42 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
@[simp]
theorem invariantOrbitCount_six : invariantOrbitCount 6 = 80 := by decide

end LeanProofs.PolynomialFormulas.LazardInvariantModularHomogeneousBasisObstruction

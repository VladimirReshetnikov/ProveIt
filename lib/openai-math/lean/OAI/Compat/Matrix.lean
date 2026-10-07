/-
Added for ProveIt (not an upstream file; distributed with this directory under
the same Apache-2.0 license). Backport of declarations that the upstream
library uses from its newer toolchain (Lean v4.34.1, Mathlib d13f23b7) but that
are absent from this repository's Lean 4.32.0 / Mathlib v4.32.0. Statements
are the upstream ones. Delete when the toolchain is upgraded.
-/
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false

namespace Matrix

alias det_of_isUpperTriangular := det_of_upperTriangular

end Matrix

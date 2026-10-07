/-
Added for ProveIt (not an upstream file; distributed with this directory under
the same Apache-2.0 license). Backport of declarations that the upstream
library uses from its newer toolchain (Lean v4.34.1, Mathlib d13f23b7) but that
are absent from this repository's Lean 4.32.0 / Mathlib v4.32.0. Statements
are the upstream ones. Delete when the toolchain is upgraded.
-/
import Mathlib.Analysis.CStarAlgebra.Basic

set_option autoImplicit false

@[simp]
theorem dist_star_star {E : Type*} [SeminormedAddCommGroup E] [StarAddMonoid E]
    [NormedStarGroup E] (x y : E) : dist (star x) (star y) = dist x y :=
  star_isometry.dist_eq x y

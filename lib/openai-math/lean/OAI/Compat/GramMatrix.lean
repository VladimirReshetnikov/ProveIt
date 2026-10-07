/-
Added for ProveIt (not an upstream file; distributed under Apache-2.0).
The Gram-matrix characterization of orthonormality, proved locally from
matrix extensionality and the existing orthonormal_iff_ite theorem.
-/
import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false

theorem Matrix.gram_eq_one_iff_orthonormal {𝕜 n E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] [DecidableEq n]
    {v : n → E} : Matrix.gram 𝕜 v = 1 ↔ Orthonormal 𝕜 v := by
  rw [orthonormal_iff_ite]
  constructor
  · intro h i j
    simpa only [Matrix.gram_apply, Matrix.one_apply] using congrFun (congrFun h i) j
  · intro h
    exact Matrix.ext h

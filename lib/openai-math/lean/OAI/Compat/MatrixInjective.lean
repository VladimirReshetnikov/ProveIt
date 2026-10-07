/-
Added for ProveIt (not an upstream file; distributed under Apache-2.0).
Matrix injectivity from a nonzero determinant, using Mathlib v4.32.0's
trivial-kernel theorem. This proof is local; no upstream proof text is copied.
-/
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

set_option autoImplicit false

theorem Matrix.mulVec_injective_of_det_ne_zero {n R : Type*} [Fintype n]
    [DecidableEq n] [CommRing R] [NoZeroDivisors R] {A : Matrix n n R}
    (hA : A.det ≠ 0) : Function.Injective A.mulVec := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hA
  rw [Matrix.mulVec_sub, hxy, sub_self]

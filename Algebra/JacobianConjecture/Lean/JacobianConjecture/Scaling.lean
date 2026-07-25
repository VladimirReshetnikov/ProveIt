import JacobianConjecture.Equivariance
import Mathlib.Tactic.FieldSimp

/-!
# The weighted torus action behind the discrete symmetry

Alpöge's map is homogeneous for the grading `weight (x, y, z) = (-1, 1, 2)`:
for every nonzero scalar `s`,

```text
F (x / s, s y, s² z) = (s² P, s Q, R / s).
```

The flip involutions of `Equivariance` are the `s = -1` instance, and
`CollisionFamily` derives the rational one-parameter family of collisions
as the orbit of the mirrored integral collision under this action.
-/

namespace LeanProofs.JacobianCounterexample

open Matrix MvPolynomial PolynomialMap

universe u

/-- The weight `(-1, 1, 2)` source action. -/
def scaleSource {R : Type u} [Field R] (s : R) (p : I → R) : I → R :=
  ![p 0 / s, s * p 1, s ^ 2 * p 2]

/-- The weight `(2, 1, -1)` target action. -/
def scaleTarget {R : Type u} [Field R] (s : R) (v : I → R) : I → R :=
  ![s ^ 2 * v 0, s * v 1, v 2 / s]

set_option maxHeartbeats 800000 in
/-- **Weighted homogeneity.** `F (x/s, sy, s²z) = (s²P, sQ, R/s)`. -/
theorem counterexample_scaling
    {R : Type u} [Field R] (s : R) (hs : s ≠ 0) (p : I → R) :
    evalMap (counterexample R) (scaleSource s p) =
      scaleTarget s (evalMap (counterexample R) p) := by
  funext i
  fin_cases i <;>
    simp [evalMap, counterexample, scaleSource, scaleTarget] <;>
    field_simp

/-- Scaling preserves collisions. -/
theorem collision_scaling
    {R : Type u} [Field R] (s : R) (hs : s ≠ 0) (p q : I → R)
    (h : evalMap (counterexample R) p = evalMap (counterexample R) q) :
    evalMap (counterexample R) (scaleSource s p) =
      evalMap (counterexample R) (scaleSource s q) := by
  rw [counterexample_scaling s hs, counterexample_scaling s hs, h]

/-- The source action composes multiplicatively. -/
theorem scaleSource_comp {R : Type u} [Field R] (a b : R) (p : I → R) :
    scaleSource a (scaleSource b p) = scaleSource (a * b) p := by
  funext i
  fin_cases i <;>
    simp [scaleSource] <;>
    ring

/-- The target action composes multiplicatively. -/
theorem scaleTarget_comp {R : Type u} [Field R] (a b : R) (v : I → R) :
    scaleTarget a (scaleTarget b v) = scaleTarget (a * b) v := by
  funext i
  fin_cases i <;>
    simp [scaleTarget] <;>
    ring

/-- The source action fixes everything at `s = 1`. -/
theorem scaleSource_one {R : Type u} [Field R] (p : I → R) :
    scaleSource 1 p = p := by
  funext i
  fin_cases i <;>
    simp [scaleSource]

/-- The target action fixes everything at `s = 1`. -/
theorem scaleTarget_one {R : Type u} [Field R] (v : I → R) :
    scaleTarget 1 v = v := by
  funext i
  fin_cases i <;>
    simp [scaleTarget]

/-- The discrete source flip is the `s = -1` instance of the action. -/
theorem flipSource_eq_scale {R : Type u} [Field R] (p : I → R) :
    flipSource p = scaleSource (-1) p := by
  funext i
  fin_cases i <;>
    norm_num [flipSource, scaleSource, div_neg, div_one,
      Matrix.cons_val_two]

/-- The discrete target flip is the `s = -1` instance of the action. -/
theorem flipTarget_eq_scale {R : Type u} [Field R] (v : I → R) :
    flipTarget v = scaleTarget (-1) v := by
  funext i
  fin_cases i <;>
    norm_num [flipTarget, scaleTarget, div_neg, div_one,
      Matrix.cons_val_two]

end LeanProofs.JacobianCounterexample

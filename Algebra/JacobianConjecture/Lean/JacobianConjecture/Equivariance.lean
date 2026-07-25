import JacobianConjecture.Counterexample

/-!
# Equivariance and the rational triple collision

Alpöge's map `F = (P, Q, R)` satisfies the exact symmetry

```text
F (-x, -y, z) = (P, -Q, -R) (x, y, z),
```

an equivariance between the linear involutions `flipSource : (x, y, z) ↦
(-x, -y, z)` and `flipTarget : (u, v, w) ↦ (u, -v, -w)`.  Whenever the image
of a point is fixed by `flipTarget`, the point therefore collides with its
mirror.

This file proves the equivariance, uses it to produce the rational triple
collision

```text
F (0, 0, -1/4) = F (1, -3/2, 13/2) = F (-1, 3/2, 13/2) = (-1/4, 0, 0)
```

— the third point is the mirror of the second, so its image needs no fresh
computation.  `Scaling` identifies the involutions as a slice of a weighted
torus action, and `CollisionFamily` derives the rational one-parameter
family of collisions from that action.
-/

namespace LeanProofs.JacobianCounterexample

open Matrix MvPolynomial PolynomialMap

universe u

/-- The source involution `(x, y, z) ↦ (-x, -y, z)`. -/
def flipSource {R : Type u} [CommRing R] (p : I → R) : I → R :=
  ![-p 0, -p 1, p 2]

/-- The target involution `(u, v, w) ↦ (u, -v, -w)`. -/
def flipTarget {R : Type u} [CommRing R] (v : I → R) : I → R :=
  ![v 0, -v 1, -v 2]

set_option maxHeartbeats 800000 in
/-- **Equivariance.**  `F (-x, -y, z) = (P, -Q, -R) (x, y, z)` over every
commutative ring. -/
theorem counterexample_equivariant
    (R : Type u) [CommRing R] (p : I → R) :
    evalMap (counterexample R) (flipSource p) =
      flipTarget (evalMap (counterexample R) p) := by
  funext i
  fin_cases i <;>
    simp [evalMap, counterexample, flipSource, flipTarget] <;>
    ring

/-- A `flipTarget`-fixed image value turns the equivariance into a collision
between a point and its mirror. -/
theorem collision_of_flipTarget_fixed
    (R : Type u) [CommRing R] (p : I → R)
    (h : flipTarget (evalMap (counterexample R) p) =
      evalMap (counterexample R) p) :
    evalMap (counterexample R) (flipSource p) =
      evalMap (counterexample R) p := by
  rw [counterexample_equivariant, h]

/-- Mirroring the integral collision of `Counterexample` yields another
integral collision, with no new polynomial evaluation. -/
theorem mirrored_integral_collision (R : Type u) [CommRing R] :
    evalMap (counterexample R) (flipSource (collision₀ R)) =
      evalMap (counterexample R) (flipSource (collision₁ R)) := by
  rw [counterexample_equivariant, counterexample_equivariant,
    collision₀_value, collision₁_value]

/-!
## The rational triple collision

Three distinct rational points share one image.  The first is fixed by the
source involution; the third is the mirror of the second.
-/

/-- First point of the rational triple collision. -/
def rationalCollision₀ (R : Type u) [Field R] : I → R := ![0, 0, -(1 / 4)]

/-- Second point of the rational triple collision. -/
def rationalCollision₁ (R : Type u) [Field R] : I → R := ![1, -(3 / 2), 13 / 2]

/-- Third point of the rational triple collision. -/
def rationalCollision₂ (R : Type u) [Field R] : I → R := ![-1, 3 / 2, 13 / 2]

/-- The common image of the rational triple. -/
def rationalCollisionValue (R : Type u) [Field R] : I → R := ![-(1 / 4), 0, 0]

theorem rationalCollision₀_value (R : Type u) [Field R] [CharZero R] :
    evalMap (counterexample R) (rationalCollision₀ R) =
      rationalCollisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [evalMap, counterexample, rationalCollision₀,
      rationalCollisionValue, Matrix.cons_val_two]

theorem rationalCollision₁_value (R : Type u) [Field R] [CharZero R] :
    evalMap (counterexample R) (rationalCollision₁ R) =
      rationalCollisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [evalMap, counterexample, rationalCollision₁,
      rationalCollisionValue, Matrix.cons_val_two]

/-- The third rational point is the mirror of the second. -/
theorem rationalCollision₂_eq_flip (R : Type u) [Field R] :
    rationalCollision₂ R = flipSource (rationalCollision₁ R) := by
  funext i
  fin_cases i <;>
    norm_num [rationalCollision₁, rationalCollision₂, flipSource,
      Matrix.cons_val_two]

/-- The common image is fixed by the target involution. -/
theorem rationalCollisionValue_flipTarget_fixed (R : Type u) [Field R] :
    flipTarget (rationalCollisionValue R) = rationalCollisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [rationalCollisionValue, flipTarget,
      Matrix.cons_val_two]

/-- The third point's image follows from the second's by symmetry alone. -/
theorem rationalCollision₂_value (R : Type u) [Field R] [CharZero R] :
    evalMap (counterexample R) (rationalCollision₂ R) =
      rationalCollisionValue R := by
  rw [rationalCollision₂_eq_flip, counterexample_equivariant,
    rationalCollision₁_value, rationalCollisionValue_flipTarget_fixed]

theorem rationalCollisions_distinct (R : Type u) [Field R] [CharZero R] :
    rationalCollision₀ R ≠ rationalCollision₁ R ∧
    rationalCollision₀ R ≠ rationalCollision₂ R ∧
    rationalCollision₁ R ≠ rationalCollision₂ R := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · have h₀ := congrFun h 0
    norm_num [rationalCollision₀, rationalCollision₁, rationalCollision₂] at h₀

/-- **Three distinct points with a common image.**  The counterexample
identifies a rational triple, not merely a pair. -/
theorem counterexample_triple_collision (R : Type u) [Field R] [CharZero R] :
    ∃ p₀ p₁ p₂ : I → R,
      p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₁ ≠ p₂ ∧
      evalMap (counterexample R) p₀ = evalMap (counterexample R) p₁ ∧
      evalMap (counterexample R) p₁ = evalMap (counterexample R) p₂ := by
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := rationalCollisions_distinct R
  exact ⟨rationalCollision₀ R, rationalCollision₁ R, rationalCollision₂ R,
    h₀₁, h₀₂, h₁₂,
    (rationalCollision₀_value R).trans (rationalCollision₁_value R).symm,
    (rationalCollision₁_value R).trans (rationalCollision₂_value R).symm⟩

end LeanProofs.JacobianCounterexample

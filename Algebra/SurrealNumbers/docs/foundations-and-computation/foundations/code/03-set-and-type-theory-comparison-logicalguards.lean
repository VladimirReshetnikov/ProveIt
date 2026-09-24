/-!
# Logical guards and finite algebra for surreal formalization

Status: illustrative source; NOT compiled or kernel-checked during preparation
of the accompanying article. No claim is made that this file formalizes the
surreal field or any analytic theorem from the supplied manuscripts.

Intended dependency environment: the pinned combinatorial-games project
recorded in ../source_audit.json and ../README.md.
-/

import Mathlib

universe u

namespace SurrealFoundations

/-- No ordered carrier contains a strict upper bound for every subset of itself.
In a surreal cut interface, the admissible family size must therefore be
strictly restricted. -/
theorem noUnrestrictedUpperBounds (F : Type u) [Preorder F] :
    ¬ (∀ s : Set F, ∃ x : F, ∀ y ∈ s, y < x) := by
  intro h
  obtain ⟨x, hx⟩ := h Set.univ
  exact (lt_irrefl x) (hx x (Set.mem_univ x))

/-- A universe-correct skeleton for raw, small-branching game trees.
This is not yet the numeric subtype, a comparison relation, or a quotient. -/
inductive RawGame : Type (u + 1) where
  | cut (L R : Type u)
      (left : L → RawGame) (right : R → RawGame) : RawGame

/-- Coordinates for a quadratic extension. They have intentionally NOT been
given the componentwise product-ring structure on `F × F`. -/
structure QuadraticPair (F : Type u) where
  re : F
  im : F

namespace QuadraticPair

variable {F : Type u} [CommRing F]

/-- Multiplication with the relation `i^2 = -1`. -/
def mul (z w : QuadraticPair F) : QuadraticPair F :=
  ⟨z.re * w.re - z.im * w.im,
   z.re * w.im + z.im * w.re⟩

/-- Norm square; no order or square-root operation is needed here. -/
def normSq (z : QuadraticPair F) : F :=
  z.re ^ 2 + z.im ^ 2

/-- A polynomial identity valid over every commutative ring. -/
theorem normSq_mul (z w : QuadraticPair F) :
    normSq (mul z w) = normSq z * normSq w := by
  dsimp [normSq, mul]
  ring

end QuadraticPair

/-- The two-dimensional Gram identity is finite polynomial algebra, not a
specifically surreal analytic theorem. -/
theorem gramIdentity {F : Type u} [CommRing F] (a b c d : F) :
    (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 =
      (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  ring

end SurrealFoundations

-- Inspect the actual output after running in the selected environment.
#print axioms SurrealFoundations.noUnrestrictedUpperBounds
#print axioms SurrealFoundations.QuadraticPair.normSq_mul
#print axioms SurrealFoundations.gramIdentity

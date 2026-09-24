/-
Illustrative code accompanying Foundations for Surreal and Surcomplex Mathematics.
Status: NOT COMPILED in the environment used to prepare the article.
This file is not a construction of surreal numbers. It records a generic
impossibility theorem and two size-conscious data shapes.
-/
import Init

universe u v

namespace SurcomplexFoundations

/-- No strict bound operation can accept every subset of its own carrier. -/
theorem noUniversalStrictBound
    {X : Type u} (lt : X -> X -> Prop)
    (irrefl : forall x, Not (lt x x))
    (bound : (X -> Prop) -> X)
    (above : forall A x, A x -> lt x (bound A)) : False := by
  let all : X -> Prop := fun _ => True
  exact irrefl (bound all) (above all (bound all) True.intro)

/-- A raw tree shape. Numericity, order, arithmetic and quotient are NOT provided. -/
inductive RawGame : Type (u + 1) where
  | cut (L R : Type u)
      (left : L -> RawGame)
      (right : R -> RawGame) : RawGame

/-- Cut INPUT data, not an axiom asserting realization in an arbitrary carrier. -/
structure SmallCutData (X : Type v) (lt : X -> X -> Prop) where
  Left : Type u
  Right : Type u
  left : Left -> X
  right : Right -> X
  separated : forall l r, lt (left l) (right r)

#print axioms noUniversalStrictBound

end SurcomplexFoundations

import Std

/-!
# Host-level blueprint: certified setoids and algebraic operations

This file contains executable data structures and *target propositions*.
It deliberately contains no `axiom`, `sorry`, or `admit`.  The functions are
ordinary Lean functions at this layer.  The object-iPRA implementation replaces
each advertised function by a fixed `ConciseIPRA.PR` code and each field proof
by a term of type `Prf PRAAx ...`.
-/

namespace IPRAAlgebraicGeometry

abbrev Code := Nat
abbrev Witness := Nat

/-- Equality is proof-relevant and need not be decidable without a witness. -/
structure CertSetoid where
  valid : Code → Bool
  eqW : Code → Code → Witness → Bool
  reflW : Code → Witness
  symmW : Code → Code → Witness → Witness
  transW : Code → Code → Code → Witness → Witness → Witness
  refl_ok : ∀ x, valid x = true → eqW x x (reflW x) = true
  symm_ok : ∀ x y w, eqW x y w = true → eqW y x (symmW x y w) = true
  trans_ok : ∀ x y z u v,
    eqW x y u = true → eqW y z v = true →
      eqW x z (transW x y z u v) = true

/-- A map carries equality certificates to equality certificates. -/
structure CertMap (A B : CertSetoid) where
  run : Code → Code
  mapW : Code → Code → Witness → Witness
  valid_ok : ∀ x, A.valid x = true → B.valid (run x) = true
  congr_ok : ∀ x y w, A.eqW x y w = true →
    B.eqW (run x) (run y) (mapW x y w) = true

/-- Ring operations together with explicit congruence-witness transformers. -/
structure CertCommRing extends CertSetoid where
  zero one : Code
  add mul : Code → Code → Code
  neg : Code → Code
  addW : Code → Code → Code → Code → Witness → Witness → Witness
  mulW : Code → Code → Code → Code → Witness → Witness → Witness
  negW : Code → Code → Witness → Witness
  zero_valid : valid zero = true
  one_valid : valid one = true
  add_valid : ∀ x y, valid x = true → valid y = true → valid (add x y) = true
  mul_valid : ∀ x y, valid x = true → valid y = true → valid (mul x y) = true
  neg_valid : ∀ x, valid x = true → valid (neg x) = true
  add_congr : ∀ x x' y y' u v,
    eqW x x' u = true → eqW y y' v = true →
      eqW (add x y) (add x' y') (addW x x' y y' u v) = true
  mul_congr : ∀ x x' y y' u v,
    eqW x x' u = true → eqW y y' v = true →
      eqW (mul x y) (mul x' y') (mulW x x' y y' u v) = true
  neg_congr : ∀ x y w, eqW x y w = true →
    eqW (neg x) (neg y) (negW x y w) = true

/-- Module operations; the laws themselves become finite certificate families. -/
structure CertModule (R : CertCommRing) extends CertSetoid where
  zero : Code
  add : Code → Code → Code
  neg : Code → Code
  smul : Code → Code → Code
  addW : Code → Code → Code → Code → Witness → Witness → Witness
  smulW : Code → Code → Code → Code → Witness → Witness → Witness
  add_congr : ∀ x x' y y' u v,
    eqW x x' u = true → eqW y y' v = true →
      eqW (add x y) (add x' y') (addW x x' y y' u v) = true
  smul_congr : ∀ a a' x x' u v,
    R.eqW a a' u = true → eqW x x' v = true →
      eqW (smul a x) (smul a' x') (smulW a a' x x' u v) = true

/-- A finite family is always a code plus a length and a bounded accessor. -/
structure FiniteFamily where
  length : Nat
  get : Nat → Code

/-- Target: bounded folds preserve certificate equality. -/
def FoldCongruenceTarget (R : CertCommRing) : Prop :=
  ∀ (xs ys : List Code), xs.length = ys.length →
    (∀ i, (hi : i < xs.length) →
      ∃ w, R.eqW (xs.get ⟨i, hi⟩) (ys.get ⟨i, by simpa [xs.length] using hi⟩) w = true) →
    ∃ w, R.eqW (xs.foldl R.add R.zero) (ys.foldl R.add R.zero) w = true

end IPRAAlgebraicGeometry

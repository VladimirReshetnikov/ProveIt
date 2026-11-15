import Mathlib

/-!
# Geometric bridge: explicit elementary proof and remaining mesh identity

STATUS: uncompiled scaffold. The two short proof scripts below express only
ordinary host-Lean facts. They do not establish an object-language iPRA theorem.
-/

namespace MinkowskiIPRA

abbrev QVec (n : Nat) := Fin n → Rat

def midpoint {n : Nat} (x y : QVec n) : QVec n :=
  fun k => (x k + y k) / 2

def Symmetric {n : Nat} (K : QVec n → Prop) : Prop :=
  ∀ x, K x → K (-x)

def MidpointClosed {n : Nat} (K : QVec n → Prop) : Prop :=
  ∀ x y, K x → K y → K (midpoint x y)

/-- The complete logical geometric step: symmetry and one midpoint. -/
theorem difference_mem {n : Nat} (K : QVec n → Prop)
    (hs : Symmetric K) (hm : MidpointClosed K)
    (x y v : QVec n) (hx : K x) (hy : K y)
    (hv : midpoint x (-y) = v) : K v := by
  rw [← hv]
  exact hm x (-y) hx (hs y hy)

/-- A basis map preserves the nonzero witness when it is injective. -/
theorem injective_map_nonzero {n : Nat} (B : QVec n →ₗ[Rat] QVec n)
    (hB : Function.Injective B) (z : QVec n) (hz : z ≠ 0) : B z ≠ 0 := by
  intro h
  apply hz
  apply hB
  simpa using h

/-- Rational points obtained by doubling the centers of mesh cells. -/
def sample {n : Nat} (m : Nat) (a : Fin n → Int) : QVec n :=
  fun k => (2 * (a k : Rat) + 1) / (m : Rat)

/-!
NEXT GEOMETRY OBLIGATION (not assumed as an axiom):

Given m>0 and a_k-b_k=m*z_k, prove coordinatewise
  midpoint (sample m a) (-(sample m b)) = (fun k => (z k : Rat)).
Clear the nonzero denominator and use the integer equality cast into Rat.
Then commute a rational basis map B with the midpoint and apply difference_mem
and injective_map_nonzero. If a real basis is represented by regular names, the
object-language conclusion is an integer coefficient vector z; the actual
real vector Bz is interpreted externally. Do not put arbitrary Lean Real
objects into the first-order arithmetic input.

For a symmetric rational halfspace body |A*x| <= b, membership and box
containment are decidable after clearing denominators. The certificate checker
should verify each row at the box endpoints or use the exact center/radius
support formula. For an abstract represented body, the checker accepts its
finite inclusion evidence through a separately proved primitive-recursive
relation. It must never assume a universal truth oracle for arbitrary bodies.
-/

end MinkowskiIPRA

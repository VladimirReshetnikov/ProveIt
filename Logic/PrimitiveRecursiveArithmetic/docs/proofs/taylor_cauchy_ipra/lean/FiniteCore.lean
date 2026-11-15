import Mathlib

/-!
# Finite algebra for the constructive Taylor/Cauchy development

Status: proof scripts supplied, NOT compiled in the producing environment.
There is no `sorry`, extra axiom, or assumed analytic theorem in this file.
These are Lean metatheorems about finite algebra. They are NOT yet derivations
in the object theory `ConciseIPRA.PRAAx`.

The recursively defined sum deliberately makes all iteration explicit.
-/

namespace ConstructiveTaylorCauchy

section FiniteSums

variable {R : Type*} [CommRing R]

/-- The first `n` entries, accumulated by primitive recursion. -/
def prefix (u : Nat → R) : Nat → R
  | 0 => 0
  | n + 1 => prefix u n + u n

theorem prefix_telescope (u : Nat → R) (n : Nat) :
    prefix (fun k => u (k + 1) - u k) n = u n - u 0 := by
  induction n with
  | zero => simp [prefix]
  | succ n ih =>
    simp only [prefix]
    rw [ih]
    ring

/-- Exact summation by parts; the finite ancestor of integration by parts. -/
theorem summation_by_parts (u v : Nat → R) (n : Nat) :
    prefix (fun k => u k * (v (k + 1) - v k)) n =
      u n * v n - u 0 * v 0 -
        prefix (fun k => v (k + 1) * (u (k + 1) - u k)) n := by
  induction n with
  | zero => simp [prefix]
  | succ n ih =>
    simp only [prefix]
    rw [ih]
    ring

/-- The finite geometric identity has no convergence hypothesis. -/
theorem finite_geometric (q : R) (n : Nat) :
    (1 - q) * prefix (fun k => q ^ k) n = 1 - q ^ n := by
  induction n with
  | zero => simp [prefix]
  | succ n ih =>
    simp only [prefix]
    calc
      (1 - q) * (prefix (fun k => q ^ k) n + q ^ n) =
          (1 - q) * prefix (fun k => q ^ k) n + (1 - q) * q ^ n := by ring
      _ = (1 - q ^ n) + (1 - q) * q ^ n := by rw [ih]
      _ = 1 - q ^ (n + 1) := by rw [pow_succ]; ring

/-- Cancellation of the common edge of two oriented cells. -/
theorem cancel_common_edge (a b c d e : R) :
    (a + e + b) + (c - e + d) = a + b + c + d := by
  ring

/-- The exact product split behind the finite Taylor error estimate. -/
theorem taylor_product_split (w0 w1 wp e0 e1 ep h : R) :
    w1 * e1 - w0 * e0 - h * (w0 * ep + wp * e0) =
      w1 * (e1 - e0 - h * ep) + h * (w1 - w0) * ep +
        (w1 - w0 - h * wp) * e0 := by
  ring

/-- Twice the affine trapezoid integral around a triangle is zero. -/
theorem affine_triangle_numerator (a b u v w : R) :
    (v - u) * ((a + b * u) + (a + b * v)) +
      (w - v) * ((a + b * v) + (a + b * w)) +
      (u - w) * ((a + b * w) + (a + b * u)) = 0 := by
  ring

end FiniteSums

section QuotientAlgebra

variable {K : Type*} [Field K]

/-- Exact quotient remainder, used to transport a differentiability modulus
to `f(z)/(z-w)` on a region with a supplied positive denominator bound. -/
theorem quotient_remainder (f fp u h e : K)
    (hu : u ≠ 0) (huh : u + h ≠ 0) :
    (f + fp * h + e) / (u + h) - f / u -
        (fp / u - f / u ^ 2) * h =
      e / (u + h) - fp * h ^ 2 / (u * (u + h)) +
        f * h ^ 2 / (u ^ 2 * (u + h)) := by
  field_simp [hu, huh]
  <;> ring

end QuotientAlgebra

#print axioms prefix_telescope
#print axioms summation_by_parts
#print axioms finite_geometric
#print axioms cancel_common_edge
#print axioms taylor_product_split
#print axioms affine_triangle_numerator
#print axioms quotient_remainder

end ConstructiveTaylorCauchy

import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

/-!
# Uniqueness and simplicity above a simple residue root

These finite algebra facts support `trigonometry:lem:hensel` and
`prony:lem:hensel`. A coefficient homomorphism to a residue ring suffices:
two roots with the same simple residue coincide over a domain. Neither
monicity nor a presumed Hensel lift is needed.
-/

namespace Surreal.FinitePolynomial

open Polynomial

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]

omit [IsDomain R] in
/-- A nonzero residue derivative guarantees a nonzero actual derivative. -/
theorem eval_derivative_ne_zero_of_simple_reduction (φ : R →+* S) (p : R[X]) (x : R)
    (hd : (p.map φ).derivative.eval (φ x) ≠ 0) : p.derivative.eval x ≠ 0 := by
  intro he
  apply hd
  rw [derivative_map, eval_map, eval₂_at_apply, he, map_zero]

/-- Divided differences prove uniqueness among all roots with the same simple residue. -/
theorem eq_of_isRoot_of_simple_reduction (φ : R →+* S) (p : R[X]) (x y : R)
    (hx : p.IsRoot x) (hy : p.IsRoot y) (hxy : φ y = φ x)
    (hd : (p.map φ).derivative.eval (φ x) ≠ 0) : y = x := by
  obtain ⟨k, hk⟩ := binomExpansion p x (y - x)
  have hadd : x + (y - x) = y := by ring
  rw [hadd] at hk
  have hprod : (p.derivative.eval x + k * (y - x)) * (y - x) = 0 := by
    linear_combination -hk + hy.eq_zero - hx.eq_zero
  have hne : p.derivative.eval x + k * (y - x) ≠ 0 := by
    intro he
    apply hd
    have hh := congrArg φ he
    rw [map_add, map_mul, map_sub, hxy, sub_self, mul_zero, add_zero, map_zero] at hh
    simpa only [derivative_map, eval_map, eval₂_at_apply] using hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hne)

end Surreal.FinitePolynomial

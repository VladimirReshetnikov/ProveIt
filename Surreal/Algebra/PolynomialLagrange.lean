import Surreal.Algebra.PolynomialInterpolation
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Lagrange formula for simple roots

This file formalizes `polynomial:eq:lagrange`, the simple-root clause of
`polynomial:thm:crt` in `docs/surcomplex/polynomial-algebra/article.tex`.
It uses Mathlib's nodal polynomial and Lagrange interpolation directly.

The formula is a polynomial identity: dividing the nodal polynomial by
`X - aᵢ` is exact polynomial division, so the identity remains valid at the
nodes. A separate evaluated formula uses scalar division only away from
the nodes. Distinct-node interpolation works over any field, with no
characteristic-zero assumption. Empty node sets are included because the
degree bound then forces the interpolated polynomial to be zero.
-/

namespace Surreal
namespace FinitePolynomial

open Polynomial

noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι]

local instance polynomialLagrangeDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The all-simple-root modulus agrees with Mathlib's nodal polynomial. -/
theorem simple_interpolationModulus_eq_nodal (a : ι → K) :
    interpolationModulus a (fun _ => 1) = Lagrange.nodal Finset.univ a := by
  simp [interpolationModulus, Lagrange.nodal]

/-- Exact division removes the selected linear factor from the nodal
polynomial; this is the quotient used in `polynomial:eq:lagrange`. -/
theorem nodal_div_linear (a : ι → K) (i : ι) :
    Lagrange.nodal Finset.univ a / (X - C (a i)) =
      ∏ j ∈ Finset.univ.erase i, (X - C (a j)) :=
  (Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i)).symm

/-- The derivative at a simple node is the product of its nonzero
separations from the other nodes. -/
theorem nodal_derivative_eval (a : ι → K) (i : ι) :
    (Lagrange.nodal Finset.univ a).derivative.eval (a i) =
      ∏ j ∈ Finset.univ.erase i, (a i - a j) := by
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]

/-- All derivative denominators in `polynomial:eq:lagrange` are nonzero
when the nodes are distinct. No lower bound on their separation is used. -/
theorem nodal_derivative_eval_ne_zero (a : ι → K) (ha : Function.Injective a) (i : ι) :
    (Lagrange.nodal Finset.univ a).derivative.eval (a i) ≠ 0 := by
  have h := Lagrange.nodalWeight_ne_zero ha.injOn (Finset.mem_univ i)
  rwa [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i),
    ne_eq, inv_eq_zero] at h

/-- The displayed Lagrange identity `polynomial:eq:lagrange`, expressed
as an everywhere-valid polynomial identity with exact polynomial quotients. -/
theorem lagrange_formula (a : ι → K) (ha : Function.Injective a)
    (H : K[X]) (hH : H.degree < (Fintype.card ι : ℕ)) :
    H = ∑ i,
      C (H.eval (a i) / (Lagrange.nodal Finset.univ a).derivative.eval (a i)) *
        (Lagrange.nodal Finset.univ a / (X - C (a i))) := by
  nth_rewrite 1 [Lagrange.eq_interpolate ha.injOn hH]
  rw [Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi, div_eq_mul_inv, map_mul]
  ring

/-- Away from the nodes, the exact quotient can also be evaluated as an
ordinary scalar quotient. -/
theorem eval_nodal_div_linear (a : ι → K) (i : ι) {z : K} (hz : z ≠ a i) :
    (Lagrange.nodal Finset.univ a / (X - C (a i))).eval z =
      (Lagrange.nodal Finset.univ a).eval z / (z - a i) := by
  rw [← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i)]
  apply (eq_div_iff (sub_ne_zero.mpr hz)).mpr
  conv_rhs => rw [Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)]
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_comm]

/-- Both factors of a pointwise Lagrange denominator are nonzero away
from the selected node. -/
theorem lagrange_denominator_ne_zero (a : ι → K) (ha : Function.Injective a)
    (i : ι) {z : K} (hz : z ≠ a i) :
    (z - a i) * (Lagrange.nodal Finset.univ a).derivative.eval (a i) ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hz) (nodal_derivative_eval_ne_zero a ha i)

/-- The pointwise rational form of `polynomial:eq:lagrange` away from
all interpolation nodes, with every denominator nonzero. -/
theorem eval_lagrange_formula (a : ι → K) (ha : Function.Injective a)
    (H : K[X]) (hH : H.degree < (Fintype.card ι : ℕ))
    {z : K} (hz : ∀ i, z ≠ a i) :
    H.eval z = ∑ i, H.eval (a i) * (Lagrange.nodal Finset.univ a).eval z /
      ((z - a i) * (Lagrange.nodal Finset.univ a).derivative.eval (a i)) := by
  have h := congrArg (Polynomial.eval z) (lagrange_formula a ha H hH)
  rw [eval_finsetSum] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_mul, eval_C, eval_nodal_div_linear a i (hz i)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end

end FinitePolynomial
end Surreal

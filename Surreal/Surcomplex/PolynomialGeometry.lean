import Surreal.Surcomplex.Modulus
import Surreal.Algebra.PolynomialRootBounds
import Surreal.Algebra.PolynomialGaussLucas

/-!
# Root bounds and split-polynomial geometry on actual surcomplex numbers

The proved surreal-valued modulus instantiates both strict Cauchy bounds
from `polynomial:prop:rootbounds` / `polynomial:eq:cauchybound`.
No existence or splitting of polynomial roots is needed for these bounds.

Gauss--Lucas and its multiplicity-weighted barycentric formula now apply
to explicitly split surcomplex polynomials. Splitting remains visible:
surcomplex algebraic closedness is a separate outstanding obligation.
The radial maximum involving arbitrary positive integer roots also remains
separate; only square roots have been constructed so far.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Polynomial FinitePolynomial

noncomputable section

local instance polynomialGeometryDecidableEq : DecidableEq Surcomplex.{u} := Classical.decEq _

/-- The actual surcomplex modulus bundled as an absolute value into surreals. -/
def modulusAbsoluteValue : AbsoluteValue Surcomplex.{u} SignSequence.{u} :=
  Complexify.modulusAbsoluteValue

@[simp] theorem modulusAbsoluteValue_apply (z : Surcomplex.{u}) :
    modulusAbsoluteValue z = modulus z := rfl

/-- The strict upper Cauchy bound uses the source's finite coefficient maximum. -/
theorem root_lt_cauchy_bound (p : Surcomplex.{u}[X]) (hn : 0 < p.natDegree)
    {z : Surcomplex.{u}} (hz : p.IsRoot z) :
    modulus z < 1 + coefficientRatioMax modulusAbsoluteValue p hn :=
  FinitePolynomial.root_lt_cauchy_bound modulusAbsoluteValue p hn hz

/-- The strict reciprocal lower bound retains its nonzero constant-coefficient guard. -/
theorem reciprocal_cauchy_bound_lt_root (p : Surcomplex.{u}[X]) (hn : 0 < p.natDegree)
    (h₀ : p.coeff 0 ≠ 0) {z : Surcomplex.{u}} (hz : p.IsRoot z) :
    (1 + reciprocalCoefficientRatioMax modulusAbsoluteValue p hn)⁻¹ < modulus z :=
  FinitePolynomial.reciprocal_cauchy_bound_lt_root modulusAbsoluteValue p hn h₀ hz

/-- A certified coefficient-domination radius suffices for the radial
bound, without asserting existence of arbitrary-degree roots. -/
theorem root_le_two_mul_of_coeff_le_pow (p : Surcomplex.{u}[X]) (hp : p ≠ 0)
    {z : Surcomplex.{u}} (hz : p.IsRoot z) {M : SignSequence.{u}} (hM : 0 ≤ M)
    (hcoeff : ∀ j < p.natDegree,
      modulus (p.coeff j / p.leadingCoeff) ≤ M ^ (p.natDegree - j)) :
    modulus z ≤ 2 * M :=
  FinitePolynomial.root_le_two_mul_of_coeff_le_pow modulusAbsoluteValue p hp hz hM hcoeff

/-- The exact source barycentric formula for a nonroot critical point.
All weights and the denominator are surreal-valued; multiplicities are retained. -/
theorem critical_point_eq_barycentric_grouped (p : Surcomplex.{u}[X])
    (hn : 0 < p.natDegree) (hs : p.Splits) {w : Surcomplex.{u}}
    (hw : p.eval w ≠ 0) (hd : p.derivative.eval w = 0) :
    w = (∑ a ∈ p.roots.toFinset, (p.rootMultiplicity a : SignSequence.{u}) /
      modulus (w - a) ^ 2)⁻¹ •
      ∑ a ∈ p.roots.toFinset, ((p.rootMultiplicity a : SignSequence.{u}) /
        modulus (w - a) ^ 2) • a := by
  classical
  exact FinitePolynomial.critical_point_eq_barycentric_grouped p hn hs hw hd

/-- Gauss--Lucas for an explicitly split polynomial on the concrete field. -/
theorem critical_point_mem_convexHull_roots (p : Surcomplex.{u}[X])
    (hn : 0 < p.natDegree) (hs : p.Splits) {w : Surcomplex.{u}}
    (hd : p.derivative.IsRoot w) :
    w ∈ convexHull SignSequence.{u} {a : Surcomplex.{u} | p.IsRoot a} :=
  FinitePolynomial.critical_point_mem_convexHull_roots p hn hs hd

/-- Higher-derivative inclusion keeps every required splitting hypothesis. -/
theorem iterate_derivative_roots_subset_convexHull (p : Surcomplex.{u}[X]) (k : ℕ)
    (hs : ∀ j < k, ((derivative^[j]) p).Splits) (hk : (derivative^[k]) p ≠ 0) :
    {w : Surcomplex.{u} | ((derivative^[k]) p).IsRoot w} ⊆
      convexHull SignSequence.{u} {a | p.IsRoot a} :=
  FinitePolynomial.iterate_derivative_roots_subset_convexHull p k hs hk

end

end Surreal.Surcomplex

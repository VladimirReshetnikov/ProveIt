import Surreal.HahnSeries.PolynomialGaussValuation
import Mathlib.Algebra.Order.AddGroupWithTop

/-!
# Differentiation of weighted initial polynomials

This proves `polynomial:lem:initialderivative` and
`polynomial:eq:initialderivative` for Hahn-coefficient polynomials. The exact
expansion identity is a formal polynomial chain rule: differentiation in the
residue polynomial variable shifts Hahn exponents by the scale `ρ`.

The valuation and initial-polynomial identities require the derivative of
the initial polynomial to be nonzero. In residue characteristic zero,
positive degree implies this hypothesis. This restriction prevents an
incorrect conclusion when a constant initial polynomial, or a nonconstant
polynomial in positive characteristic, has zero derivative.
-/

namespace Surreal.HahnSeries

open Polynomial
open scoped _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- Translation commutes with formal polynomial differentiation. -/
theorem derivative_taylor (a : K⟦Γ⟧) (P : K⟦Γ⟧[X]) :
    (taylor a P).derivative = taylor a P.derivative := by
  simp [taylor_apply, derivative_comp]

/-- Before translation, the chain rule shifts the differentiated Gauss
expansion by `-ρ`. The coefficient map is additive, not a ring homomorphism. -/
theorem gaussExpansion_derivative (ρ : Γ) (P : K⟦Γ⟧[X]) :
    gaussExpansion ρ P.derivative =
      _root_.HahnSeries.single (-ρ) (1 : K[X]) *
        (gaussExpansion ρ P).map (Polynomial.derivative (R := K)) := by
  apply _root_.HahnSeries.ext
  funext g
  apply Polynomial.ext
  intro j
  rw [coeff_coeff_gaussExpansion, Polynomial.coeff_derivative,
    ← Nat.cast_add_one, ← nsmul_eq_mul', _root_.HahnSeries.coeff_nsmul, Pi.smul_apply, nsmul_eq_mul',
    _root_.HahnSeries.coeff_single_mul, one_mul, _root_.HahnSeries.map_coeff,
    Polynomial.coeff_derivative, coeff_coeff_gaussExpansion]
  simp only [Nat.cast_add_one]
  congr 2
  simp only [sub_neg_eq_add, add_nsmul, one_nsmul]
  abel

/-- The normalized derivative expansion used in the proof of
`polynomial:eq:initialderivative`, prior to taking leading coefficients. -/
theorem centeredGaussExpansion_derivative (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) :
    centeredGaussExpansion a ρ P.derivative =
      _root_.HahnSeries.single (-ρ) (1 : K[X]) *
        (centeredGaussExpansion a ρ P).map (Polynomial.derivative (R := K)) := by
  rw [centeredGaussExpansion_apply, ← derivative_taylor, gaussExpansion_derivative]
  rfl

/-- The literal normalized chain rule from the proof of
`polynomial:eq:initialderivative`. It holds for every normalization exponent
`ℓ`, and specializes to the Gauss value of a nonzero polynomial. -/
theorem normalizedGaussExpansion_derivative (a : K⟦Γ⟧) (ρ ℓ : Γ) (P : K⟦Γ⟧[X]) :
    (_root_.HahnSeries.single (-ℓ) (1 : K[X]) * centeredGaussExpansion a ρ P).map
        (Polynomial.derivative (R := K)) =
      _root_.HahnSeries.single (ρ - ℓ) (1 : K[X]) *
        centeredGaussExpansion a ρ P.derivative := by
  rw [centeredGaussExpansion_derivative, ← mul_assoc,
    _root_.HahnSeries.single_mul_single]
  have hs : ρ - ℓ + -ρ = -ℓ := by abel
  rw [hs, mul_one]
  apply _root_.HahnSeries.ext
  funext g
  rw [_root_.HahnSeries.map_coeff, _root_.HahnSeries.coeff_single_mul, one_mul,
    _root_.HahnSeries.coeff_single_mul, one_mul, _root_.HahnSeries.map_coeff]

omit [IsOrderedAddMonoid Γ] in
/-- Coefficientwise differentiation preserves Hahn order when it does not
annihilate the leading polynomial coefficient. -/
theorem orderTop_map_derivative (x : K[X]⟦Γ⟧) (h : x.leadingCoeff.derivative ≠ 0) :
    (x.map (Polynomial.derivative (R := K))).orderTop = x.orderTop := by
  have hx : x ≠ 0 := by
    intro hx
    simp [hx] at h
  apply le_antisymm
  · rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hx]
    apply _root_.HahnSeries.orderTop_le_of_coeff_ne_zero
    simpa only [_root_.HahnSeries.map_coeff, ← _root_.HahnSeries.leadingCoeff_eq] using h
  · apply _root_.HahnSeries.le_orderTop_iff_forall.mpr
    intro g hg
    rw [_root_.HahnSeries.map_coeff, _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop hg,
      Polynomial.derivative_zero]

omit [IsOrderedAddMonoid Γ] in
/-- The leading coefficient also differentiates exactly under the same
nonvanishing condition. -/
theorem leadingCoeff_map_derivative (x : K[X]⟦Γ⟧)
    (h : x.leadingCoeff.derivative ≠ 0) :
    (x.map (Polynomial.derivative (R := K))).leadingCoeff = x.leadingCoeff.derivative := by
  have hx : x ≠ 0 := by
    intro hx
    simp [hx] at h
  have hm : x.map (Polynomial.derivative (R := K)) ≠ 0 := by
    intro hm
    have hh := orderTop_map_derivative x h
    rw [hm, _root_.HahnSeries.orderTop_zero] at hh
    exact hx (_root_.HahnSeries.orderTop_eq_top.mp hh.symm)
  have ho : (x.map (Polynomial.derivative (R := K))).order = x.order := by
    apply WithTop.coe_injective
    rw [_root_.HahnSeries.order_eq_orderTop_of_ne_zero hm,
      _root_.HahnSeries.order_eq_orderTop_of_ne_zero hx, orderTop_map_derivative x h]
  rw [_root_.HahnSeries.leadingCoeff_eq, ho, _root_.HahnSeries.map_coeff,
    ← _root_.HahnSeries.leadingCoeff_eq]

/-- The weighted derivative value in `polynomial:eq:initialderivative`.
Subtraction is by a finite exponent; the nonzero initial derivative forces
both polynomial values to be finite. -/
theorem weightedGaussVal_derivative (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X])
    (h : (gaussInitial a ρ P).derivative ≠ 0) :
    weightedGaussVal a ρ P.derivative = weightedGaussVal a ρ P - (ρ : WithTop Γ) := by
  rw [weightedGaussVal_apply, centeredGaussExpansion_derivative,
    _root_.HahnSeries.orderTop_mul, _root_.HahnSeries.orderTop_single one_ne_zero,
    orderTop_map_derivative _ h]
  rw [weightedGaussVal_apply, sub_eq_add_neg,
    WithTop.LinearOrderedAddCommGroup.coe_neg, add_comm]

/-- The exact derivative of the initial polynomial in
`polynomial:eq:initialderivative`, with its necessary nonvanishing condition. -/
theorem gaussInitial_derivative (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X])
    (h : (gaussInitial a ρ P).derivative ≠ 0) :
    gaussInitial a ρ P.derivative = (gaussInitial a ρ P).derivative := by
  rw [gaussInitial, centeredGaussExpansion_derivative,
    _root_.HahnSeries.leadingCoeff_mul, _root_.HahnSeries.leadingCoeff_of_single,
    one_mul, leadingCoeff_map_derivative _ h]
  rfl

/-- The first-derivative assertions of `polynomial:lem:initialderivative`
under the exact residue-derivative nonvanishing hypothesis. -/
theorem initialDerivative_of_ne_zero (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X])
    (h : (gaussInitial a ρ P).derivative ≠ 0) :
    weightedGaussVal a ρ P.derivative = weightedGaussVal a ρ P - (ρ : WithTop Γ) ∧
      gaussInitial a ρ P.derivative = (gaussInitial a ρ P).derivative :=
  ⟨weightedGaussVal_derivative a ρ P h, gaussInitial_derivative a ρ P h⟩

variable [CharZero K]

/-- In residue characteristic zero, positive degree supplies the hypothesis
in `polynomial:lem:initialderivative`. -/
theorem initialDerivative (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X])
    (h : 0 < (gaussInitial a ρ P).natDegree) :
    weightedGaussVal a ρ P.derivative = weightedGaussVal a ρ P - (ρ : WithTop Γ) ∧
      gaussInitial a ρ P.derivative = (gaussInitial a ρ P).derivative :=
  initialDerivative_of_ne_zero a ρ P (Polynomial.derivative_ne_zero.mpr (ne_of_gt h))

private theorem natDegree_iterate_derivative_eq (I : K[X]) (r : ℕ) :
    (derivative^[r] I).natDegree = I.natDegree - r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
    omega

/-- The higher-derivative clause of `polynomial:lem:initialderivative`.
In characteristic zero, each derivative through the degree of the initial
polynomial has the expected valuation and initial polynomial. The harmless
zeroth iterate is included. -/
theorem initialIterateDerivative (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) (r : ℕ)
    (hr : r ≤ (gaussInitial a ρ P).natDegree) :
    weightedGaussVal a ρ (derivative^[r] P) =
        weightedGaussVal a ρ P - (r • ρ : Γ) ∧
      gaussInitial a ρ (derivative^[r] P) = derivative^[r] (gaussInitial a ρ P) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hir := ih (Nat.le_of_succ_le hr)
    have hdeg : 0 < (gaussInitial a ρ (derivative^[r] P)).natDegree := by
      rw [hir.2, natDegree_iterate_derivative_eq]
      omega
    have hstep := initialDerivative a ρ (derivative^[r] P) hdeg
    constructor
    · rw [Function.iterate_succ_apply', hstep.1, hir.1]
      simp only [sub_eq_add_neg, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      rw [add_assoc, ← WithTop.coe_add]
      congr 2
      simp [succ_nsmul, neg_add_rev, add_comm]
    · simpa only [Function.iterate_succ_apply', hir.2] using hstep.2

end

end Surreal.HahnSeries

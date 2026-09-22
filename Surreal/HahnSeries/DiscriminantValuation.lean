import Surreal.Algebra.PolynomialDiscriminant
import Surreal.HahnSeries.PolynomialValuation

/-!
# Discriminant valuations

This proves `polynomial:eq:discval`: the leading-coefficient and pairwise
separation formula, and the equality with the sum of root-derivative
valuations for monic polynomials. The discriminant is Mathlib's native
`Polynomial.discr`.

The `orderTop` formulas retain infinity when roots collide or derivative
values vanish. The exponent-group-valued formulas use `order` only under
explicit distinctness or nonvanishing assumptions. The leading-coefficient
formula requires positive degree; the monic root-multiset formula includes
the constant polynomial one. No surreal embedding or algebraic closedness
is assumed.
-/

namespace Surreal.HahnSeries

open Polynomial
open scoped _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K] [CharZero K]

local instance hahnCharZero : CharZero K⟦Γ⟧ where
  cast_injective m n h := by
    apply Nat.cast_injective (R := K)
    apply _root_.HahnSeries.C_injective (Γ := Γ)
    simpa only [map_natCast] using h

/-- The pairwise formula in `polynomial:eq:discval`, retaining infinity
for collisions. The enumeration contains every root occurrence, with its
multiplicity; its factorization is an explicit hypothesis. -/
theorem orderTop_discr_eq_pair_sum (P : Polynomial K⟦Γ⟧)
    (hP : 0 < P.natDegree) (a : Fin P.natDegree → K⟦Γ⟧)
    (hfactor : P = C P.leadingCoeff * ∏ i, (X - C (a i))) :
    P.discr.orderTop = (2 * P.natDegree - 2) • P.leadingCoeff.orderTop +
      2 • ∑ i, ∑ j ∈ Finset.Iio i, (a i - a j).orderTop := by
  rw [FinitePolynomial.discr_eq_leadingCoeff_pow_mul_prod_sub_sq P hP a hfactor,
    _root_.HahnSeries.orderTop_mul, orderTop_pow]
  simp only [orderTop_finset_prod, orderTop_pow, Finset.smul_sum]

/-- The finite-valued pairwise formula of `polynomial:eq:discval`.
Distinct enumerated roots ensure that every separation and the discriminant
are nonzero. -/
theorem order_discr_eq_pair_sum (P : Polynomial K⟦Γ⟧)
    (hP : 0 < P.natDegree) (a : Fin P.natDegree → K⟦Γ⟧)
    (ha : Function.Injective a)
    (hfactor : P = C P.leadingCoeff * ∏ i, (X - C (a i))) :
    P.discr.order = (2 * P.natDegree - 2) • P.leadingCoeff.order +
      2 • ∑ i, ∑ j ∈ Finset.Iio i, (a i - a j).order := by
  classical
  have hf (i : Fin P.natDegree) : ∀ j ∈ Finset.Iio i, (a i - a j) ^ 2 ≠ 0 := by
    intro j hj
    exact pow_ne_zero _ (sub_ne_zero.mpr (ha.ne (ne_of_gt (Finset.mem_Iio.mp hj))))
  have hprod : (∏ i, ∏ j ∈ Finset.Iio i, (a i - a j) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (hf i))
  have hval (i : Fin P.natDegree) :
      (∏ j ∈ Finset.Iio i, (a i - a j) ^ 2).order =
        ∑ j ∈ Finset.Iio i, 2 • (a i - a j).order := by
    rw [order_finset_prod _ _ (hf i)]
    simp only [_root_.HahnSeries.order_pow]
  rw [FinitePolynomial.discr_eq_leadingCoeff_pow_mul_prod_sub_sq P hP a hfactor,
    _root_.HahnSeries.order_mul
      (pow_ne_zero _ (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hP))) hprod,
    _root_.HahnSeries.order_pow,
    order_finset_prod _ _ (fun i _ => Finset.prod_ne_zero_iff.mpr (hf i))]
  simp only [hval, Finset.smul_sum]

/-- The monic equality `v(Disc(P)) = ∑ᵢ dᵢ` in
`polynomial:eq:discval`, with infinity allowed at repeated roots.
The multiset counts each root occurrence and includes the empty constant
case. -/
theorem orderTop_discr_eq_sum_derivative (P : Polynomial K⟦Γ⟧)
    (hm : P.Monic) (hs : P.Splits) :
    P.discr.orderTop = (P.roots.map fun a => (P.derivative.eval a).orderTop).sum := by
  rw [FinitePolynomial.discr_eq_sign_mul_resultant P hm,
    _root_.HahnSeries.orderTop_mul, orderTop_pow, _root_.HahnSeries.orderTop_neg,
    _root_.HahnSeries.orderTop_one, nsmul_zero, zero_add,
    orderTop_resultant_eq_sum_eval P P.derivative hs,
    hm.leadingCoeff, _root_.HahnSeries.orderTop_one, nsmul_zero, zero_add]

/-- The finite-valued monic equality in `polynomial:eq:discval` under
the nonvanishing discriminant hypothesis. Equivalently, in characteristic
zero the nonzero polynomial is squarefree. -/
theorem order_discr_eq_sum_derivative (P : Polynomial K⟦Γ⟧)
    (hm : P.Monic) (hs : P.Splits) (hd : P.discr ≠ 0) :
    P.discr.order = (P.roots.map fun a => (P.derivative.eval a).order).sum := by
  have heq : P.discr = (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) *
      (P.roots.map P.derivative.eval).prod := by
    rw [FinitePolynomial.discr_eq_sign_mul_resultant P hm,
      FinitePolynomial.resultant_eq_leadingCoeff_mul_prod_eval P P.derivative hs,
      hm.leadingCoeff, one_pow, one_mul]
  have hprod : (P.roots.map P.derivative.eval).prod ≠ 0 :=
    right_ne_zero_of_mul (heq ▸ hd)
  have hf : ∀ x ∈ P.roots.map P.derivative.eval, x ≠ 0 := by
    intro x hx hx0
    exact hprod (Multiset.prod_eq_zero_iff.mpr (hx0 ▸ hx))
  rw [heq, _root_.HahnSeries.order_mul
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hprod,
    _root_.HahnSeries.order_pow, _root_.HahnSeries.order_neg,
    _root_.HahnSeries.order_one, nsmul_zero, zero_add,
    order_multiset_prod _ hf, Multiset.map_map]
  rfl

end
end Surreal.HahnSeries

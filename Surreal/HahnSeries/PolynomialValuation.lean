import Surreal.Algebra.PolynomialResultant
import Surreal.Algebra.PolynomialLagrange
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Resultant and derivative valuations in a Hahn field

This file proves `polynomial:eq:resval` and the simple-root identity
`v(P'(aᵢ)) = ∑ⱼ≠ᵢ v(aᵢ-aⱼ)` used throughout the polynomial report.
The valuation is Mathlib's Hahn `orderTop`, with value infinity at zero.
Finite-valued versions use `order` only under explicit nonvanishing
hypotheses. No algebraic closedness or surreal embedding is assumed.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries Polynomial

noncomputable section

variable {Γ K ι : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- The Hahn valuation of a finite power, with infinity retained at zero. -/
theorem orderTop_pow (x : K⟦Γ⟧) (n : ℕ) :
    (x ^ n).orderTop = n • x.orderTop := (addVal Γ K).map_pow x n

/-- Multiplicities in a finite product become multiplicities in its valuation sum. -/
theorem orderTop_multiset_prod (s : Multiset K⟦Γ⟧) :
    s.prod.orderTop = (s.map orderTop).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih => simp only [Multiset.prod_cons, orderTop_mul,
      Multiset.map_cons, Multiset.sum_cons, ih]

/-- The same finite-product formula with values in the exponent group,
when no factor vanishes. -/
theorem order_multiset_prod (s : Multiset K⟦Γ⟧) (hs : ∀ x ∈ s, x ≠ 0) :
    s.prod.order = (s.map order).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have hx : x ≠ 0 := hs x (by simp)
    have hs' : ∀ y ∈ s, y ≠ 0 := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.prod_cons, order_mul hx (Multiset.prod_ne_zero (fun h0 => hs' 0 h0 rfl)),
      Multiset.map_cons, Multiset.sum_cons, ih hs']

theorem orderTop_finset_prod (s : Finset ι) (f : ι → K⟦Γ⟧) :
    (∏ i ∈ s, f i).orderTop = ∑ i ∈ s, (f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi,
      orderTop_mul, ih]

theorem order_finset_prod (s : Finset ι) (f : ι → K⟦Γ⟧)
    (hf : ∀ i ∈ s, f i ≠ 0) : (∏ i ∈ s, f i).order = ∑ i ∈ s, (f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hf' : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      order_mul (hf i (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hf'), ih hf']

/-- The valuation form of the first resultant root product. It includes
zero factors by using `WithTop Γ` rather than the zero-series `order` convention. -/
theorem orderTop_resultant_eq_sum_eval (P Q : Polynomial K⟦Γ⟧) (hP : P.Splits) :
    (P.resultant Q).orderTop = Q.natDegree • P.leadingCoeff.orderTop +
      (P.roots.map fun a => (Q.eval a).orderTop).sum := by
  rw [FinitePolynomial.resultant_eq_leadingCoeff_mul_prod_eval P Q hP,
    orderTop_mul, orderTop_pow, orderTop_multiset_prod, Multiset.map_map]
  rfl

/-- `polynomial:eq:resval`, with infinity allowed when a root difference
vanishes. Nonvanishing is needed only to replace `orderTop` by finite `order`. -/
theorem orderTop_resultant (P Q : Polynomial K⟦Γ⟧) (hP : P.Splits) (hQ : Q.Splits) :
    (P.resultant Q).orderTop = Q.natDegree • P.leadingCoeff.orderTop +
      P.natDegree • Q.leadingCoeff.orderTop +
        ((P.roots ×ˢ Q.roots).map fun ab => (ab.1 - ab.2).orderTop).sum := by
  rw [FinitePolynomial.resultant_eq_leadingCoeffs_mul_prod_sub P Q hP hQ,
    orderTop_mul, orderTop_mul, orderTop_pow, orderTop_pow,
    orderTop_multiset_prod, Multiset.map_map]
  rfl

/-- The exponent-group-valued version of `polynomial:eq:resval` under
the manuscript's nonvanishing hypotheses. -/
theorem order_resultant (P Q : Polynomial K⟦Γ⟧) (hP : P.Splits) (hQ : Q.Splits)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hres : P.resultant Q ≠ 0) :
    (P.resultant Q).order = Q.natDegree • P.leadingCoeff.order +
      P.natDegree • Q.leadingCoeff.order +
        ((P.roots ×ˢ Q.roots).map fun ab => (ab.1 - ab.2).order).sum := by
  have heq := FinitePolynomial.resultant_eq_leadingCoeffs_mul_prod_sub P Q hP hQ
  have hprod : ((P.roots ×ˢ Q.roots).map fun ab => ab.1 - ab.2).prod ≠ 0 :=
    right_ne_zero_of_mul (heq ▸ hres)
  have hleadP := pow_ne_zero Q.natDegree (leadingCoeff_ne_zero.mpr hP0)
  have hleadQ := pow_ne_zero P.natDegree (leadingCoeff_ne_zero.mpr hQ0)
  have hfactors : ∀ x ∈ (P.roots ×ˢ Q.roots).map (fun ab => ab.1 - ab.2), x ≠ 0 := by
    intro x hx hx0
    exact hprod (Multiset.prod_eq_zero_iff.mpr (hx0 ▸ hx))
  rw [heq, order_mul (mul_ne_zero hleadP hleadQ) hprod,
    order_mul hleadP hleadQ, _root_.HahnSeries.order_pow, _root_.HahnSeries.order_pow,
    order_multiset_prod _ hfactors, Multiset.map_map]
  rfl

variable [Fintype ι]

local instance polynomialValuationDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The simple-root derivative valuation is the sum of the separation
valuations, as in the definition of `dᵢ` in the polynomial report. -/
theorem orderTop_nodal_derivative_eval (a : ι → K⟦Γ⟧) (i : ι) :
    ((Lagrange.nodal Finset.univ a).derivative.eval (a i)).orderTop =
      ∑ j ∈ Finset.univ.erase i, (a i - a j).orderTop := by
  classical
  rw [FinitePolynomial.nodal_derivative_eval, orderTop_finset_prod]

/-- For distinct nodes the derivative valuation is finite, with exactly
the same separation sum in the ordered exponent group. -/
theorem order_nodal_derivative_eval (a : ι → K⟦Γ⟧) (ha : Function.Injective a) (i : ι) :
    ((Lagrange.nodal Finset.univ a).derivative.eval (a i)).order =
      ∑ j ∈ Finset.univ.erase i, (a i - a j).order := by
  classical
  rw [FinitePolynomial.nodal_derivative_eval, order_finset_prod]
  intro j hj
  exact sub_ne_zero.mpr (ha.ne (Finset.ne_of_mem_erase hj).symm)

end

end Surreal.HahnSeries

import Surreal.Algebra.PolynomialScaling
import Surreal.HahnSeries.StandardPart
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.GroupTheory.Divisible
import Mathlib.Data.Finset.Max

/-!
# Weighted monomial normalization of Hahn polynomials

In a divisible ordered abelian exponent group, a finite family of coefficients
with positive integral weights has an attained least weighted order. Scaling
by its Hahn monomial makes every coefficient nonnegative in order and retains
a nonzero residue. Applied to the lower coefficients of a monic polynomial,
this gives the finite normalization step in the odd-degree-root argument for
`found:sub:realclosed`, inside one fixed Hahn field.

Divisibility is used only to divide an exponent by a positive natural number.
The exponent group is not assumed to be a field. No odd-root theorem, real
closedness, or bridge to actual surreal normal forms is assumed.
-/

namespace Surreal.HahnSeries

open Polynomial
open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- Division by a weighted Hahn monomial subtracts its weighted exponent. -/
theorem orderTop_div_monomial_pow {a : K⟦Γ⟧} (ha : a ≠ 0) (γ : Γ) (n : ℕ) :
    (a / (single γ (1 : K)) ^ n).orderTop = (a.order - n • γ : Γ) := by
  rw [single_pow, one_pow, div_eq_mul_inv, inv_single, inv_one,
    orderTop_mul, ← order_eq_orderTop_of_ne_zero ha, orderTop_single one_ne_zero,
    ← WithTop.coe_add, sub_eq_add_neg]

variable [DivisibleBy Γ ℕ]

/-- A finite nonzero family has a common monomial scale making all weighted
coefficients nonnegative in order, with a nonzero residue attained somewhere. -/
theorem exists_weighted_monomial_normalization {ι : Type*} [Fintype ι]
    (a : ι → K⟦Γ⟧) (n : ι → ℕ) (hn : ∀ i, 0 < n i) (ha : ∃ i, a i ≠ 0) :
    ∃ γ : Γ,
      (∀ i, 0 ≤ (a i / (single γ (1 : K)) ^ n i).orderTop) ∧
      ∃ i, (a i / (single γ (1 : K)) ^ n i).coeff 0 ≠ 0 := by
  classical
  let s : Finset ι := Finset.univ.filter fun i => a i ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image s
    (fun i => DivisibleBy.div (a i).order (n i)) hs
  have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  refine ⟨DivisibleBy.div (a j).order (n j), ?_, j, ?_⟩
  · intro i
    obtain hi | hi := eq_or_ne (a i) 0
    · simp [hi]
    · rw [orderTop_div_monomial_pow hi]
      change ((0 : Γ) : WithTop Γ) ≤ ↑((a i).order - n i • DivisibleBy.div (a j).order (n j))
      apply WithTop.coe_le_coe.mpr
      apply sub_nonneg.mpr
      have h := nsmul_le_nsmul_right (hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)) (n i)
      simpa only [DivisibleBy.div_cancel _ (hn i).ne'] using h
  · apply coeff_orderTop_ne
    rw [orderTop_div_monomial_pow haj, DivisibleBy.div_cancel _ (hn j).ne', sub_self]

/-- The lower polynomial coefficients have the strictly positive weights
`natDegree - j`, so one monomial normalizes all of them simultaneously. -/
theorem exists_scalePolynomial_nonnegative {P : Polynomial K⟦Γ⟧}
    (hP : P.Monic) (hne : P ≠ X ^ P.natDegree) :
    ∃ γ : Γ,
      (∀ j, 0 ≤ ((FinitePolynomial.scalePolynomial P (single γ (1 : K))).coeff j).orderTop) ∧
      ∃ j < P.natDegree,
        ((FinitePolynomial.scalePolynomial P (single γ (1 : K))).coeff j).coeff 0 ≠ 0 := by
  obtain ⟨γ, hnonneg, j, hres⟩ := exists_weighted_monomial_normalization
    (fun j : Fin P.natDegree => P.coeff j.val) (fun j => P.natDegree - j.val)
    (fun j => Nat.sub_pos_of_lt j.isLt) (FinitePolynomial.exists_lowerCoeff_ne_zero hP hne)
  have ht : single γ (1 : K) ≠ 0 := single_ne_zero one_ne_zero
  refine ⟨γ, ?_, j.val, j.isLt, ?_⟩
  · intro k
    rcases lt_trichotomy k P.natDegree with hk | rfl | hk
    · rw [FinitePolynomial.scalePolynomial_coeff_of_le P ht hk.le]
      exact hnonneg ⟨k, hk⟩
    · rw [FinitePolynomial.scalePolynomial_coeff_of_le P ht le_rfl,
        Nat.sub_self, pow_zero, div_one, hP.coeff_natDegree, orderTop_one]
    · rw [FinitePolynomial.scalePolynomial_coeff_eq_zero _
        (Polynomial.coeff_eq_zero_of_natDegree_lt hk), orderTop_zero]
      exact le_top
  · rw [FinitePolynomial.scalePolynomial_coeff_of_le P ht j.isLt.le]
    exact hres

/-- A normalized polynomial over the actual nonnegative Hahn subring, with
nontrivial monic residue of the same degree and exact root pullback. -/
theorem exists_monic_reduction {P : Polynomial K⟦Γ⟧}
    (hP : P.Monic) (hne : P ≠ X ^ P.natDegree) :
    ∃ γ : Γ, ∃ Q : Polynomial (nonnegativeSubring Γ K),
      Q.Monic ∧ Q.natDegree = P.natDegree ∧
      Q.map (nonnegativeSubring Γ K).subtype = FinitePolynomial.scalePolynomial P (single γ 1) ∧
      (Q.map (standardPart Γ K)).Monic ∧
      (Q.map (standardPart Γ K)).natDegree = P.natDegree ∧
      Q.map (standardPart Γ K) ≠ X ^ P.natDegree ∧
      (∀ j, P.coeff j = 0 → (Q.map (standardPart Γ K)).coeff j = 0) ∧
      (∀ x : K⟦Γ⟧, (Q.map (nonnegativeSubring Γ K).subtype).IsRoot x ↔
        P.IsRoot (single γ 1 * x)) := by
  obtain ⟨γ, hnonneg, j, hj, hres⟩ := exists_scalePolynomial_nonnegative hP hne
  have ht : single γ (1 : K) ≠ 0 := single_ne_zero one_ne_zero
  let H := FinitePolynomial.scalePolynomial P (single γ (1 : K))
  have hH : H.Monic := FinitePolynomial.scalePolynomial_monic hP ht
  have hlift : H ∈ lifts (nonnegativeSubring Γ K).subtype := by
    apply (lifts_iff_coeff_lifts H).mpr
    intro n
    exact ⟨⟨H.coeff n, hnonneg n⟩, rfl⟩
  obtain ⟨Q, hQmap, _, hQ⟩ := lifts_and_degree_eq_and_monic hlift hH
  have hQcoeff (n : ℕ) : (Q.coeff n : K⟦Γ⟧) = H.coeff n := by
    have h := congrArg (fun F => F.coeff n) hQmap
    rw [Polynomial.coeff_map] at h
    exact h
  have hQd : Q.natDegree = P.natDegree := by
    rw [← hQ.natDegree_map (nonnegativeSubring Γ K).subtype, hQmap]
    exact FinitePolynomial.scalePolynomial_natDegree P ht
  have hRd : (Q.map (standardPart Γ K)).natDegree = P.natDegree :=
    (hQ.natDegree_map _).trans hQd
  refine ⟨γ, Q, hQ, hQd, hQmap, hQ.map _, hRd, ?_, ?_, ?_⟩
  · intro heq
    have hc := congrArg (fun F : K[X] => F.coeff j) heq
    rw [Polynomial.coeff_map, standardPart_apply, hQcoeff,
      coeff_X_pow, if_neg hj.ne] at hc
    exact hres hc
  · intro k hk
    rw [Polynomial.coeff_map, standardPart_apply, hQcoeff]
    change ((FinitePolynomial.scalePolynomial P (single γ 1)).coeff k).coeff 0 = 0
    rw [FinitePolynomial.scalePolynomial_coeff_eq_zero _ hk, HahnSeries.coeff_zero]
  · intro x
    rw [hQmap]
    exact FinitePolynomial.isRoot_scalePolynomial_iff P ht x

/-- In depressed form the ordinary residue stays depressed and is not a pure
power. This is the reduction needed for the subsequent odd-degree induction. -/
theorem exists_monic_depressed_reduction {P : Polynomial K⟦Γ⟧}
    (hP : P.Monic) (hd : P.coeff (P.natDegree - 1) = 0) (hne : P ≠ X ^ P.natDegree) :
    ∃ γ : Γ, ∃ Q : Polynomial (nonnegativeSubring Γ K),
      Q.Monic ∧ Q.natDegree = P.natDegree ∧
      Q.map (nonnegativeSubring Γ K).subtype = FinitePolynomial.scalePolynomial P (single γ 1) ∧
      (Q.map (standardPart Γ K)).Monic ∧
      (Q.map (standardPart Γ K)).natDegree = P.natDegree ∧
      (Q.map (standardPart Γ K)).coeff (P.natDegree - 1) = 0 ∧
      Q.map (standardPart Γ K) ≠ X ^ P.natDegree ∧
      (∀ x : K⟦Γ⟧, (Q.map (nonnegativeSubring Γ K).subtype).IsRoot x ↔
        P.IsRoot (single γ 1 * x)) := by
  obtain ⟨γ, Q, hQ, hQd, hmap, hR, hRd, hne, hzero, hroot⟩ := exists_monic_reduction hP hne
  exact ⟨γ, Q, hQ, hQd, hmap, hR, hRd, hzero _ hd, hne, hroot⟩

end

end Surreal.HahnSeries

import DiophantineConsistency.Sign17DegreeCompose
import Mathlib.Algebra.MvPolynomial.Equiv

/-! SOURCE-ONLY: probe a univariate path around the Matrix import conflict. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17UnivariateDegree
open MvPolynomial

abbrev P := Polynomial ℤ

theorem product_degree (p q : P) (hp : p ≠ 0) (hq : q ≠ 0) :
    (p*q).natDegree = p.natDegree + q.natDegree := by
  exact Polynomial.natDegree_mul' (mul_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr hp) (Polynomial.leadingCoeff_ne_zero.mpr hq))

theorem dominant_add (p q : P) (h : q.natDegree < p.natDegree) :
    (p+q).natDegree = p.natDegree :=
  Polynomial.natDegree_add_eq_left_of_natDegree_lt h

theorem mapped_degree_le (p : MvPolynomial (Fin 1) ℤ) :
    (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1) p).natDegree ≤ p.totalDegree := by
  let q : P := MvPolynomial.uniqueAlgEquiv ℤ (Fin 1) p
  change q.natDegree ≤ p.totalDegree
  by_cases hq : q = 0
  · simp [hq]
  · have hc : q.coeff q.natDegree ≠ 0 := by
      simpa only [Polynomial.coeff_natDegree] using (Polynomial.leadingCoeff_ne_zero.mpr hq)
    change (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1) p).coeff q.natDegree ≠ 0 at hc
    rw [MvPolynomial.coeff_uniqueAlgEquiv] at hc
    by_contra hn
    have hlt : p.totalDegree < ∑ i ∈ (Finsupp.single (default : Fin 1) q.natDegree).support,
        (Finsupp.single (default : Fin 1) q.natDegree) i := by
      change p.totalDegree < (Finsupp.single (default : Fin 1) q.natDegree).sum (fun _ n => n)
      rw [Finsupp.sum_single_index]
      exact Nat.lt_of_not_ge hn
    exact hc (MvPolynomial.coeff_eq_zero_of_totalDegree_lt hlt)
end DiophantineConsistency.Sign17UnivariateDegree
#print axioms DiophantineConsistency.Sign17UnivariateDegree.product_degree
#print axioms DiophantineConsistency.Sign17UnivariateDegree.dominant_add
#print axioms DiophantineConsistency.Sign17UnivariateDegree.mapped_degree_le

import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem homogeneous_aeval_scaled {I J R : Type*} [CommRing R]
    (P : MvPolynomial I R) {h : ℕ} (hP : P.IsHomogeneous h)
    (w : I → R) (Q : MvPolynomial J R) :
    aeval (fun i => C (w i) * Q) P = C (eval w P) * Q ^ h := by
  have hm (a : I →₀ ℕ) (ha : a ∈ P.support) :
      aeval (fun i => C (w i) * Q) (monomial a (P.coeff a)) =
        C (eval w (monomial a (P.coeff a))) * Q ^ h := by
    have hd : (∑ i ∈ a.support, a i) = h := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using
        hP (mem_support_iff.mp ha)
    rw [aeval_monomial, eval_monomial]
    simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum, hd, map_mul, mul_assoc]
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl hm

end Erdos3

end

end OAI

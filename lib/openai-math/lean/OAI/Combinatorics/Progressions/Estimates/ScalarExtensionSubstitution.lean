import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem aeval_polynomial_totalDegree_le {I J R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : MvPolynomial I R) (f : I → MvPolynomial J S) {d e : ℕ}
    (hP : P.totalDegree ≤ d) (hf : ∀ i, (f i).totalDegree ≤ e) :
    (aeval f P).totalDegree ≤ d * e := by
  rw [aeval_def, eval₂_eq]
  apply totalDegree_finsetSum_le
  intro a ha
  apply (totalDegree_mul _ _).trans
  simp only [MvPolynomial.algebraMap_apply, totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ a.support, (f i ^ a i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ a.support, a i * e := Finset.sum_le_sum (fun i _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i)))
    _ = (a.sum fun _ n => n) * e := by rw [← Finset.sum_mul]; rfl
    _ ≤ d * e := Nat.mul_le_mul_right _ ((le_totalDegree ha).trans hP)

end Erdos3

end

end OAI

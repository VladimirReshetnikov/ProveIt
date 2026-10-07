import OAI.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem rowPolynomial_map {K R S : Type*} [Fintype K] [CommRing R] [CommRing S]
    (f : R →+* S) (a : K → R) :
    map f (rowPolynomial a) = rowPolynomial (fun k => f (a k)) := by
  simp only [rowPolynomial, map_sum, map_mul, map_C, map_X]

theorem rowPolynomial_linear_combination {K H R : Type*} [Fintype K] [Fintype H]
    [CommRing R] (a : H → K → R) (x : H → R) :
    rowPolynomial (fun k => ∑ i, x i * a i k) = ∑ i, x i • rowPolynomial (a i) := by
  simp only [rowPolynomial, map_sum, map_mul, smul_eq_C_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem rowPolynomial_diagonal {K H R : Type*} [Fintype K] [Fintype H] [CommRing R]
    (a : H → K → R) (x : H → R) (w : R) :
    rowPolynomial (fun k => ∑ i, a i k * (x i * w)) =
      C w * ∑ i, x i • rowPolynomial (a i) := by
  simp only [rowPolynomial, map_sum, map_mul, smul_eq_C_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Erdos3

end

end OAI

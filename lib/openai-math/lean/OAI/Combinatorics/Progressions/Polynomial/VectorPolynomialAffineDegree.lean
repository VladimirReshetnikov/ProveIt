import OAI.Combinatorics.Progressions.Estimates.VectorHomogenization
import OAI.Combinatorics.Progressions.Lattices.LayerSamplingRankAffine

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

theorem degreeLE_finset_sum {I A R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (weight : I → ℕ) (h : ℕ) (s : Finset A) (p : A → VectorPolynomial I R W)
    (hp : ∀ a ∈ s, DegreeLE weight h (p a)) : DegreeLE weight h (∑ a ∈ s, p a) := by
  intro d hd
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun a ha => hp a ha d hd)

theorem degreeLE_tmul_totalDegree {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (P : MvPolynomial I R) (w : W) {h : ℕ} (hP : P.totalDegree ≤ h) :
    DegreeLE (1 : I → ℕ) h (P ⊗ₜ[R] w) := by
  intro d hd
  have hsum : h < ∑ i ∈ d.support, d i := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_def, smul_eq_mul, mul_one] using hd
  rw [coefficients_tmul, MvPolynomial.coeff_eq_zero_of_totalDegree_lt (hP.trans_lt hsum), zero_smul]

theorem degreeLE_substitute_affine {I K R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (f : I → MvPolynomial K R) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : VectorPolynomial I R W) (hp : DegreeLE (1 : I → ℕ) h p) :
    DegreeLE (1 : K → ℕ) h (substitute f p) := by
  classical
  rw [← sum_monomial_coefficients p, Finsupp.sum, map_sum]
  apply degreeLE_finset_sum
  intro d hd
  rw [monomial, substitute_tmul]
  apply degreeLE_tmul_totalDegree
  have hb : d.sum (fun _ n => n) ≤ h := by
    simpa only [Finsupp.weight_apply, Pi.one_def, smul_eq_mul, mul_one] using
      (degreeLE_iff (1 : I → ℕ) h p).mp hp d hd
  simpa only [Nat.mul_one] using aeval_polynomial_totalDegree_le (MvPolynomial.monomial d (1 : R)) f
    ((MvPolynomial.totalDegree_monomial_le d 1).trans hb) hf

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem residueAffine_degreeLE {I V : Type*} [AddCommGroup V] [Module ℝ V]
    {h : ℕ} (q : ℕ) (r : I → ℤ) (P : VectorPolynomial I ℝ V)
    (hP : DegreeLE (fun _ => 1) h P) :
    DegreeLE (fun _ => 1) h (residueAffine q r P) := by
  apply degreeLE_substitute_affine _ _ P hP
  intro i
  change (MvPolynomial.C (r i : ℝ) +
    MvPolynomial.C (q : ℝ) * MvPolynomial.X i).totalDegree ≤ 1
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · rw [MvPolynomial.totalDegree_C]
    exact Nat.zero_le _
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

end Erdos3.VectorPolynomial

end

end OAI

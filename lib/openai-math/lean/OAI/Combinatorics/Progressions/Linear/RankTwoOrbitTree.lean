import OAI.Combinatorics.Progressions.Estimates.NativeProductCoefficient
import OAI.Combinatorics.Progressions.Polynomial.NativeRankPolynomialFactorization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open VectorPolynomial
open scoped TensorProduct

theorem top_tree_product_rank_two
    {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
    {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r) (hs : 1 ≤ s)
    (A K U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hK : ∀ d : Fin s, coefficients K.log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (d : I → Fin s) (a : FreeMagma I)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r) :
    lieTreeEval (fun i => coefficients (A * K * U).log (Finsupp.single () ((d i).val + 1))) a =
      lieTreeEval (fun i => coefficients A.log (Finsupp.single () ((d i).val + 1)) +
        coefficients U.log (Finsupp.single () ((d i).val + 1))) a := by
  have hmem (v : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (j : Fin s) :
      coefficients v.log (Finsupp.single () (j.val + 1)) ∈
        (T.filtration.layer (j.val + 1) 1).baseChange ℝ := by
    have h := (E.filtration.realification.adapted_iff_coefficients _ _).mp v.adapted
      (Finsupp.single () (j.val + 1))
    have h₀ : coefficients v.log (Finsupp.single () (j.val + 1)) ∈
        T.filtration.realification.associatedDegree.layer (j.val + 1) := by
      rw [T.real_associated]
      simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using h
    change coefficients v.log (Finsupp.single () (j.val + 1)) ∈
      (T.filtration.layer (j.val + 1) 0).baseChange ℝ at h₀
    rwa [T.filtration.rank_zero_eq_one] at h₀
  have hdiff (j : Fin s) :
      coefficients (A * K * U).log (Finsupp.single () (j.val + 1)) -
        (coefficients A.log (Finsupp.single () (j.val + 1)) +
          coefficients U.log (Finsupp.single () (j.val + 1))) ∈
        (T.filtration.layer (j.val + 1) 2).baseChange ℝ := by
    have h₁ := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs
      (fun _ : Unit => 1) (Finsupp.single () (j.val + 1)) A K
    have h₂ := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs
      (fun _ : Unit => 1) (Finsupp.single () (j.val + 1)) (A * K) U
    simp only [Finsupp.weight_single, smul_eq_mul, mul_one] at h₁ h₂
    convert ((T.filtration.layer (j.val + 1) 2).baseChange ℝ).add_mem
      (((T.filtration.layer (j.val + 1) 2).baseChange ℝ).add_mem h₂ h₁) (hK j) using 1
    abel
  exact T.filtration.realification.top_lieTreeEval_congr _ _
    (fun i => (d i).val + 1) (fun i => hmem _ (d i))
    (fun i => ((T.filtration.layer ((d i).val + 1) 1).baseChange ℝ).add_mem
      (hmem A (d i)) (hmem U (d i)))
    (fun i => hdiff (d i)) a hd hr

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI

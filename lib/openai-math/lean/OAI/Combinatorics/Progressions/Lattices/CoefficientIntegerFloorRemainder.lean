import OAI.Combinatorics.Progressions.Polynomial.CoefficientPolynomialLift

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientIntegerFloorPolynomial
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (j : Fin m) (i : J j) : MvPolynomial K ℤ :=
  integerMonomialArrayPolynomial Subtype.val
    (fun d : BoundedCoefficientExponent K (j.val + 1) =>
      ⌊(c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i⌋)

theorem coefficientIntegerFloorPolynomial_degree
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (j : Fin m) (i : J j) :
    (coefficientIntegerFloorPolynomial U b o a c j i).totalDegree ≤ j.val + 1 :=
  integerMonomialArrayPolynomial_degree Subtype.val _ (fun d => d.property)

theorem canonicalCoefficientSample_floor_coefficient_remainder
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) (i : J j) :
    (c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i =
      (⌊(c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i⌋ : ℤ) := by
  obtain ⟨z, hz⟩ := canonicalCoefficientSample_integer_remainder U b hb o a c hc j d i
  rw [mixedLiftCoefficient_eq, hz, Int.floor_intCast]

theorem canonicalCoefficientSample_floor_polynomial_remainder
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (i : J j) :
    coefficientRowPolynomial U c j i =
      mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (a j) i +
        MvPolynomial.map (Int.castRingHom ℝ) (coefficientIntegerFloorPolynomial U b o a c j i) ∧
      (coefficientIntegerFloorPolynomial U b o a c j i).totalDegree ≤ j.val + 1 := by
  refine ⟨?_, coefficientIntegerFloorPolynomial_degree U b o a c j i⟩
  rw [coefficientIntegerFloorPolynomial, integerMonomialArrayPolynomial_map]
  change (∑ d : BoundedCoefficientExponent K (j.val + 1), MvPolynomial.monomial d.val ((c ⟨j,d⟩).val i)) = _
  unfold mixedLiftPolynomial monomialArrayPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← map_add]
  apply congrArg (MvPolynomial.monomial d.val)
  have hd := canonicalCoefficientSample_floor_coefficient_remainder U b hb o a c hc j d i
  linarith

theorem canonicalCoefficientSample_floor_integer_evaluation
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (i : J j) (x : K → ℤ) :
    MvPolynomial.eval (fun v => (x v : ℝ)) (coefficientRowPolynomial U c j i) =
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (a j).1 (a j).2 (fun v => (x v : ℝ)) i +
          (MvPolynomial.eval x (coefficientIntegerFloorPolynomial U b o a c j i) : ℝ) := by
  have h := integerPolynomial_remainder_eval _ _ _
    (canonicalCoefficientSample_floor_polynomial_remainder U b hb o a c hc j i).1 x
  rwa [mixedLiftPolynomial_eval] at h

end Erdos3.VectorPolynomial

end

end OAI

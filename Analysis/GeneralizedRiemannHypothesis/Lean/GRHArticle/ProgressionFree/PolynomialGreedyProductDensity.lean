import GRHArticle.ProgressionFree.PolynomialExteriorValuationProduct
import GRHArticle.ProgressionFree.PolynomialOneFreePrimeGain
import GRHArticle.ProgressionFree.PolynomialValuationScalarClosure

/-!
# The Euler products of the actual greedy family and one-free-prime optimum
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The greedy valuation set of all nonzero polynomials has the all-prime
Euler product as its natural degree-ball density. -/
theorem tendsto_polynomialValuationGreedySet_eulerProduct :
    Tendsto (polynomialBallProportion (polynomialValuationGreedySet F)) atTop
      (𝓝 (greedyPrimeExteriorProduct (∅ : Finset F[X]))) := by
  let V : (F[X] → ℕ) → Prop := fun v ↦ ∀ p, v p ∈ greedyExponents
  let B : Set F[X] := {f | V (fun p ↦ polynomialPrimeExponent p f)}
  have hlayer (n : ℕ) : monicFamilyLayer B n = greedyPrimeAvoidingLayer ∅ n := by
    ext f
    rw [mem_monicFamilyLayer, mem_greedyPrimeAvoidingLayer]
    simp [B, V]
  have hmono : Tendsto (monicFamilyProportion B) atTop
      (𝓝 (greedyPrimeAvoidingDensity (∅ : Finset F[X]))) := by
    unfold monicFamilyProportion
    simp_rw [hlayer]
    exact tendsto_greedyPrimeAvoidingLayer_card_div_pow ∅ (by simp)
  have he : polynomialScalarClosure B = polynomialValuationGreedySet F :=
    polynomialScalarClosure_valuationPredicate V
  have hd : greedyPrimeAvoidingDensity (∅ : Finset F[X]) =
      greedyPrimeExteriorProduct (∅ : Finset F[X]) := by
    rw [greedyPrimeAvoidingDensity_eq_exclusion_mul_exteriorProduct ∅ (by simp)]
    simp [polynomialPrimeExclusionWeight]
  simpa only [he, hd] using tendsto_polynomialBallProportion_scalarClosure hmono

/-- The attained one-free-prime optimum with the exterior Euler factor
written explicitly. -/
theorem polynomialOneFreePrimeOptimum_eq_exteriorProduct {P : F[X]}
    (hm : P.Monic) (hi : Irreducible P) (hP : P.natDegree = 1) :
    polynomialOneFreePrimeOptimum P =
      let z := (Fintype.card F : ℝ)⁻¹
      greedyPrimeExteriorProduct {P} * (1-z)^2 *
        ∑' t : ℕ, (rothNumberNat (t+1) : ℝ)*z^t := by
  rw [polynomialOneFreePrimeOptimum, greedyPrimeAvoidingDensity_singleton_linear_eq_exteriorProduct hm hi hP]
  ring

end GRHArticle.ProgressionFree

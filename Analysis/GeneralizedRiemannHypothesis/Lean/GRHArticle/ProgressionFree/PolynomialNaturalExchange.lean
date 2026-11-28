import GRHArticle.ProgressionFree.PolynomialNaturalExchangeRule
import GRHArticle.ProgressionFree.PolynomialOneFreePrimeFibers

/-!
# Polynomial progressions in the joint valuation exchange

The joint rule on selected primes can be combined with independent rules on
all other prime factors. Multiplication by a common polynomial ratio gives
nonnegative steps in every valuation.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical

variable {F : Type*} [Field F]

/-- The polynomial family associated to a joint exponent rule and a uniform
background set of allowed multiplicities. Scalars are unrestricted. -/
def polynomialValuationFamily (S : Finset F[X]) (A : Set ℕ) (D : Set (↥S → ℕ)) :
    Set F[X] :=
  {f | f ≠ 0 ∧ (∀ p ∉ S, polynomialPrimeExponent p f ∈ A) ∧
    (fun p : ↥S ↦ polynomialPrimeExponent p.val f) ∈ D}

/-- A progression-free background and a joint rule forbidding nonnegative
steps suffice for polynomial-ratio progression avoidance over any field. -/
theorem polynomialRatioThreeGPFree_valuationFamily {S : Finset F[X]} {A : Set ℕ}
    {D : Set (↥S → ℕ)} (hA : ThreeAPFree A)
    (hD : ∀ u h : ↥S → ℕ, u ∈ D → (fun p ↦ u p + h p) ∈ D →
      (fun p ↦ u p + 2 * h p) ∈ D → ∀ p, h p = 0) :
    PolynomialRatioThreeGPFree (polynomialValuationFamily S A D) := by
  intro f r hf hr he
  rcases he with ⟨ha, hb, hc⟩
  have hr₀ : r ≠ 0 := fun hz ↦ by simp [hz] at hr
  have hfr := mul_ne_zero hf hr₀
  have hb' (p : F[X]) := polynomialPrimeExponent_mul p hf hr₀
  have hc' (p : F[X]) : polynomialPrimeExponent p (f*r*r) =
      polynomialPrimeExponent p f + 2 * polynomialPrimeExponent p r := by
    rw [polynomialPrimeExponent_mul p hfr hr₀, hb']
    omega
  have hsel := hD (fun p ↦ polynomialPrimeExponent p.val f)
    (fun p ↦ polynomialPrimeExponent p.val r) ha.2.2
    (by simpa only [hb'] using hb.2.2) (by simpa only [hc'] using hc.2.2)
  have hcount (p : F[X]) : polynomialPrimeExponent p r = 0 := by
    by_cases hp : p ∈ S
    · exact hsel ⟨p, hp⟩
    · have hm := hb' p
      have he := hc' p
      have hap := hA (ha.2.1 p hp) (hb.2.1 p hp) (hc.2.1 p hp) (by omega)
      omega
  have hfac : normalizedFactors r = 0 := Multiset.ext.mpr (fun p ↦ by
    simpa [polynomialPrimeExponent] using hcount p)
  exact (not_isUnit_of_natDegree_pos r hr) ((normalizedFactors_eq_zero_iff hr₀).mp hfac)

/-- The natural-density exchange contains no triple with a positive-degree
polynomial ratio. The choice of the finite set is arbitrary. -/
theorem polynomialRatioThreeGPFree_naturalExchange (S : Finset F[X]) :
    PolynomialRatioThreeGPFree
      (polynomialValuationFamily S greedyExponents (naturalExchangeRule greedyExponents ↥S)) :=
  polynomialRatioThreeGPFree_valuationFamily threeAPFree_greedyExponents
    (fun _ _ ↦ greedy_naturalExchangeRule_step_eq_zero)

end GRHArticle.ProgressionFree

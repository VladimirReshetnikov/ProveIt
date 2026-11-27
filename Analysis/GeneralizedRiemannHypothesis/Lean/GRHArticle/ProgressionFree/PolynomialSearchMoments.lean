import GRHArticle.ProgressionFree.PolynomialProductMoments
import GRHArticle.ProgressionFree.PolynomialGeometricMoments
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Tilted moments of the smooth degree series

The smooth Euler product has one geometric factor per monic irreducible.
Its normalized mean and variance are sums of the corresponding prime contributions.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

/-- Raw moments of a finite product of positive-degree geometric factors. -/
theorem hasTiltedDegreeMoments_smooth {ι : Type*} (S : Finset ι) (d : ι → ℕ)
    (hd : ∀ i ∈ S, 0 < d i) {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    HasTiltedDegreeMoments (smoothDegreeCountingSeries S d) z
      (∏ i ∈ S, 1 / (1 - z ^ d i))
      (∑ i ∈ S, (d i : ℝ) * z ^ d i / (1 - z ^ d i))
      (∑ i ∈ S, (d i : ℝ) ^ 2 * z ^ d i / (1 - z ^ d i) ^ 2) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [smoothDegreeCountingSeries] using hasTiltedDegreeMoments_one z
  | @insert i S hi ih =>
    have hi' := hd i (Finset.mem_insert_self i S)
    have hg : HasTiltedDegreeMoments (degreeGeometricSeries (d i)) z _ _ _ :=
      ⟨hasSum_degreeGeometric_mass hi' hz₀ hz₁, hasSum_degreeGeometric_first hi' hz₀ hz₁,
       hasSum_degreeGeometric_second hi' hz₀ hz₁⟩
    simpa only [smoothDegreeCountingSeries, Finset.prod_insert hi, Finset.sum_insert hi] using
      hasTiltedDegreeMoments_mul hg (ih (fun j hj ↦ hd j (Finset.mem_insert_of_mem hj)))

/-- Exact normalized mean and variance of the tilted smooth-polynomial counts.
The weighted first and centered second moments both converge. -/
theorem polynomialSmoothDegreeSeries_moments (F : Type*) [Field F] [Fintype F] (L : ℕ)
    {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    let S := polynomialSmoothPrimes F L
    let A (n : ℕ) := (PowerSeries.coeff (R := ℕ) n (polynomialSmoothDegreeSeries F L) : ℝ)
    Summable (fun n ↦ A n * z ^ n) ∧ 0 < coefficientMass z A ∧
    coefficientMean z A = ∑ p ∈ S, (p.natDegree : ℝ) * z ^ p.natDegree / (1 - z ^ p.natDegree) ∧
    coefficientVariance z A =
      ∑ p ∈ S, (p.natDegree : ℝ)^2 * z ^ p.natDegree / (1 - z ^ p.natDegree)^2 ∧
    Summable (fun n ↦ coefficientWeight z A n * n) ∧
    Summable (fun n ↦ coefficientWeight z A n * ((n : ℝ) - coefficientMean z A)^2) := by
  classical
  let S := polynomialSmoothPrimes F L
  have hd (p : Polynomial F) (hp : p ∈ S) : 0 < p.natDegree :=
    Irreducible.natDegree_pos (mem_polynomialSmoothPrimes.mp hp).2.1
  have hm := hasTiltedDegreeMoments_smooth S Polynomial.natDegree hd hz₀ hz₁
  have hp : 0 < ∏ p ∈ S, 1 / (1 - z ^ p.natDegree) :=
    Finset.prod_pos fun p h ↦ one_div_pos.mpr (sub_pos.mpr (pow_lt_one₀ hz₀ hz₁ (hd p h).ne'))
  obtain ⟨hmass, hμ, hv, hfirst, hsecond⟩ := hm.normalized hp.ne'
  exact ⟨hm.mass.summable, hmass ▸ hp, hμ, hv, hfirst, hsecond⟩

end GRHArticle.ProgressionFree

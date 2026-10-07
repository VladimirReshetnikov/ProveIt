import OAI.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison
import OAI.Combinatorics.Progressions.Probability.AllocatedProgressionDensityIdentity

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U))

theorem CoefficientDeckDensityLaw.masked_integral
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d]
    (hlaw : CoefficientDeckDensityLaw U bW b hb o μ source density d)
    (hdensity : Measurable density)
    (A : CoefficientTorus (K := K) U → ℝ) (hA : Measurable A)
    (hA0 : ∀ y, 0 ≤ A y)
    (hAD : ∀ y, A y ≤ density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y))
    (f : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d → ℝ)
    (hmask : ∀ᵐ p ∂source.prod (PMF.uniformOfFintype
      (CoefficientDeckResidues (K := K) B d)).toMeasure,
      A (canonicalCoefficientDeckSample U bW b hb o d (NeZero.pos d) p.1 p.2) =
        f p * density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d
          (canonicalCoefficientDeckSample U bW b hb o d (NeZero.pos d) p.1 p.2))) :
    (∫ y, A y ∂μ) = ∫ p, f p ∂source.prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure := by
  exact maskedDensity_integral_of_sample_law
    (source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) μ
    (fun p => canonicalCoefficientDeckSample U bW b hb o d (NeZero.pos d) p.1 p.2)
    (canonicalCoefficientDeckSample_measurable U bW b hb o d)
    (fun y => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y)) A
    (hdensity.comp (quotientIntegerCover_continuous _ d).measurable) hA hA0 hAD hlaw f hmask

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.PreparedCanonicalRelativeEndpointBounds
import OAI.Combinatorics.Progressions.Fourier.PreparedCoefficientTorusCompact

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule MeasureTheory VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
    (K : Type) [Fintype K]

structure CanonicalSamplerMeasures where
  lattice : ∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))
  coefficientCompact : CompactSpace (CoefficientTorus (K := K) (fun j => (L j).space))
  coefficientBorel : BorelSpace (CoefficientTorus (K := K) (fun j => (L j).space))
  rowCompact : CompactSpace (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space))
  rowBorel : BorelSpace (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space))
  siteBorel : BorelSpace (SiteTorus (Finset (Fin (0 + 1))) (fun j => (L j).space))
  layer : ∀ j, Measure (euclideanSubspace (L j).space ⧸
    (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)).toAddSubgroup)
  layerInvariant : ∀ j, (layer j).IsAddLeftInvariant
  layerProbability : ∀ j, IsProbabilityMeasure (layer j)
  coefficient : Measure (CoefficientTorus (K := K) (fun j => (L j).space))
  coefficientInvariant : coefficient.IsAddLeftInvariant
  coefficientProbability : IsProbabilityMeasure coefficient
  row : Measure (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space))
  rowInvariant : row.IsAddLeftInvariant
  rowProbability : IsProbabilityMeasure row

noncomputable def PreparedHeights.canonicalSamplerMeasures
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R) (hp : 0 ≤ p) (hR : 1 ≤ R) :
    L.CanonicalSamplerMeasures K := by
  let : ∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)) :=
    hL.lattice_full L hp hR
  let : CompactSpace (CoefficientTorus (K := K) (fun j => (L j).space)) :=
    hL.coefficientTorus_compact L hp hR
  let : CompactSpace (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space)) :=
    hL.coefficientTorus_compact L hp hR
  let : BorelSpace (CoefficientTorus (K := K) (fun j => (L j).space)) :=
    QuotientAddGroup.borelSpace
  let : BorelSpace (CoefficientTorus (K := Fin (0 + 1)) (fun j => (L j).space)) :=
    QuotientAddGroup.borelSpace
  let : ∀ j, BorelSpace (SubspaceArrayTorus (Finset (Fin (0 + 1))) (L j).space) :=
    fun _ => QuotientAddGroup.borelSpace
  let : BorelSpace (SiteTorus (Finset (Fin (0 + 1))) (fun j => (L j).space)) :=
    Pi.borelSpace
  let : ∀ j, CompactSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)).toAddSubgroup) :=
    hL.euclideanLayerTorus_compact L hp hR
  let : ∀ j, BorelSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  exact {
    lattice := inferInstance
    coefficientCompact := inferInstance
    coefficientBorel := inferInstance
    rowCompact := inferInstance
    rowBorel := inferInstance
    siteBorel := inferInstance
    layer := fun j => probabilityAddHaar (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)).toAddSubgroup)
    layerInvariant := fun _ => inferInstance
    layerProbability := fun _ => inferInstance
    coefficient := probabilityAddHaar _
    coefficientInvariant := inferInstance
    coefficientProbability := inferInstance
    row := probabilityAddHaar _
    rowInvariant := inferInstance
    rowProbability := inferInstance }

noncomputable def PreparedHeights.paddedCanonicalSamplerMeasures
    {q : ℕ} {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hmq : m ≤ q) (hp : 0 ≤ p) (hR : 1 ≤ R) :
    (L.pad q).CanonicalSamplerMeasures K :=
  (hL.pad hmq hp).canonicalSamplerMeasures (L.pad q) K hp hR

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule MeasureTheory VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
    (K : Type) [Fintype K]

structure CanonicalSamplerData (M : ℕ) (pLate : ℝ) where
  measures : L.CanonicalSamplerMeasures K
  b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
    (euclideanSubspace (L j).space)ᗮ
  o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
    (euclideanSubspace (L j).space)
  bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
    (latticeSection (standardEuclideanLattice (L j).Coord)
      (euclideanSubspace (L j).space))
  span_eq : ∀ j, span ℤ (Set.range (b j)) =
    projectedIntegerLattice (euclideanSubspace (L j).space)
  chart_bound : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
    Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖
  inverse_chart_bound : ∀ j z,
    ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
      Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖
  covolume_bound : ∀ j,
    0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
    mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
      Real.exp (allocatedUniformChartLog (M : ℝ))
  integral_basis_bound : ∀ j a, ‖(bW j a).val‖ ≤
    Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)
  axis_bound : ∀ j i, (basisAxisScale (b j) i : ℝ) ≤
    Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)

noncomputable def PreparedHeights.canonicalPaddedSamplerData
    {q : ℕ} {pPrep pLate : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights pPrep R)
    (hmq : m ≤ q) (hpPrep : 0 ≤ pPrep) (hR : 1 ≤ R) (hPrepLate : pPrep ≤ pLate)
    (hRLate : (R : ℝ) ≤ Real.exp pLate)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcapLate : (preparationCoordinateCap q D T : ℝ) ≤ pLate) :
    (L.pad q).CanonicalSamplerData K (preparationCoordinateCap q D T) pLate :=
  Classical.choice (by
    obtain ⟨b, o, bW, hb, hchart, hinverse, hcov, hnorm, haxis⟩ :=
      hL.exists_padded_early_late_sampler_geometry L hmq hpPrep hR hPrepLate hRLate
        hsize ht hcapLate
    exact ⟨{
      measures := hL.paddedCanonicalSamplerMeasures L K hmq hpPrep hR
      b := b
      o := o
      bW := bW
      span_eq := hb
      chart_bound := hchart
      inverse_chart_bound := hinverse
      covolume_bound := hcov
      integral_basis_bound := hnorm
      axis_bound := haxis }⟩)

end Erdos3.RankPreparationFamily

end

end OAI

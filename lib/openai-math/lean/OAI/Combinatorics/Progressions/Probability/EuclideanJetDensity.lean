import OAI.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem siteImage_density_euclideanJet {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset α) U)] [BorelSpace (SiteTorus (Finset α) U)]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (ρ : Measure (CoefficientTorus (K := K) U)) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    let π := Set.rangeFactorization E
    let e := euclideanSiteImageHomeomorph U root D a ha hperiod
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet α (j.val + 1) => ν j))
    ∀ g : Set.range E → ℝ, Continuous g → ∀ {B : ℝ},
      (∀ y, g y ∈ Set.Icc (0 : ℝ) B) → (∫ y, g y ∂μ.map π) = 1 →
      ρ.map π = realDensityMeasure (μ.map π) g →
      let f := fun z => g (e.symm z)
      Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) B) ∧
        Integrable f ξ ∧ (∫ z, f z ∂ξ) = 1 ∧ (∀ y, f (e y) = g y) ∧
        ρ.map (euclideanCoefficientJetMap U root D
          (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))) =
          realDensityMeasure ξ f := by
  intro E π e ξ g hgc B hcap hmass hlaw f
  let eM := e.toMeasurableEquiv
  have hhaar : (μ.map π).map eM = ξ := euclideanSiteImageHomeomorph_haar U root D a ha hperiod μ ν
  have hfc : Continuous f := hgc.comp e.symm.continuous
  have hfb (z) : f z ∈ Set.Icc (0 : ℝ) B := hcap (e.symm z)
  let : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : BoundedBooleanJet α (j.val + 1) => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  have hfi : Integrable f ξ := Integrable.of_bound hfc.aestronglyMeasurable B
    (ae_of_all _ (fun z => by rw [Real.norm_of_nonneg (hfb z).1]; exact (hfb z).2))
  have hfvalue (y) : f (e y) = g y := congrArg g (e.symm_apply_apply y)
  have hfmass : (∫ z, f z ∂ξ) = 1 := by
    rw [← hhaar, integral_map_equiv]
    change (∫ y, g (e.symm (e y)) ∂μ.map π) = 1
    simpa only [Homeomorph.symm_apply_apply] using hmass
  refine ⟨hfc, hfb, hfi, hfmass, hfvalue, ?_⟩
  have hπ : Measurable π := (coefficientSiteTorusMap_continuous U _).rangeFactorization.measurable
  calc
    _ = (ρ.map π).map eM := (Measure.map_map eM.measurable hπ).symm
    _ = realDensityMeasure ξ f := by
      rw [hlaw, realDensityMeasure_map_equiv, hhaar]
      rfl

end Erdos3.VectorPolynomial

end

end OAI

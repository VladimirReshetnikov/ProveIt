import OAI.Combinatorics.Progressions.Estimates.CoefficientJetHaar
import OAI.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem siteImage_density_lowJet {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset α) U)] [BorelSpace (SiteTorus (Finset α) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus (BoundedBooleanJet α (j.val + 1)) (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus (BoundedBooleanJet α (j.val + 1)) (U j))]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (SubspaceArrayTorus (BoundedBooleanJet α (j.val + 1)) (U j)))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (ρ : Measure (CoefficientTorus (K := K) U)) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    let π := Set.rangeFactorization E
    let κ := fun y : Set.range E => siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val
    ∀ g : Set.range E → ℝ, Continuous g → ∀ {B : ℝ},
      (∀ y, g y ∈ Set.Icc (0 : ℝ) B) → (∫ y, g y ∂μ.map π) = 1 →
      ρ.map π = realDensityMeasure (μ.map π) g →
      ∃ f : LowBooleanJetTorus α U → ℝ,
        Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) B) ∧
        Integrable f (Measure.pi ν) ∧ (∫ z, f z ∂Measure.pi ν) = 1 ∧
        (∀ y, f (κ y) = g y) ∧
        ρ.map (coefficientBooleanJetTorusMap U root D
          (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))) =
          realDensityMeasure (Measure.pi ν) f := by
  intro E π κ g hgc B hcap hmass hlaw
  let ψ := lowJetSiteImageSection U root D a ha hperiod
  let f : LowBooleanJetTorus α U → ℝ := fun z => g (ψ z)
  have hfc : Continuous f := hgc.comp (lowJetSiteImageSection_continuous U root D a ha hperiod)
  have hfb (z) : f z ∈ Set.Icc (0 : ℝ) B := hcap (ψ z)
  have hvalue (y) : f (κ y) = g y := congrArg g (lowJetSiteImageSection_site U root D a ha hperiod y)
  have hκ : Measurable κ := ((siteBooleanJetTorusMap_continuous U
    (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))).comp
    (continuous_subtype_val : Continuous (Subtype.val : Set.range E → SiteTorus (Finset α) U))).measurable
  have hπ : Measurable π :=
    (coefficientSiteTorusMap_continuous U (integerAffineCube root D)).rangeFactorization.measurable
  have hp : MeasurePreserving κ (μ.map π) (Measure.pi ν) := ⟨hκ,
    coefficientSiteImage_booleanJet_haar U root D a ha hperiod
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
      (fun _ => Subtype.val_injective) (fun _ o => o.property) μ ν⟩
  have hfi : Integrable f (Measure.pi ν) := Integrable.of_bound hfc.aestronglyMeasurable B
    (ae_of_all _ (fun z => by rw [Real.norm_of_nonneg (hfb z).1]; exact (hfb z).2))
  have hfmass : (∫ z, f z ∂Measure.pi ν) = 1 := by
    rw [← hp.map_eq, integral_map hκ.aemeasurable hfc.aestronglyMeasurable]
    simp_rw [hvalue]
    exact hmass
  refine ⟨f, hfc, hfb, hfi, hfmass, hvalue, ?_⟩
  calc
    _ = (ρ.map π).map κ := (Measure.map_map hκ hπ).symm
    _ = (realDensityMeasure (μ.map π) g).map κ := congrArg (fun σ => σ.map κ) hlaw
    _ = realDensityMeasure (Measure.pi ν) f := by
      have hg : g = fun y => f (κ y) := funext (fun y => (hvalue y).symm)
      rw [hg]
      exact measurePreserving_realDensity_map (μ.map π) (Measure.pi ν) κ hp f
        hfc.measurable hfi (fun z => (hfb z).1)

end Erdos3.VectorPolynomial

end

end OAI

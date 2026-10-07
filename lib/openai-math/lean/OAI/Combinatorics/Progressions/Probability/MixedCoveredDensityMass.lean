import OAI.Combinatorics.Progressions.Estimates.MixedCoveredRowReindex
import OAI.Combinatorics.Progressions.Geometry.FiniteGoodSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem coveredJetArray_density_law (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
    (f : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) → ℝ)
    (hf : ∀ p, mixedCoveredJetCoordinates U o d p ∉ coveredJetSourceRegion U b d Ω → f p = 0) :
    (realDensityMeasure (coveredJetArrayReference U d) f).map
      (fun p => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d p)) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
      (restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1
        (fun x => f ((mixedCoveredJetEquiv U o d).symm x))) := by
  let e := mixedCoveredJetEquiv (O := O) (B := B) (n := n) U o d
  have he : MeasurePreserving e (coveredJetArrayReference U d) (coveredJetReference U d) :=
    mixedCoveredJetEquiv_measurePreserving U o d
  have hq := (coveredJetChart_continuous (O := O) U b hb bW d).measurable
  change (realDensityMeasure (coveredJetArrayReference U d) f).map
    (coveredJetChart U b hb bW d ∘ e) = _
  rw [← Measure.map_map hq e.measurable, realDensityMeasure_map_equiv, he.map_eq]
  apply coveredJetChart_density_law U b hb bW d ν Ω hΩm hΩ
  intro x hx
  apply hf
  change e (e.symm x) ∉ coveredJetSourceRegion U b d Ω
  simpa only [e.apply_symm_apply] using hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule Set
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

noncomputable def mixedCoveredJetRawReference : Measure (MixedCoveredJetSource I O E n d) :=
  (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
    (PMF.uniformOfFintype (∀ j, O j → E j → ZMod d)).toMeasure

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d

include hΩm hΩ

theorem mixedCoveredJet_density_law (f : MixedCoveredJetSource I O E n d → ℝ)
    (hf : ∀ z ∉ region, f z = 0) :
    Measure.map chart (realDensityMeasure (coveredJetArrayReference U d) f) =
      realDensityMeasure haar (restrictedChartDensity chart region 1 f) := by
  have h := coveredJetArray_density_law U o b hb bW d ν Ω hΩm hΩ f hf
  have he : restrictedChartDensity (coveredJetChart U b hb bW d)
      (coveredJetSourceRegion U b d Ω) 1 (fun z => f ((mixedCoveredJetEquiv U o d).symm z)) =
      restrictedChartDensity chart region 1 f := by
    apply restrictedChartDensity_eq_of_values chart region
      (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
    · intro z hz
      rw [mixedCoveredJetChart, restrictedChartDensity_apply _ _ _ _
        (coveredJetChart_injOn U b hb bW d Ω hΩ) hz, one_mul]
      exact congrArg f ((mixedCoveredJetEquiv U o d).symm_apply_apply z)
    · intro y hy
      apply restrictedChartDensity_zero
      rwa [← mixedCoveredJetChart_image U o b hb bW d Ω]
  rw [he] at h
  exact h

theorem mixedCoveredJet_normalized_density_law (f : MixedCoveredJetSource I O E n d → ℝ) :
    Measure.map chart (realDensityMeasure raw (Set.indicator region f)) =
      realDensityMeasure haar (restrictedChartDensity chart region 1
        (fun z => f z / coveredJetArrayScale (O := O) U)) := by
  have he : (fun z => Set.indicator region f z / coveredJetArrayScale (O := O) U) =
      Set.indicator region (fun z => f z / coveredJetArrayScale (O := O) U) := by
    funext z
    by_cases hz : z ∈ region
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, zero_div]
  unfold mixedCoveredJetRawReference
  rw [← coveredJetArrayReference_density U d (Set.indicator region f)]
  rw [he, mixedCoveredJet_density_law U o b hb bW d ν Ω hΩm hΩ _
    (fun z hz => Set.indicator_of_notMem hz _), restrictedChartDensity_indicator]

theorem mixedCoveredJet_normalized_lintegral (f : MixedCoveredJetSource I O E n d → ℝ) :
    (∫⁻ y, ENNReal.ofReal (restrictedChartDensity chart region 1
      (fun z => f z / coveredJetArrayScale (O := O) U) y) ∂haar) =
      ∫⁻ z in region, ENNReal.ofReal (f z) ∂raw := by
  have h := realDensityMeasure_lintegral_of_map raw haar chart
    ((coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d))
    (Set.indicator region f) _ (mixedCoveredJet_normalized_density_law U o b hb bW d ν Ω hΩm hΩ f)
  rw [h]
  have hS : MeasurableSet region := (coveredJetSourceRegion_measurable U b d Ω hΩm).preimage
    (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  have he : (fun z => ENNReal.ofReal (Set.indicator region f z)) =
      Set.indicator region (fun z => ENNReal.ofReal (f z)) := by
    funext z
    by_cases hz : z ∈ region
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, ENNReal.ofReal_zero]
  rw [he, lintegral_indicator hS]

end Erdos3.VectorPolynomial

end

end OAI

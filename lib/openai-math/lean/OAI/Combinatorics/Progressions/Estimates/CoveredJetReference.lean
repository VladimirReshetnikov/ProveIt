/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use the proved chart-source Borel instance and specify the chart index
family explicitly in the density law to avoid older instance-search
timeouts. The statements are unchanged. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Geometry.CoveredJetChart

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem normalizedCoveredReference_sigmaFinite {D R : Type*} [Fintype D] [Fintype R]
    {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)] (d : ℕ) [NeZero d] :
    SigmaFinite (normalizedCoveredReference (R := R) (n := n) W d) := by
  have hc : (ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice D) W)))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne'
  let : SigmaFinite ((ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
        ((volume : Measure W).prod (Measure.count : Measure (Fin n → ℤ)))) :=
    ennreal_smul_sigmaFinite ((volume : Measure W).prod (Measure.count : Measure (Fin n → ℤ))) _ hc
  unfold normalizedCoveredReference
  infer_instance

namespace VectorPolynomial

variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetReference (d : ℕ) [NeZero d] :
    Measure (CoveredJetChartSource U O B n d) :=
  Measure.pi (fun j => Measure.pi (fun _ : O j =>
    normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem coveredJetReference_sigmaFinite :
    SigmaFinite (coveredJetReference (O := O) (B := B) (n := n) U d) := by
  let : ∀ j, SigmaFinite (normalizedCoveredReference (R := B j) (n := n j)
      (euclideanSubspace (U j)) d) := fun j => normalizedCoveredReference_sigmaFinite _ d
  unfold coveredJetReference
  infer_instance

theorem coveredJetChart_reference_map (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    ((coveredJetReference U d).restrict (coveredJetSourceRegion U b d Ω)).map
      (coveredJetChart U b hb bW d) =
    (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))).restrict
      (coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω) := by
  let : ∀ j, SigmaFinite (normalizedCoveredReference (R := B j) (n := n j)
      (euclideanSubspace (U j)) d) := fun j => normalizedCoveredReference_sigmaFinite _ d
  let : ∀ j, BorelSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  let q := fun j => normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
  have hq (j) : Measurable (q j) := (normalizedCoveredChart_continuous _ (b j) (hb j) (bW j) d).measurable
  unfold coveredJetReference coveredJetSourceRegion coveredJetChart
  refine piChart_reference_map
    (fun j => Measure.pi (fun _ : O j => normalizedCoveredReference (R := B j) (n := n j)
      (euclideanSubspace (U j)) d))
    (fun j => Measure.pi (fun _ : O j => ν j))
    (fun j (x : O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) t => q j (x t))
    (fun j => Measurable.of_eval (fun t => (hq j).comp (measurable_pi_apply t))) _ ?_
  intro j
  refine piChart_reference_map
    (fun _ : O j => normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d)
    (fun _ : O j => ν j) (fun _ : O j => q j) (fun _ => hq j) _ ?_
  intro t
  exact normalizedCoveredChart_reference_map _ (b j) (hb j) (bW j) d (ν j) (hΩm j t) (hΩ j t)

theorem coveredJetChart_reference_region (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    ((coveredJetReference U d).restrict (coveredJetSourceRegion U b d Ω)).map
      (coveredJetChart U b hb bW d) =
    (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))).restrict
      (coveredJetTargetRegion U b hb d Ω) := by
  rw [coveredJetChart_reference_map U b hb bW d ν Ω hΩm hΩ, coveredJetChart_image]

theorem coveredJetChart_density_law (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
    (f : CoveredJetChartSource U O B n d → ℝ)
    (hf : ∀ x ∉ coveredJetSourceRegion U b d Ω, f x = 0) :
    (realDensityMeasure (coveredJetReference U d) f).map (coveredJetChart U b hb bW d) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
      (restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1 f) := by
  let : BorelSpace (CoveredJetChartSource U O B n d) := coveredJetChartSource_borel U d
  apply restrictedChartDensity_law (coveredJetChart (O := O) U b hb bW d)
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable
    (coveredJetSourceRegion_measurable U b d Ω hΩm)
    (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ) _ _ zero_le_one _ f hf
  simpa only [ENNReal.ofReal_one, one_smul] using
    coveredJetChart_reference_map U b hb bW d ν Ω hΩm hΩ

end VectorPolynomial

end Erdos3

end

end OAI

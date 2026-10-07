import OAI.Combinatorics.Progressions.Estimates.AllocatedCutoffCoveredEnvelope
import OAI.Combinatorics.Progressions.Estimates.AllocatedProductPrefactorMeasurable
import OAI.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowAmbient" => JetAmbientIndex rowTypes J

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "ampN" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖₊

variable (hbudgetRows : ∀ j, ((rowSets j).card + 1 : ℝ) *
  (Fintype.card (Finset α) * (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))
local notation "envelope" => allocatedCutoffCoveredEnvelope B U b S rowSets o hb bW d r
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

include hR hC hchart hbudgetRows hb bW in
theorem allocatedNormalizedProductTorusCutoff_mass (hσ1 : ∀ j, σ j ≤ 1) :
    Integrable (fun y => allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S
      (coveredJetAmbientTorus U d y)) haar ∧
    (∫ y, allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S
      (coveredJetAmbientTorus U d y) ∂haar) ≤
      allocatedUniformGridVolumeCap B rowSets r *
        (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) := by
  have hpoint : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4 := by
    intro j
    have hcost : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) :=
      mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))
    have hsite : (1 : ℝ) ≤ Fintype.card (Finset α) := by
      exact_mod_cast (show 1 ≤ Fintype.card (Finset α) from Fintype.card_pos)
    have hcost' := mul_le_mul_of_nonneg_right hsite hcost
    have hprod : 0 ≤ (Fintype.card (Finset α) : ℝ) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j))) :=
      mul_nonneg (Nat.cast_nonneg _) hcost
    have hrow : (1 : ℝ) ≤ (rowSets j).card + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (rowSets j).card]
    have hstep := mul_le_mul_of_nonneg_right hrow hprod
    simp only [one_mul] at hcost' hstep
    exact hcost'.trans (hstep.trans (hbudgetRows j))
  have heq : (fun y : EuclideanJetLayers U rowTypes => allocatedNormalizedProductTorusCutoff U b o r hr rowSets B S
      (coveredJetAmbientTorus U d y)) = fun y => amp * ‖cutoff y‖ :=
    funext (fun y => allocatedNormalizedProductTorusCutoff_pullback U b o r hr hR C hC hchart hpoint rowSets B S hb bW d y)
  rw [heq]
  have hle (y : EuclideanJetLayers U rowTypes) : amp * ‖cutoff y‖ ≤ envelope y :=
    allocatedProductIdealNormalizer_cutoff_le_covered_envelope B U b S rowSets o hb bW d r hr
      hR C hC hchart hbudgetRows y
  have hE := allocatedCutoffCoveredEnvelope_integrable B U b S rowSets o hb bW d r hR ν
  have hm : Measurable (fun y => amp * ‖cutoff y‖) := measurable_const.mul
    (allocatedProductSiteCutoff_measurable B U b S rowSets d r hr hb o bW).norm
  have hi : Integrable (fun y => amp * ‖cutoff y‖) haar := hE.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hle y))
  refine ⟨hi, ?_⟩
  have hmass := allocatedCutoffCoveredEnvelope_integral_abs_le B U b S rowSets o hb bW d r hR ν hσ1
  have hmass' : (∫ y, envelope y ∂haar) ≤ allocatedCutoffGridVolumeCap B U b S rowSets r *
      (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) := by
    simpa only [abs_of_nonneg (allocatedCutoffCoveredEnvelope_nonneg B U b S rowSets o hb bW d r hR _)] using hmass
  exact (integral_mono hi hE hle).trans (hmass'.trans
    (mul_le_mul_of_nonneg_right (allocatedCutoffGridVolumeCap_le_uniform B U b S rowSets r) (by positivity)))

end Erdos3.VectorPolynomial

end

end OAI

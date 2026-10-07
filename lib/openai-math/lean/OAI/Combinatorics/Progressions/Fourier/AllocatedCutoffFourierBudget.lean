import OAI.Combinatorics.Progressions.Dynamics.AllocatedCutoffLipschitzBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α]
variable (rowSets : Fin m → Finset (Finset α))
variable (C V : Fin m → ℝ≥0) {P : ℝ} (hnum : AllocatedSourceNumerics B U b S C V P)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "H" => (2 : ℝ) ^ Fintype.card α

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "ampN" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖₊

include hnum in
theorem allocatedNormalizedCutoff_fourier_budget
    (hR : ∀ j, 0 < R j)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (r : ℝ≥0) (hr : 1 ≤ r) {η E Psp : ℝ}
    (hE : 0 ≤ E) (hPsp : 0 ≤ Psp) (hηE : η⁻¹ ≤ Real.exp E) :
    let L := allocatedCutoffFourierLog m (Fintype.card α) P (normalizedSiteCutoffBound : ℝ) E
    let Q := allocatedCutoffSamplingLog m (Fintype.card α) P (normalizedSiteCutoffBound : ℝ) E Psp
    0 ≤ L ∧ 0 ≤ Q ∧ Psp ≤ Q ∧ P ≤ Q ∧
      (Fintype.card (JetAmbientIndex rowTypes J) : ℝ) ≤ L ∧ η⁻¹ ≤ Real.exp L ∧
      ((ampN * (Fintype.card (Finset α) *
        (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
          ((⟨Real.exp P, (Real.exp_pos P).le⟩ : ℝ≥0) * ∑ j, C j * Fintype.card (J j))) *
            ∑ j, (Finset.card (rowSets j) : ℝ≥0)))) : ℝ) ≤ Real.exp L ∧
      Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp Q ∧
      Real.exp (2 * L * (2 * L + 2) ^ 4) * amp ≤ Real.exp Q := by
  intro L Q
  obtain ⟨hL, haL, hlL, hdL, heL, hpL⟩ := allocatedCutoffFourierLog_bounds m (Fintype.card α)
    hnum.nonneg normalizedSiteCutoffBound.coe_nonneg hE
  obtain ⟨hQ, hspQ, hLQ, hfQ, hcQ⟩ := allocatedCutoffSamplingLog_bounds m (Fintype.card α)
    hnum.nonneg normalizedSiteCutoffBound.coe_nonneg hE hPsp
  have hd := (allocatedNormalizedCutoff_dimensions B U b S rowSets C V hnum).2.2.2
  have hl := allocatedNormalizedCutoff_lipschitz_budget B U b S rowSets C V hnum hR hV r hr
  have ha : amp ≤ Real.exp (allocatedCutoffAmplitudeLog m (Fintype.card α) P) := by
    simpa only [allocatedCutoffAmplitudeLog, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      allocatedProductIdealNormalizer_source_budget B U b S rowSets hR C V hnum hV
  refine ⟨hL, hQ, hspQ, hpL.trans hLQ, hd.trans hdL,
    hηE.trans (Real.exp_le_exp.mpr heL), hl.trans (Real.exp_le_exp.mpr hlL),
    Real.exp_le_exp.mpr hfQ, ?_⟩
  calc
    _ ≤ Real.exp (2 * L * (2 * L + 2) ^ 4) * Real.exp L :=
      mul_le_mul_of_nonneg_left (ha.trans (Real.exp_le_exp.mpr haL)) (Real.exp_pos _).le
    _ = Real.exp (2 * L * (2 * L + 2) ^ 4 + L) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hcQ

end Erdos3.VectorPolynomial

end

end OAI

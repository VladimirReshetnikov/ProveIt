import OAI.Combinatorics.Progressions.Dynamics.AllocatedCanonicalBudget
import OAI.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff

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

include hnum in
theorem allocatedNormalizedCutoff_dimensions :
    (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ 2 * m * P ∧
      (∑ j, (Finset.card (rowSets j) : ℝ)) ≤ m * H ∧
      (∑ j, (C j : ℝ) * Fintype.card (J j)) ≤ m * (Real.exp P * P) ∧
      (Fintype.card (JetAmbientIndex rowTypes J) : ℝ) ≤ (m * H) * P := by
  have haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ 2 * m * P := by
    simp only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin,
      Nat.cast_sum, Nat.cast_add]
    calc
      _ ≤ ∑ _j : Fin m, 2 * P := Finset.sum_le_sum (fun j _ => by
        linarith [hnum.real_axes j, hnum.integer_axes j])
      _ = _ := by simp; ring
  have hrows : (∑ j, (Finset.card (rowSets j) : ℝ)) ≤ m * H := by
    simpa only [Nat.cast_sum, Fintype.card_coe] using
      (allocatedIdealNormalizer_row_counts (I := I) (n := n) rowSets
        hnum.nonneg hnum.real_axes hnum.integer_axes).1
  refine ⟨haxes, hrows, ?_, ?_⟩
  · calc
      _ ≤ ∑ _j : Fin m, Real.exp P * P := Finset.sum_le_sum (fun j _ =>
        mul_le_mul (hnum.chart j) (hnum.ambient_axes j) (Nat.cast_nonneg _) (Real.exp_pos P).le)
      _ = _ := by simp
  · simp only [JetAmbientIndex, Fintype.card_sigma, Fintype.card_prod,
      Nat.cast_sum, Nat.cast_mul, Fintype.card_coe]
    calc
      _ ≤ ∑ j, (Finset.card (rowSets j) : ℝ) * P := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hnum.ambient_axes j) (Nat.cast_nonneg _))
      _ = (∑ j, (Finset.card (rowSets j) : ℝ)) * P := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hrows hnum.nonneg

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "ampN" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖₊

include hnum in
theorem allocatedNormalizedCutoff_lipschitz_budget
    (hR : ∀ j, 0 < R j)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (r : ℝ≥0) (hr : 1 ≤ r) :
    ((ampN * (Fintype.card (Finset α) *
      (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
        ((⟨Real.exp P, (Real.exp_pos P).le⟩ : ℝ≥0) * ∑ j, C j * Fintype.card (J j))) *
          ∑ j, (Finset.card (rowSets j) : ℝ≥0)))) : ℝ) ≤
      Real.exp (allocatedCutoffLipschitzLog m (Fintype.card α) P (normalizedSiteCutoffBound : ℝ)) := by
  obtain ⟨haxes, hrows, hchart, _⟩ := allocatedNormalizedCutoff_dimensions B U b S rowSets C V hnum
  have hamp : amp ≤ Real.exp (allocatedCutoffAmplitudeLog m (Fintype.card α) P) := by
    simpa only [allocatedCutoffAmplitudeLog, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      allocatedProductIdealNormalizer_source_budget B U b S rowSets hR C V hnum hV
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : (1 : ℝ) ≤ 2 * r := by linarith
  have hcut : (Fintype.card (LayerSamplerAxis I n) : ℝ) * normalizedSiteCutoffBound / (2 * r) ≤
      (2 * m * P) * normalizedSiteCutoffBound :=
    (div_le_self (by positivity) hden).trans
      (mul_le_mul_of_nonneg_right haxes normalizedSiteCutoffBound.coe_nonneg)
  let F : ℝ := 2 * normalizedSiteCutoffBound * (m : ℝ) ^ 3 * H ^ 2 * P ^ 2
  have hF : F ≤ Real.exp F := by linarith [Real.add_one_le_exp F]
  have hexp : Real.exp (2 * P) = Real.exp P * Real.exp P := by
    rw [show 2 * P = P + P by ring, Real.exp_add]
  simp only [NNReal.coe_mul, NNReal.coe_sum, NNReal.coe_natCast, coe_nnnorm]
  change amp * ((Fintype.card (Finset α) : ℝ) *
    ((((Fintype.card (LayerSamplerAxis I n) : ℝ) * normalizedSiteCutoffBound / (2 * r)) *
      (Real.exp P * ∑ j, (C j : ℝ) * Fintype.card (J j))) *
        ∑ j, (Finset.card (rowSets j) : ℝ))) ≤ _
  simp only [Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ ≤ Real.exp (allocatedCutoffAmplitudeLog m (Fintype.card α) P) *
        (H * ((((2 * m * P) * normalizedSiteCutoffBound) *
          (Real.exp P * (m * (Real.exp P * P)))) * (m * H))) := by
      exact normalizedCutoff_product_bound hamp hcut
        (mul_le_mul_of_nonneg_left hchart (Real.exp_pos P).le) hrows
        (Real.exp_pos _).le (pow_nonneg (by norm_num) _)
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) normalizedSiteCutoffBound.coe_nonneg)
          (mul_nonneg (by norm_num) r.coe_nonneg))
        (mul_nonneg (Real.exp_pos P).le (Finset.sum_nonneg (fun j _ =>
          mul_nonneg (C j).coe_nonneg (Nat.cast_nonneg _))))
        (Finset.sum_nonneg (fun j _ => Nat.cast_nonneg (Finset.card (rowSets j))))
    _ = Real.exp (allocatedCutoffAmplitudeLog m (Fintype.card α) P + 2 * P) * F := by
      rw [Real.exp_add, hexp]
      dsimp only [F]
      ring
    _ ≤ Real.exp (allocatedCutoffAmplitudeLog m (Fintype.card α) P + 2 * P) * Real.exp F :=
      mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      rfl

end Erdos3.VectorPolynomial

end

end OAI

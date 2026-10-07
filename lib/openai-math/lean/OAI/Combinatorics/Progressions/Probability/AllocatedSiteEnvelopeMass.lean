import OAI.Combinatorics.Progressions.Estimates.AllocatedSiteBufferLog

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

local notation "radius" => idealSiteEnvelopeRadius α m
local notation "reference" => allocatedLongJetReference B U b S jets
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := jets) a)

theorem allocatedIdealSiteEnvelope_integrable (hR : ∀ j, 0 < R j) :
    Integrable (allocatedIdealSiteEnvelope (α := α) B U b S) reference := by
  let box := allocatedPhysicalLongJetBox B U b S jets radius
  let Jv : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
  have hg : Integrable (box.indicator (fun _ => Jv⁻¹)) reference :=
    (integrableOn_const (allocatedPhysicalLongJetBox_measure_lt_top B U b S jets radius).ne).integrable_indicator
      (allocatedPhysicalLongJetBox_measurable B U b S jets radius)
  apply hg.mono' (allocatedIdealSiteEnvelope_measurable B U b S).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (allocatedIdealSiteEnvelope_nonneg B U b S hR z)]
  exact allocatedIdealSiteEnvelope_le_box B U b S hR z

theorem allocatedIdealSiteEnvelope_integral_le (hR : ∀ j, 0 < R j)
    (hσ1 : ∀ j, σ j ≤ 1) :
    (∫ z, allocatedIdealSiteEnvelope (α := α) B U b S z ∂reference) ≤
      (2 * radius + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) * scale := by
  let box := allocatedPhysicalLongJetBox B U b S jets radius
  let Jv : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
  have hJv : 0 < Jv := Finset.prod_pos (fun q _ => hR q.1.val.1)
  have hbox := allocatedPhysicalLongJetBox_measurable B U b S jets radius
  have hg : Integrable (box.indicator (fun _ => Jv⁻¹)) reference :=
    (integrableOn_const (allocatedPhysicalLongJetBox_measure_lt_top B U b S jets radius).ne).integrable_indicator hbox
  have hrad : 0 ≤ radius := (idealSiteEnvelopeRadius_pos α m).le
  calc
    _ ≤ ∫ z, box.indicator (fun _ => Jv⁻¹) z ∂reference :=
      integral_mono (allocatedIdealSiteEnvelope_integrable B U b S hR) hg
        (allocatedIdealSiteEnvelope_le_box B U b S hR)
    _ = Jv⁻¹ * (reference).real box := by
      rw [integral_indicator hbox, setIntegral_const, smul_eq_mul]
      ring
    _ ≤ Jv⁻¹ * ((2 * radius + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) * Jv * scale) :=
      mul_le_mul_of_nonneg_left
        (allocatedPhysicalLongJetBox_measure_bound B U b S jets hR hσ1 hrad) (inv_nonneg.mpr hJv.le)
    _ = _ := by field_simp [hJv.ne']

theorem allocatedIdealSiteEnvelope_normalized_integral_le (hR : ∀ j, 0 < R j)
    (hσ1 : ∀ j, σ j ≤ 1) :
    (∫ z, allocatedIdealSiteEnvelope (α := α) B U b S z / scale ∂reference) ≤
      (2 * radius + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) := by
  have hscale : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  rw [integral_div]
  exact (div_le_iff₀ hscale).mpr (allocatedIdealSiteEnvelope_integral_le B U b S hR hσ1)

end Erdos3.VectorPolynomial

end

end OAI

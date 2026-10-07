import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedBooleanSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Output" => (Σ _e : Row, Unit)

omit [∀ index, DecidableEq (B index)] in
theorem allocatedSlicedNormalizedIdeal_norm_le [∀ index, DecidableEq (B index)]
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (r : Coeff → ℝ) (hr : ∀ j, |r j| ≤ 1)
    (x : Endpoint → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    ‖allocatedSlicedNormalizedIdeal B U basis S lower width r x‖ ≤ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro o
  have hp := principalSliceValue_abs_le
    (jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B)) (fun e j => r ⟨e.2,j⟩) o.1)
    (lower o.1.2) (width o.1.2) (hwidth o.1.2)
    (fun j => x ⟨o.1,j⟩) (fun j => hx _)
  have hm := jointSlicedProfilePrincipal_unit_mass degree axis (fun e j => r ⟨e.2,j⟩) (fun e j => hr _) o.1
  have hc : |(1 / 4 : ℝ) * r ⟨o.1.2, constantCoefficientSlot _ _⟩| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    exact mul_le_of_le_one_right (by norm_num) (hr _)
  change |(1 / 4 : ℝ) * r ⟨o.1.2, constantCoefficientSlot _ _⟩ +
    principalSliceValue _ _ _ _| ≤ 2
  exact (abs_add_le _ _).trans ((add_le_add hc (hp.trans hm)).trans (by norm_num))

theorem allocatedSlicedAveragedIdealDensity_zero_off_ball
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (z : Output → ℝ) (hz : 2 < ‖z‖) :
    allocatedSlicedAveragedIdealDensity B U basis S hB lower width z = 0 := by
  have hd := allocatedSlicedAveragedIdealDensity_law_probability B U basis S hB lower width ha hδ hprincipal hw hl
  have hb := allocatedSlicedAveragedIdealDensity_cap_lipschitz B U basis S hB lower width ha hδ hprincipal hw hl
  have hm := allocatedSlicedNormalizedIdeal_measurable B U basis S lower width
  apply continuousDensity_zero_off_closed volume _ hb.2.continuous hd.2.1 (S := Metric.closedBall 0 2) Metric.isClosed_closedBall ?_ z
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)
  rw [← hd.1]
  apply (ae_map_iff hm.aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
  apply (Measure.ae_prod_iff_ae_ae (Metric.isClosed_closedBall.measurableSet.preimage hm)).mpr
  filter_upwards [unitCoefficientSource_abs_le Coeff] with r hr
  filter_upwards [unitBoxMeasure_ae] with x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact allocatedSlicedNormalizedIdeal_norm_le B U basis S lower width hwidth r hr x
    (fun j => by rw [abs_of_nonneg (hx j).1.le]; exact (hx j).2)

end Erdos3.VectorPolynomial

end

end OAI

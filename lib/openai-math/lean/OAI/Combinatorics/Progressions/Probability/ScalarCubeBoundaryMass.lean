import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod
import OAI.Combinatorics.Progressions.Estimates.ScalarCubeBoundaryCost
import OAI.Combinatorics.Progressions.Estimates.ScalarCubeBoundaryVolume

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def scalarCubeMeasure (α : Type*) [Fintype α] [DecidableEq α] :
    Measure (Option α → ℝ) :=
  (volume (scalarCubeDomain α))⁻¹ • volume.restrict (scalarCubeDomain α)

instance scalarCubeMeasure_probability (α : Type*) [Fintype α] [DecidableEq α] :
    IsProbabilityMeasure (scalarCubeMeasure α) := by
  constructor
  simp only [scalarCubeMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (scalarCubeDomain_volume_pos α).ne' (scalarCubeDomain_volume_lt_top α).ne

theorem scalarCubeMeasure_real_apply {α : Type*} [Fintype α] [DecidableEq α]
    (s : Set (Option α → ℝ)) (hs : MeasurableSet s) :
    (scalarCubeMeasure α).real s = scalarCubeDomainDensity α * volume.real (scalarCubeDomain α ∩ s) := by
  rw [scalarCubeMeasure, measureReal_ennreal_smul_apply, measureReal_restrict_apply hs,
    ENNReal.toReal_inv, Set.inter_comm]
  rfl

theorem scalarCubeMeasure_integral {α : Type*} [Fintype α] [DecidableEq α]
    (f : (Option α → ℝ) → ℝ) :
    (∫ a, f a ∂scalarCubeMeasure α) = scalarCubeDomainDensity α * ∫ a in scalarCubeDomain α, f a := by
  rw [scalarCubeMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rfl

theorem scalarCubeMeasure_ae_domain (α : Type*) [Fintype α] [DecidableEq α] :
    ∀ᵐ a ∂scalarCubeMeasure α, a ∈ scalarCubeDomain α := by
  apply ae_iff.mpr
  change scalarCubeMeasure α (scalarCubeDomain α)ᶜ = 0
  simp [scalarCubeMeasure, Measure.smul_apply,
    Measure.restrict_apply (scalarCubeDomain_isOpen α).measurableSet.compl]

theorem scalarCubeMeasure_face_bound {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) {u : ℝ} (hu : 0 ≤ u) :
    (scalarCubeMeasure α).real {a | scalarCubeFace i a < u} ≤
      scalarCubeDomainDensity α * (2 : ℝ) ^ Fintype.card α * u := by
  rw [scalarCubeMeasure_real_apply _ (measurableSet_lt
    (scalarCubeFace_contDiff i).continuous.measurable measurable_const)]
  have h := mul_le_mul_of_nonneg_left (scalarCubeFaceStrip_volume_le i hu) (scalarCubeDomainDensity_pos α).le
  exact h.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def oneCubeEndpointEquiv : (Option (Fin 1) → ℝ) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).trans
    (((MeasurableEquiv.funUnique (Fin 1) ℝ).prodCongr (MeasurableEquiv.refl ℝ)).trans
      ((MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ).trans (MeasurableEquiv.shearAddRight ℝ)))

@[simp] theorem oneCubeEndpointEquiv_apply (a : Option (Fin 1) → ℝ) :
    oneCubeEndpointEquiv a = (a none, a none + a (some 0)) := rfl

theorem oneCubeEndpointEquiv_volume :
    MeasurePreserving oneCubeEndpointEquiv volume (volume.prod volume) := by
  have hopt : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ))
      volume (volume.prod volume) := by
    have hsymm : MeasurePreserving
        (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm
        (volume.prod volume) volume :=
      ⟨MeasurableEquiv.measurable _, Measure.pi_map_piOptionEquivProd (fun _ => volume)⟩
    exact hsymm.symm _
  exact (measurePreserving_prod_add volume volume).comp
    ((Measure.measurePreserving_swap (μ := volume) (ν := volume)).comp
      (((volume_preserving_funUnique (Fin 1) ℝ).prod (MeasurePreserving.id volume)).comp hopt))

theorem scalarCubeDomain_one :
    scalarCubeDomain (Fin 1) =
      oneCubeEndpointEquiv ⁻¹' ((Set.Ioo (0 : ℝ) 1) ×ˢ Set.Ioo (0 : ℝ) 1) := by
  ext a
  simp only [Set.mem_preimage, oneCubeEndpointEquiv_apply, Set.mem_prod]
  constructor
  · intro ha
    exact ⟨by simpa only [scalarCubeValue_empty] using ha ∅,
      by simpa only [scalarCubeValue_singleton] using ha {0}⟩
  · rintro ⟨h0, h1⟩ t
    have ht : t = ∅ ∨ t = {0} := by
      apply Finset.subset_singleton_iff.mp
      intro i hi
      have hi0 : i = 0 := Subsingleton.elim _ _
      simpa only [Finset.mem_singleton] using hi0
    rcases ht with rfl | rfl
    · simpa only [scalarCubeValue_empty] using h0
    · simpa only [scalarCubeValue_singleton] using h1

theorem scalarCubeDomain_one_volume : volume (scalarCubeDomain (Fin 1)) = 1 := by
  rw [scalarCubeDomain_one]
  rw [oneCubeEndpointEquiv_volume.measure_preimage
    ((measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet)]
  simp

theorem scalarCubeMeasure_one_endpoints :
    (scalarCubeMeasure (Fin 1)).map oneCubeEndpointEquiv =
      unitScalarMeasure.prod unitScalarMeasure := by
  rw [scalarCubeMeasure, scalarCubeDomain_one_volume, inv_one, one_smul,
    scalarCubeDomain_one]
  rw [(oneCubeEndpointEquiv_volume.restrict_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo)).map_eq]
  rw [← Measure.prod_restrict]
  simp only [unitScalarMeasure, restrict_Ioo_eq_restrict_Ioc]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeBoundaryConstant (α : Type*) [Fintype α] [DecidableEq α] : ℝ :=
  4 * scalarCubeDomainDensity α * ((2 : ℝ) ^ Fintype.card α) ^ 2

theorem scalarCubeBoundaryConstant_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeBoundaryConstant α := by
  have h := scalarCubeDomainDensity_pos α
  unfold scalarCubeBoundaryConstant
  positivity

theorem scalarCubeBoundaryCutoff_mass_loss (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    (∫ a, 1 - inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace a
      ∂scalarCubeMeasure α) ≤ scalarCubeBoundaryConstant α * r := by
  apply (inequalityBoundaryCutoff_integral_loss_le (scalarCubeMeasure α) _ (fun _ => hr)
    scalarCubeFace (fun i => (scalarCubeFace_contDiff i).continuous.measurable)).trans
  calc
    _ ≤ ∑ _i : Bool × Finset α,
        scalarCubeDomainDensity α * (2 : ℝ) ^ Fintype.card α * (2 * r) :=
      Finset.sum_le_sum (fun i _ => scalarCubeMeasure_face_bound i (by positivity))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, scalarCubeFace_card, nsmul_eq_mul]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, scalarCubeBoundaryConstant]
      ring

end Erdos3

end

end OAI

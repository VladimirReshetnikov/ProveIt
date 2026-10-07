import OAI.Combinatorics.Progressions.Probability.BlockCubeDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem coordinateReindex_measurePreserving {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) : MeasurePreserving (fun x : J → ℝ => x ∘ e) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : I => ℝ) e.symm
  convert h using 1
  funext x i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

def reindexedBlockCubeDomain {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] {N : ℕ} (e : BlockParameter B F α ≃ Fin N) : Set (Fin N → ℝ) :=
  (fun x => x ∘ e) ⁻¹' blockCubeDomain B F α

theorem reindexedBlockCubeDomain_measurable {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α] {N : ℕ} (e : BlockParameter B F α ≃ Fin N) :
    MeasurableSet (reindexedBlockCubeDomain e) :=
  (blockCubeDomain_measurable B F α).preimage (coordinateReindex_measurePreserving e).measurable

theorem reindexedBlockCubeDomain_box {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α] {N : ℕ} (e : BlockParameter B F α ≃ Fin N)
    {x : Fin N → ℝ} (hx : x ∈ reindexedBlockCubeDomain e) (j : Fin N) : |x j| ≤ 1 := by
  have h := blockCubeDomain_box hx (e.symm j)
  simpa only [Function.comp_apply, e.apply_symm_apply] using h

theorem blockCubeMeasure_real_reindex {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α] {N : ℕ} (e : BlockParameter B F α ≃ Fin N)
    (s : Set (BlockParameter B F α → ℝ)) (hs : MeasurableSet s) :
    (blockCubeMeasure B F α).real s = scalarCubeDomainDensity α ^ Fintype.card (B × F) *
      volume.real (reindexedBlockCubeDomain e ∩ {x | x ∘ e ∈ s}) := by
  rw [blockCubeMeasure_real_apply_domain s hs]
  have hm := (coordinateReindex_measurePreserving e).measureReal_preimage
    ((blockCubeDomain_measurable B F α).inter hs).nullMeasurableSet
  rw [← hm]
  rfl

end Erdos3

end

end OAI

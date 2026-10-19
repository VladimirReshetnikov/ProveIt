import GowersSzemeredi.Proofs05BoxTransport

/-! Transport modular index partitions along a proper arithmetic progression. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem modAPAffine_image_indexInterval {N : Nat} [NeZero N] (P : ModAP N) :
    (modInterval N 0 P.length).carrier.image (fun t => P.start + P.step * t) = P.carrier := by
  rw [modInterval_zero_carrier, Finset.image_image, section5_carrier_eq_image_range]
  apply Finset.image_congr
  intro t _
  simp only [Function.comp_apply, section5IndexPoint, mul_comm]

theorem modAPAffine_partition {N m : Nat} [NeZero N] (P : ModAP N)
    (hP : P.IsProper) (R : Fin m → ModAP N)
    (hR : IsPartition (fun j => (R j).carrier) (modInterval N 0 P.length).carrier) :
    IsPartition (fun j => (modAPAffine P (R j)).carrier) P.carrier := by
  refine ⟨fun x => ?_, fun i j hij => ?_⟩
  · rw [← modAPAffine_image_indexInterval P]
    simp only [modAPAffine_carrier, Finset.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨j, hj⟩ := (hR.1 t).mp ht
      exact ⟨j, t, hj, rfl⟩
    · rintro ⟨j, t, ht, rfl⟩
      exact ⟨t, (hR.1 t).mpr ⟨j, ht⟩, rfl⟩
  · simp only [modAPAffine_carrier, Finset.disjoint_left, Finset.mem_image]
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
    obtain rfl := modAP_affine_injective_on_indices P hP
      (hR.cell_subset j ht) (hR.cell_subset i hs) hts
    exact Finset.disjoint_left.mp (hR.2 i j hij) hs ht

end LeanProofs.GowersSzemeredi

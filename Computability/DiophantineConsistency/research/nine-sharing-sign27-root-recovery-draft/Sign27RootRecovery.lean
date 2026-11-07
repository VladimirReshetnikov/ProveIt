import DiophantineConsistency.SharingSign28Squares

/-! SOURCE-ONLY: abstract normalized-root recovery from a ring equality. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27RootRecovery
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem recover (x y : V) (h : ι x * ι x = ι y + 1) :
    ∃ u : V, x = u + 1 ∧ y = u * (u + 2) := by
  rcases zero_or_succ x with h0 | ⟨u, hu⟩
  · have hp : (0 : DiffRing V) < ι y + 1 :=
      add_pos_of_nonneg_of_pos (ι_nonneg y) zero_lt_one
    have hz : (0 : DiffRing V) = ι y + 1 := by simpa [h0] using h
    exact False.elim ((ne_of_gt hp) hz.symm)
  · refine ⟨u, hu, ?_⟩
    have huR : ι x = ι u + 1 := by rw [hu, map_add, map_one]
    have hid : (ι u + 1) * (ι u + 1) = ι u * (ι u + 2) + 1 := by ring
    rw [huR, hid] at h
    have hyR : ι y = ι u * (ι u + 2) := (add_right_cancel h).symm
    apply ι_injective
    simpa only [map_mul, map_add, map_ofNat] using hyR
end DiophantineConsistency.Sign27RootRecovery
#print axioms DiophantineConsistency.Sign27RootRecovery.recover

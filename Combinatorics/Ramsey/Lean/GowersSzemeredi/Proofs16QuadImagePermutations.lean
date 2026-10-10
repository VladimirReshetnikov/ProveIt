import GowersSzemeredi.Proofs16ColumnImageBridges

/-! Domain-respecting permutations used in the second shared-bridge step. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem column_quad_image_swap_middle {N K : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (rho : Real) (a b c d : ZMod N) (h : ColumnQuadImageRelation T L rho K a b c d) :
    ColumnQuadImageRelation T L rho K a c b d := by
  apply (image_card_le_of_eq_on_subset (columnQuadCommonDomain T rho a c b d)
    (columnQuadCommonDomain T rho a b c d) _ _ ?_ ?_).trans h
  · intro y hy
    obtain ⟨_, ha, hc, hb, hd⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hb, hc, hd⟩
  · intro y _
    dsimp only [columnQuadDefect]
    ring

/-- Restricting a local Freiman domain to a smaller radius preserves it. -/
theorem column_freiman_smaller_radius {N : Nat} [NeZero N]
    (T : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho r : Real} (hr : r ≤ rho)
    (hf : IsFreimanLinearOn (bohr T rho) f) : IsFreimanLinearOn (bohr T r) f := by
  intro a b c d ha hb hc hd he
  exact hf a b c d (bohr_mono_radius T hr ha) (bohr_mono_radius T hr hb)
    (bohr_mono_radius T hr hc) (bohr_mono_radius T hr hd) he

end LeanProofs.GowersSzemeredi

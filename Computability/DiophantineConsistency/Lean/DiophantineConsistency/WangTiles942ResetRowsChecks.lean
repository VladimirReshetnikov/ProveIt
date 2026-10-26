import DiophantineConsistency.WangTiles942ResetRows
import DiophantineConsistency.WangTiles942StripGeometry

/-! Focused checks: arbitrary signed intervals, singleton interiors,
all local reset/finish variants, indispensable seam exclusion, and the
actual marked-plane geometry supplied without a uniform-row premise. -/

namespace DiophantineConsistency.WangTiles942ResetRowsChecks

open WangTiles942 WangTiles942Language WangTiles942ResetRows
  WangTiles942Periodic WangTiles942StripGeometry

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- Both induction directions are instantiated at a negative seed; the
-- interval is not centered at that seed or at the distinguished origin.
example (P : ℤ → Prop) (h : P (-4))
    (hn : ∀ x, -9 < x → x+1 < 3 → P x → P (x+1))
    (hp : ∀ x, -9 < x-1 → x < 3 → P x → P (x-1)) : P (-8) ∧ P 2 := by
  have hh := interval_propagate P (-9) 3 (-4) (by omega) (by omega) h hn hp
  exact ⟨hh (-8) (by omega) (by omega), hh 2 (by omega) (by omega)⟩

-- A one-point interior needs no usable neighboring edge.
example (P : ℤ → Prop) (z : ℤ) (h : P z) :
    ∀ x, z-1 < x → x < z+1 → P x := by
  apply interval_propagate P (z-1) (z+1) z (by omega) (by omega) h
  · intro x hl hr; omega
  · intro x hl hr; omega

example (p : ℕ) (hp : p ∈ [434,435,436]) :
    ResetTile (⟨1,438,1,p⟩ : Tile) := ⟨p,hp,rfl⟩

example (a b : Fin 2) : FinishTile (⟨0,432*a.val+b.val,0,438⟩ : Tile) :=
  ⟨a,b,rfl⟩

-- Reset status does not assert that different south labels are identical.
example : ResetTile (⟨1,438,1,434⟩ : Tile) ∧
    ResetTile (⟨1,438,1,436⟩ : Tile) ∧
    (⟨1,438,1,434⟩ : Tile) ≠ ⟨1,438,1,436⟩ := by
  refine ⟨⟨434,by decide,rfl⟩,⟨436,by decide,rfl⟩,?_⟩
  intro he
  have hs := congrArg Tile.south he
  norm_num at hs

-- An actual seam has both horizontal colors1 and still is not a reset.
example : Allowed (⟨1,437,1,437⟩ : Tile) ∧
    ¬ ResetTile (⟨1,437,1,437⟩ : Tile) := by
  refine ⟨Allowed.seam (1 : Fin 3) (1 : Fin 3),?_⟩
  intro h
  have hn := h.north
  norm_num at hn

-- The root geometry theorem discharges the entire nonseam premise, and
-- actual plane matching fixes both directions. Only one south438 remains
-- as a trigger; no finish/reset row or machine-run condition is supplied.
theorem marked_finish_trigger {N L R : ℕ} [NeZero N]
    {s : ℤ} {a : ZMod N → Fin 942} (h : MarkedWord N s a)
    (hg : PersistentStrip (plane N s a) N L R) (x₀ t : ℤ)
    (hl₀ : -(L : ℤ) < x₀) (hr₀ : x₀ < (R : ℤ))
    (hs : (plane N s a x₀ t).south = 438) :
    ∀ x, -(L : ℤ) < x → x < (R : ℤ) →
      ResetTile (plane N s a x (t+1)) ∧
      (plane N s a x t).south = 438 ∧ FinishTile (plane N s a x t) := by
  exact strip_finish_and_reset_of_south438 (plane N s a) (-(L : ℤ)) (R : ℤ) x₀ t
    (fun x τ _ _ => plane_allowed N s a x τ)
    (fun x τ _ _ => plane_east_matching h x τ)
    (fun x τ _ _ => plane_time_matching h x τ)
    (fun x τ hl hr => (hg.interior x hl hr τ).1) hl₀ hr₀ hs

#print axioms interval_propagate
#print axioms reset_next
#print axioms reset_previous
#print axioms row_reset
#print axioms row_reset_of_north438
#print axioms strip_reset_row
#print axioms strip_finish_and_reset_of_south438
#print axioms strip_finish_and_reset_of_finish
#print axioms marked_finish_trigger

end DiophantineConsistency.WangTiles942ResetRowsChecks

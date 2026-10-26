import DiophantineConsistency.WangTiles942SeamColumns

/-! Checks distinguish the necessary local/time premises from unneeded
horizontal or periodic premises, and cover negative integer times. -/

namespace DiophantineConsistency.WangTiles942SeamColumnsChecks

open WangTiles942 WangTiles942Language WangTiles942Periodic WangTiles942SeamColumns

set_option Elab.async false
set_option maxHeartbeats 1000000

-- This is an allowed time-matching column family, but it is not horizontally matched.
def constantSeam (_x _t : ℤ) : Tile := ⟨4,437,2,437⟩

private theorem constant_allowed (x t : ℤ) : Allowed (constantSeam x t) :=
  Allowed.seam (2 : Fin 3) (2 : Fin 3)

private theorem constant_time (x t : ℤ) :
    (constantSeam x (t+1)).north = (constantSeam x t).south := rfl

example : ¬ (∀ x t, (constantSeam (x+1) t).west = (constantSeam x t).east) := by
  intro h
  have hh := h 0 0
  norm_num [constantSeam] at hh

example (x : ℤ) : SeamAt constantSeam x (-31) ↔ SeamAt constantSeam x 17 :=
  seam_iff_time constant_allowed constant_time x (-31) 17

example (x t : ℤ) : ∃ u v : Fin 3, constantSeam x t = ⟨u.val^2,437,v.val,437⟩ :=
  column_seam_tuples constant_allowed constant_time x 0 rfl t

-- Allowedness without time matching does not make a seam invariant.
def jumpPlane (_x t : ℤ) : Tile := if t = 0 then ⟨4,437,2,437⟩ else ⟨0,0,0,0⟩

private theorem jump_allowed (x t : ℤ) : Allowed (jumpPlane x t) := by
  by_cases h : t = 0
  · rw [jumpPlane, if_pos h]
    exact Allowed.seam (2 : Fin 3) (2 : Fin 3)
  · rw [jumpPlane, if_neg h]
    exact Allowed.pass (0 : Fin 2) (0 : Fin 2)

example : SeamAt jumpPlane 0 0 ∧ ¬ SeamAt jumpPlane 0 1 := by
  norm_num [SeamAt, jumpPlane]

example : ¬ (∀ x t, (jumpPlane x (t+1)).north = (jumpPlane x t).south) := by
  intro h
  have hh := h 0 0
  norm_num [jumpPlane] at hh

-- Conversely, time matching alone does not supply the local seam equivalence.
def unallowedPlane (_x t : ℤ) : Tile :=
  ⟨0, if t = 0 then 437 else 0, 0, if t+1 = 0 then 437 else 0⟩

example (x t : ℤ) : (unallowedPlane x (t+1)).north = (unallowedPlane x t).south := rfl

example : SeamAt unallowedPlane 0 0 ∧ ¬ SeamAt unallowedPlane 0 1 := by
  norm_num [SeamAt, unallowedPlane]

example : ¬ Allowed (unallowedPlane 0 0) := by
  intro h
  have he := WangTiles942Boundary.north_437_iff_south_437 h
  norm_num [unallowedPlane] at he

example {T : ℤ → ℤ → Tile} (hA : ∀ x t, Allowed (T x t))
    (hT : ∀ x t, (T x (t+1)).north = (T x t).south)
    (h0 : T 7 (-5) = start) (t : ℤ) : (T 7 t).north ≠ 437 ∧ (T 7 t).south ≠ 437 :=
  start_column_vertical_ne hA hT 7 (-5) h0 t

example {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}
    (h : MarkedWord N s a) (t : ℤ) :
    (plane N s a 0 t).north ≠ 437 ∧ (plane N s a 0 t).south ≠ 437 :=
  marked_origin_never_seam h t

#print axioms seam_at_iff_south
#print axioms seam_successor_iff
#print axioms seam_iff_zero
#print axioms seam_iff_time
#print axioms column_seam_tuples
#print axioms column_seam_tuples_of_exists
#print axioms start_column_not_seam
#print axioms start_column_vertical_ne
#print axioms marked_seam_iff_zero
#print axioms marked_column_seam_tuples
#print axioms marked_origin_never_seam

end DiophantineConsistency.WangTiles942SeamColumnsChecks

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.SplitIfs

/-! A checked generic kernel for an alternative proof view of Wang step rows.
This record has the same four-field order as the repository Tile; it is
intentionally separate, so no full module-integration claim follows. -/
namespace NewWangSimplification

structure EdgeTile where
  west : ℕ
  north : ℕ
  east : ℕ
  south : ℕ
  deriving DecidableEq

def rowFromEdges (north south edge : ℤ → ℕ) (x : ℤ) : EdgeTile :=
  ⟨edge (x - 1), north x, edge x, south x⟩

theorem rowFromEdges_horizontal (north south edge : ℤ → ℕ) (x : ℤ) :
    (rowFromEdges north south edge (x + 1)).west =
      (rowFromEdges north south edge x).east := by
  exact congrArg edge (by omega)

theorem rowFromEdges_north (north south edge : ℤ → ℕ) (x : ℤ) :
    (rowFromEdges north south edge x).north = north x := rfl

theorem rowFromEdges_south (north south edge : ℤ → ℕ) (x : ℤ) :
    (rowFromEdges north south edge x).south = south x := rfl

/-- true means move right, matching the repository action direction. -/
def neighbor (p : ℤ) (d : Bool) : ℤ := if d then p + 1 else p - 1

def bridge (p : ℤ) (d : Bool) : ℤ := if d then p else p - 1

def impulse (cut : ℤ) (signal : ℕ) (x : ℤ) : ℕ :=
  if x = cut then signal else 0

theorem bridge_eq_min (p : ℤ) (d : Bool) :
    bridge p d = min p (neighbor p d) := by
  cases d <;> simp only [bridge, neighbor, Bool.false_eq_true, ↓reduceIte]
  · exact (min_eq_right (show p - 1 ≤ p by omega)).symm
  · exact (min_eq_left (show p ≤ p + 1 by omega)).symm

theorem old_head_edges (p : ℤ) (d : Bool) (signal : ℕ) :
    (impulse (bridge p d) signal (p-1), impulse (bridge p d) signal p) =
      if d then (0, signal) else (signal, 0) := by
  cases d <;> simp only [bridge, impulse, Bool.false_eq_true, ↓reduceIte]
  all_goals split_ifs <;> simp_all <;> omega

theorem new_head_edges (p : ℤ) (d : Bool) (signal : ℕ) :
    (impulse (bridge p d) signal (neighbor p d-1),
      impulse (bridge p d) signal (neighbor p d)) =
      if d then (signal, 0) else (0, signal) := by
  cases d <;> simp only [bridge, neighbor, impulse, Bool.false_eq_true, ↓reduceIte]
  all_goals split_ifs <;> simp_all <;> omega

theorem outside_edges_zero (p x : ℤ) (d : Bool) (signal : ℕ)
    (hold : x ≠ p) (hnew : x ≠ neighbor p d) :
    impulse (bridge p d) signal (x-1) = 0 ∧
      impulse (bridge p d) signal x = 0 := by
  cases d <;> simp only [bridge, neighbor, impulse, Bool.false_eq_true, ↓reduceIte] at *
  all_goals split_ifs <;> simp_all <;> omega

#print axioms rowFromEdges_horizontal
#print axioms bridge_eq_min
#print axioms old_head_edges
#print axioms new_head_edges
#print axioms outside_edges_zero
end NewWangSimplification

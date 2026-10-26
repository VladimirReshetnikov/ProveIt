import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
Portable validation of the periodic seam-gap argument at ProveIt commit
553a5f7a463cbaab8800ff8148fef0bc5a9e1b22, using its pinned Mathlib.
This is not a compilation of the full WangTiles dependency chain.

The fixture copies Tile, start, InitialStrip, wall_north, initial_tile,
and initial_vertical_nonseam exactly except for namespace relocation.
No imported project theorem is assumed as an axiom.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

#check Function.Periodic

namespace NewGeometry

/-- A positive period cannot fit strictly inside a seam-free gap. -/
theorem gap_le_period {α : Type*} {T : ℤ → α} {Seam : α → Prop}
    {p l r : ℤ} (hp : 0 < p) (hperiod : Function.Periodic T p)
    (hleft : Seam (T l))
    (hinside : ∀ x : ℤ, l < x → x < r → ¬ Seam (T x)) :
    r - l ≤ p := by
  by_contra hgap
  apply hinside (l + p) (by omega) (by omega)
  rwa [hperiod l]

#print axioms gap_le_period

namespace Fixture

structure Tile where
  west : ℕ
  north : ℕ
  east : ℕ
  south : ℕ
  deriving DecidableEq, Repr, Inhabited


def start : Tile := ⟨2, 435, 3, 1⟩

structure InitialStrip (T : ℤ → Tile) (N L R : ℕ) : Prop where
  left_pos : 0 < L
  left_le : L ≤ N
  right_min : 2 ≤ R
  right_le : R ≤ N+1
  start_at_zero : T 0 = start
  head_at_one : T 1 = ⟨3,436,4,4⟩
  left_wall : ∃ a : Fin 3, T (-(L : ℤ)) = ⟨a.val^2,437,2,437⟩
  right_wall : ∃ b : Fin 3, T (R : ℤ) = ⟨4,437,b.val,437⟩
  left_inside : ∀ j : ℕ, 1 ≤ j → j < L → T (-(j : ℤ)) = ⟨2,434,2,0⟩
  right_inside : ∀ j : ℕ, 2 ≤ j → j < R → T (j : ℤ) = ⟨4,436,4,0⟩

theorem InitialStrip.wall_north {T : ℤ → Tile} {N L R : ℕ} (h : InitialStrip T N L R) :
    (T (-(L : ℤ))).north = 437 ∧ (T (R : ℤ)).north = 437 := by
  obtain ⟨a,ha⟩ := h.left_wall
  obtain ⟨b,hb⟩ := h.right_wall
  rw [ha,hb]
  exact ⟨rfl,rfl⟩

theorem initial_tile {T : ℤ → Tile} {N L R : ℕ} (h : InitialStrip T N L R)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    T x = if x < 0 then ⟨2,434,2,0⟩ else
      if x = 0 then start else if x = 1 then ⟨3,436,4,4⟩ else ⟨4,436,4,0⟩ := by
  by_cases hx : x < 0
  · rw [if_pos hx]
    have hc : ((-x).toNat : ℤ) = -x := Int.toNat_of_nonneg (by omega)
    have hi := h.left_inside (-x).toNat (by omega) (by omega)
    simpa only [hc, neg_neg] using hi
  · rw [if_neg hx]
    by_cases hz : x = 0
    · rw [if_pos hz, hz]
      exact h.start_at_zero
    · rw [if_neg hz]
      by_cases ho : x = 1
      · rw [if_pos ho, ho]
        exact h.head_at_one
      · rw [if_neg ho]
        have hc : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (by omega)
        have hi := h.right_inside x.toNat (by omega) (by omega)
        simpa only [hc] using hi

theorem initial_vertical_nonseam {T : ℤ → Tile} {N L R : ℕ}
    (h : InitialStrip T N L R) (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    (T x).north ≠ 437 ∧ (T x).south ≠ 437 := by
  rw [initial_tile h x hl hr]
  split_ifs <;> decide

/-- Production-candidate proof against an exact local fixture.
The fixture run timed out; only StripWidthCore.lean has a successful check. -/
theorem initial_width_le_period {T : ℤ → Tile} {N L R : ℕ}
    (h : InitialStrip T N L R) (hperiod : Function.Periodic T (N : ℤ)) :
    L + R ≤ N := by
  have hN : 0 < N := lt_of_lt_of_le h.left_pos h.left_le
  by_contra hwidth
  apply (initial_vertical_nonseam h (-(L : ℤ) + (N : ℤ)) (by omega) (by omega)).1
  exact (congrArg Tile.north (hperiod (-(L : ℤ)))).trans h.wall_north.1

/-- Same estimate factored through the general gap theorem. -/
theorem initial_width_le_period_via_gap {T : ℤ → Tile} {N L R : ℕ}
    (h : InitialStrip T N L R) (hperiod : Function.Periodic T (N : ℤ)) :
    L + R ≤ N := by
  have hN : 0 < N := lt_of_lt_of_le h.left_pos h.left_le
  have hw := gap_le_period (Seam := fun t : Tile => t.north = 437)
    (p := (N : ℤ)) (l := -(L : ℤ)) (r := (R : ℤ))
    (by omega) hperiod h.wall_north.1
    (fun x hl hr => (initial_vertical_nonseam h x hl hr).1)
  omega

/-- Geometry-only period obstruction, with no allowedness or machine-run premise. -/
theorem initial_period_gt_two {T : ℤ → Tile} {N L R : ℕ}
    (h : InitialStrip T N L R) (hperiod : Function.Periodic T (N : ℤ)) :
    2 < N := by
  have hw := initial_width_le_period h hperiod
  have hl := h.left_pos
  have hr := h.right_min
  omega

/-- Equality at the right endpoint is possible in the precise initial-strip interface. -/
def widthThreeRow (x : ℤ) : Tile :=
  if x % 3 = 0 then start else
    if x % 3 = 1 then ⟨3,436,4,4⟩ else ⟨4,437,2,437⟩

theorem widthThreeRow_periodic : Function.Periodic widthThreeRow 3 := by
  intro x
  have hx : (x + 3) % 3 = x % 3 := by omega
  simp only [widthThreeRow, hx]

theorem widthThreeRow_initial : InitialStrip widthThreeRow 3 1 2 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨⟨2, by decide⟩, by decide⟩
  · exact ⟨⟨2, by decide⟩, by decide⟩
  · intro j hj hjl
    omega
  · intro j hj hjr
    omega

#print axioms widthThreeRow_periodic
#print axioms widthThreeRow_initial

#print axioms initial_width_le_period
#print axioms initial_width_le_period_via_gap
#print axioms initial_period_gt_two

end Fixture

#print axioms gap_le_period

end NewGeometry

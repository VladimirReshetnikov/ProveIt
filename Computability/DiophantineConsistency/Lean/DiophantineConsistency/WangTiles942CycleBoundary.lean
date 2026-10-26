import DiophantineConsistency.WangTiles942TraceCycle

/-!
# Exact outer edges of the actual variable-height trace cycle

A supplied actual halt time bounds the old and next heads at every time. With
independent margins T+2≤L,R, the cells −L+1 and R−1 are therefore blank pass
cells in every run row. The cycle has edge codes 2/4 at initialization, 1/1 at
reset, and 0/0 elsewhere. No boundary-cleanliness premise is assumed.
-/

namespace DiophantineConsistency.WangTiles942CycleBoundary

open SetTheory.BusyBeaver WangTiles942 WangMachineEncoding WangMachineTraceBounds
open WangTiles942StepConstruction WangTiles942FinishConstruction WangTiles942TraceCycle

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- At and beyond ±(T+1), an actual run row is the literal all-zero pass tile.
Both its old head and moved head are excluded using actual run bounds. -/
theorem runTile_outer_blank (T : ℕ) (hh : (DecimalMachine215.machine.run T).state = none)
    (t : ℕ) (x : ℤ) (hx : x ≤ -((T : ℤ)+1) ∨ (T : ℤ)+1 ≤ x) :
    runTile t x = ⟨0,0,0,0⟩ := by
  obtain ⟨hl,hr,hblank⟩ := halted_trace_box DecimalMachine215.machine T (T+1) (T+1)
    hh (by omega) (by omega) t
  obtain ⟨hnl,hnr,_⟩ := halted_trace_box DecimalMachine215.machine T (T+1) (T+1)
    hh (by omega) (by omega) (t+1)
  have ho : x ≠ (DecimalMachine215.machine.run t).head := by omega
  have hz : Tape.read (DecimalMachine215.machine.run t).tape x = false :=
    hblank x (by omega)
  cases hs : (DecimalMachine215.machine.run t).state with
  | none =>
      simp only [runTile,hs,passTile,color_of_ne_head _ x ho,hz,Bool.toNat_false]
  | some q =>
      have he : nextHead (DecimalMachine215.machine.run t) q =
          (DecimalMachine215.machine.run (t+1)).head := by
        change _ = (DecimalMachine215.machine.step (DecimalMachine215.machine.run t)).head
        rw [WangMachineStep.step_eq _ _ q hs]
        rfl
      have hn : x ≠ nextHead (DecimalMachine215.machine.run t) q := by rw [he]; omega
      simp only [runTile,hs]
      rw [stepTile_elsewhere _ q x ho hn,hz]
      rfl

/-- Each side's width may be chosen independently, with no height relation. -/
theorem runTile_left_blank (T L : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) (hL : T+2 ≤ L) (t : ℕ) :
    runTile t (-(L : ℤ)+1) = ⟨0,0,0,0⟩ :=
  runTile_outer_blank T hh t _ (Or.inl (by omega))

theorem runTile_right_blank (T R : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) (hR : T+2 ≤ R) (t : ℕ) :
    runTile t ((R : ℤ)-1) = ⟨0,0,0,0⟩ :=
  runTile_outer_blank T hh t _ (Or.inr (by omega))

/-- The seam's right edge is this code; its left edge uses a code squared. -/
def edgeCode {H : ℕ} (k : Fin H) : ℕ :=
  if k.val = 0 then 2 else if k.val+1 = H then 1 else 0

theorem edgeCode_le_two {H : ℕ} (k : Fin H) : edgeCode k ≤ 2 := by
  unfold edgeCode
  split_ifs <;> decide

/-- Exact left-facing color of the first interior cell. -/
theorem cycleTile_left_west (T L : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) (hL : T+2 ≤ L)
    {H : ℕ} (k : Fin H) :
    (cycleTile k (-(L : ℤ)+1)).west = edgeCode k := by
  unfold cycleTile edgeCode
  split_ifs
  · rw [initialTile_negative (-(L : ℤ)+1) (by omega)]
  · rfl
  · rfl
  · rw [runTile_left_blank T L hh hL k.val]

/-- Exact right-facing color of the last interior cell: 4, 1, or 0. -/
theorem cycleTile_right_east (T R : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) (hR : T+2 ≤ R)
    {H : ℕ} (k : Fin H) :
    (cycleTile k ((R : ℤ)-1)).east = (edgeCode k)^2 := by
  unfold cycleTile edgeCode
  split_ifs
  · have hr : 1 < (R : ℤ)-1 ∨ (R : ℤ)-1 = 1 := by omega
    rcases hr with hr | hr
    · rw [initialTile_right _ hr]
      rfl
    · rw [hr,initialTile_one]
      rfl
  · rfl
  · rfl
  · rw [runTile_right_blank T R hh hR k.val]
    rfl

/-- Joint boundary formula with separate independent left and right margin bounds. -/
theorem cycleTile_outer_edges (T L R : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hL : T+2 ≤ L) (hR : T+2 ≤ R) {H : ℕ} (k : Fin H) :
    (cycleTile k (-(L : ℤ)+1)).west = edgeCode k ∧
      (cycleTile k ((R : ℤ)-1)).east = (edgeCode k)^2 :=
  ⟨cycleTile_left_west T L hh hL k,cycleTile_right_east T R hh hR k⟩

end DiophantineConsistency.WangTiles942CycleBoundary

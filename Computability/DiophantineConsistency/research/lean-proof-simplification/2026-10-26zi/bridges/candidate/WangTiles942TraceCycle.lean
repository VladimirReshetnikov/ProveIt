import DiophantineConsistency.WangTiles942StepConstruction
import DiophantineConsistency.WangTiles942FinishConstruction
import DiophantineConsistency.WangMachineTraceBounds

/-!
# A variable-height cycle of actual run rows

An actual run row uses the transition construction while live and a pass row
while halted. A finite cycle replaces row 0 by the actual initializer and its
last two rows by finish and reset. Height is arbitrary above the explicit halt
bound; this module chooses no spatial walls or helical quotient.
-/

namespace DiophantineConsistency.WangTiles942TraceCycle

open SetTheory.BusyBeaver WangTiles942 WangTiles942Language WangMachineEncoding
open WangTiles942StepConstruction WangTiles942FinishConstruction WangMachineTraceBounds

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- A row for the actual t-th blank-run configuration, including stationary halt. -/
def runTile (t : ℕ) (x : ℤ) : Tile :=
  match (DecimalMachine215.machine.run t).state with
  | some q => stepTile (DecimalMachine215.machine.run t) q x
  | none => passTile (DecimalMachine215.machine.run t) x

theorem runTile_allowed (t : ℕ) (x : ℤ) : Allowed (runTile t x) := by
  cases hs : (DecimalMachine215.machine.run t).state with
  | none =>
      simp only [runTile,hs]
      exact passTile_allowed _ hs x
  | some q =>
      simp only [runTile,hs]
      exact stepTile_allowed _ q x

theorem runTile_north (t : ℕ) (x : ℤ) :
    (runTile t x).north = color (DecimalMachine215.machine.run t) x := by
  cases hs : (DecimalMachine215.machine.run t).state with
  | none => simp only [runTile,hs,passTile]
  | some q =>
      simp only [runTile,hs]
      exact stepTile_north _ q hs x

theorem runTile_south (t : ℕ) (x : ℤ) :
    (runTile t x).south = color (DecimalMachine215.machine.run (t+1)) x := by
  cases hs : (DecimalMachine215.machine.run t).state with
  | none =>
      have he : DecimalMachine215.machine.run (t+1) = DecimalMachine215.machine.run t := by
        change DecimalMachine215.machine.step (DecimalMachine215.machine.run t) = _
        simp only [Machine.step,hs]
      simp only [runTile,hs,passTile,he]
  | some q =>
      simp only [runTile,hs]
      exact stepTile_south _ q hs x

theorem runTile_horizontal (t : ℕ) (x : ℤ) :
    (runTile t (x+1)).west = (runTile t x).east := by
  cases hs : (DecimalMachine215.machine.run t).state with
  | none => simp only [runTile,hs]; exact passTile_horizontal _ x
  | some q => simp only [runTile,hs]; exact stepTile_horizontal _ q x

/-- Extra time after a halt is filled by the same literal pass row. -/
theorem runTile_after_halt (T : ℕ) (hh : (DecimalMachine215.machine.run T).state = none)
    (t : ℕ) (ht : T ≤ t) (x : ℤ) :
    runTile t x = passTile (DecimalMachine215.machine.run T) x := by
  simp only [runTile,run_eq_of_halted _ T hh t ht,hh]

/-- The successor of a finite row index, with explicit wrap to zero. -/
def nextIndex {H : ℕ} (hH : 0 < H) (k : Fin H) : Fin H :=
  ⟨(k.val+1)%H, Nat.mod_lt _ hH⟩

theorem nextIndex_val_of_lt {H : ℕ} (hH : 0 < H) (k : Fin H) (hk : k.val+1 < H) :
    (nextIndex hH k).val = k.val+1 := Nat.mod_eq_of_lt hk

theorem nextIndex_val_of_last {H : ℕ} (hH : 0 < H) (k : Fin H) (hk : k.val+1 = H) :
    (nextIndex hH k).val = 0 := by
  simp only [nextIndex,hk,Nat.mod_self]

/-- Initializer, actual run/wait rows, finish, reset, in that exact order. -/
def cycleTile {H : ℕ} (k : Fin H) (x : ℤ) : Tile :=
  if k.val = 0 then initialTile x
  else if k.val+1 = H then resetTile x
  else if k.val+2 = H then finishTile (DecimalMachine215.machine.run k.val) x
  else runTile k.val x

theorem cycleTile_zero {H : ℕ} (hH : 0 < H) (x : ℤ) :
    cycleTile (⟨0,hH⟩ : Fin H) x = initialTile x := by simp [cycleTile]

theorem cycleTile_last {H : ℕ} (hH : 3 ≤ H) (k : Fin H)
    (hk : k.val+1 = H) (x : ℤ) : cycleTile k x = resetTile x := by
  simp only [cycleTile,if_neg (show k.val ≠ 0 by omega),if_pos hk]

theorem cycleTile_finish {H : ℕ} (hH : 3 ≤ H) (k : Fin H)
    (hk : k.val+2 = H) (x : ℤ) :
    cycleTile k x = finishTile (DecimalMachine215.machine.run k.val) x := by
  simp only [cycleTile,if_neg (show k.val ≠ 0 by omega),
    if_neg (show k.val+1 ≠ H by omega),if_pos hk]

theorem cycleTile_run {H : ℕ} (k : Fin H) (h0 : k.val ≠ 0)
    (hlast : k.val+1 ≠ H) (hfinish : k.val+2 ≠ H) (x : ℤ) :
    cycleTile k x = runTile k.val x := by
  simp only [cycleTile,if_neg h0,if_neg hlast,if_neg hfinish]

/-- Membership at the finish row uses actual halt persistence at time H−2. -/
theorem cycleTile_allowed (T H : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) (hTH : T+2 ≤ H)
    (k : Fin H) (x : ℤ) : Allowed (cycleTile k x) := by
  unfold cycleTile
  split_ifs with h0 hlast hfinish
  · exact initialTile_allowed x
  · exact resetTile_allowed x
  · apply finishTile_allowed
    rw [run_eq_of_halted _ T hh k.val (by omega)]
    exact hh
  · exact runTile_allowed k.val x

theorem cycleTile_horizontal {H : ℕ} (k : Fin H) (x : ℤ) :
    (cycleTile k (x+1)).west = (cycleTile k x).east := by
  unfold cycleTile
  split_ifs
  · exact initialTile_horizontal x
  · exact resetTile_horizontal x
  · exact finishTile_horizontal _ x
  · exact runTile_horizontal k.val x

/-- The finish row has the same input color as the run row it replaces. -/
theorem cycleTile_north {H : ℕ} (k : Fin H) (x : ℤ) :
    (cycleTile k x).north =
      if k.val = 0 then (initialTile x).north
      else if k.val+1 = H then 438
      else color (DecimalMachine215.machine.run k.val) x := by
  unfold cycleTile
  split_ifs <;> first | rfl | exact runTile_north k.val x

/-- Initializer output is actual run time 1; final reset returns to its input. -/
theorem cycleTile_south {H : ℕ} (k : Fin H) (x : ℤ) :
    (cycleTile k x).south =
      if k.val = 0 then color (DecimalMachine215.machine.run 1) x
      else if k.val+1 = H then (initialTile x).north
      else if k.val+2 = H then 438
      else color (DecimalMachine215.machine.run (k.val+1)) x := by
  unfold cycleTile
  split_ifs
  · rw [DecimalMachineInitialization.run_one]
    exact initialTile_south x
  · rfl
  · rfl
  · exact runTile_south k.val x

/-- Every vertical edge matches around the finite cycle, including reset→initializer.
The height lower bound keeps the initializer distinct from finish and reset. -/
theorem cycleTile_temporal {H : ℕ} (hH : 3 ≤ H) (k : Fin H) (x : ℤ) :
    (cycleTile (nextIndex (by omega) k) x).north = (cycleTile k x).south := by
  rw [cycleTile_north,cycleTile_south]
  by_cases hlast : k.val+1 = H
  · rw [nextIndex_val_of_last (by omega) k hlast]
    simp only [if_pos rfl,if_neg (show k.val ≠ 0 by omega),if_pos hlast]
  · rw [nextIndex_val_of_lt (by omega) k (by have hk := k.isLt; omega)]
    have hsucc : k.val+1 ≠ 0 := by omega
    by_cases h0 : k.val = 0
    · simp only [h0,hsucc,hlast,Nat.zero_add,↓reduceIte,show 2 ≠ H by omega]
    · simp only [h0,hsucc,hlast,↓reduceIte,Nat.add_assoc]

/-- A marked, horizontally matching, cyclic sequence of whole-integer rows
exists at every sufficiently large height, independently of spatial choices. -/
theorem trace_cycle (T H : ℕ) (hh : (DecimalMachine215.machine.run T).state = none)
    (hTH : T+2 ≤ H) (hH : 3 ≤ H) :
    (∀ k : Fin H, ∀ x : ℤ, Allowed (cycleTile k x)) ∧
    (∀ k : Fin H, ∀ x : ℤ, (cycleTile k (x+1)).west = (cycleTile k x).east) ∧
    (∀ k : Fin H, ∀ x : ℤ,
      (cycleTile (nextIndex (by omega) k) x).north = (cycleTile k x).south) ∧
    cycleTile (⟨0,by omega⟩ : Fin H) 0 = start := by
  refine ⟨cycleTile_allowed T H hh hTH,cycleTile_horizontal,cycleTile_temporal hH,?_⟩
  rw [cycleTile_zero,initialTile_zero]

end DiophantineConsistency.WangTiles942TraceCycle

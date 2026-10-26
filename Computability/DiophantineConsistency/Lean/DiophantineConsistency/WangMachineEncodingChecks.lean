import DiophantineConsistency.WangMachineEncoding

/-! Checks for literal head-state colors, entering-halt write/move semantics,
and the exact actual initialization boundary. No tiling hypotheses occur. -/

namespace DiophantineConsistency.WangMachineEncodingChecks

open SetTheory.BusyBeaver
open WangMachineEncoding

set_option Elab.async false
set_option maxRecDepth 10000

example (s t : Option (Fin 215)) (h : stateNumber s = stateNumber t) : s = t :=
  stateNumber_injective h

example (s t : Option (Fin 215)) (b c : Bool) :
    headColor s b = headColor t c ↔ s = t ∧ b = c := headColor_injective

example : headColor (some (214 : Fin 215)) false = 430 := rfl
example : headColor (some (214 : Fin 215)) true = 431 := rfl
example : headColor none false = 432 := rfl
example : headColor none true = 433 := rfl

example (q : Fin 215) (b c : Bool) : headColor (some q) b ≠ headColor none c := by
  intro h
  have hs := (headColor_injective.mp h).1
  exact Option.some_ne_none _ hs

example (cfg : Config 215) (x : ℤ) (h : x ≠ cfg.head) : color cfg x ≤ 1 :=
  plain_color_le_one cfg x h

example (cfg : Config 215) (x : ℤ) : color cfg x ≤ 433 := color_le_433 cfg x

example (cfg : Config 215) (x : ℤ) : 2 ≤ color cfg x ↔ x = cfg.head := head_iff cfg x

/-- Synthetic transition checks distinguish write/move-before-halt from
incorrectly replacing the configuration by its old head and tape. -/
private def haltLeftWrite : Machine 215 where
  transition _ _ := { write := true, move := Move.left, next := none }

example : (haltLeftWrite.step (initial 215)).head = (-1 : ℤ) := rfl
example : (haltLeftWrite.step (initial 215)).tape = [0] := rfl
example : color (haltLeftWrite.step (initial 215)) 0 = 1 := rfl
example : color (haltLeftWrite.step (initial 215)) (-1) = 432 := rfl

private def haltLeftErase : Machine 215 where
  transition _ _ := { write := false, move := Move.left, next := none }

private def readOneAtDestination : Config 215 where
  state := some 0
  head := 0
  tape := [-1]

example : color (haltLeftErase.step readOneAtDestination) (-1) = 433 := rfl
example : color (haltLeftErase.step readOneAtDestination) 0 = 0 := rfl

example (x : ℤ) : color DecimalMachineInitialization.initialized x =
    if x = 0 then 1 else if x = 1 then 4 else 0 := initialized_color x

example : color DecimalMachineInitialization.initialized (-1) = 0 :=
  initialized_color_other (-1) (by decide) (by decide)

example : color DecimalMachineInitialization.initialized 1 =
    WangTiles942.headColor 1 0 := initialized_color_one

example (x : ℤ) : color (DecimalMachine215.machine.run 1) x =
    if x = 0 then 1 else if x = 1 then 4 else 0 := by
  rw [DecimalMachineInitialization.run_one]
  exact initialized_color x

#print axioms stateNumber_le
#print axioms stateNumber_injective
#print axioms bit_le_one
#print axioms operating_head_color
#print axioms halted_head_color
#print axioms headColor_bounds
#print axioms headColor_injective
#print axioms color_at_head
#print axioms color_of_ne_head
#print axioms plain_color_le_one
#print axioms color_le_433
#print axioms head_iff
#print axioms step_enter_halt
#print axioms step_enter_halt_color
#print axioms initialized_color_zero
#print axioms initialized_color_one
#print axioms initialized_color_other
#print axioms initialized_color

end DiophantineConsistency.WangMachineEncodingChecks

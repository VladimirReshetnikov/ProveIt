import DiophantineConsistency.WangTiles942StepConstruction

/-!
Source-only regression statements. No Lean run was performed in this review.
These counterexamples forbid strengthening interior tile equality to Config
identity, or replacing the actual initializer by a blank-tape convention.
-/
namespace DiophantineConsistency.Round3MachineScopeChecks

open SetTheory.BusyBeaver WangMachineEncoding

private def original : Config 215 := ⟨some 1, 1, [0]⟩
private def outside : Config 215 := ⟨some 1, 1, [0, 100]⟩
private def duplicate : Config 215 := ⟨some 1, 1, [0, 0]⟩

-- A finite open strip cannot observe a distant tape cell.
example (x : ℤ) (hx : x < 3) : color original x = color outside x := by
  have h100 : x ≠ 100 := by omega
  simp [color, original, outside, Tape.read, h100]

example : original ≠ outside := by
  intro h
  have hl := congrArg (fun cfg : Config 215 => cfg.tape.length) h
  change (1 : ℕ) = 2 at hl
  omega

-- Even equality of every color does not recover the concrete list tape.
example (x : ℤ) : color original x = color duplicate x := by
  simp [color, original, duplicate, Tape.read]

example : original ≠ duplicate := by
  intro h
  have hl := congrArg (fun cfg : Config 215 => cfg.tape.length) h
  change (1 : ℕ) = 2 at hl
  omega

-- The initial row's exact profile remains one at zero, four at one.
example : color DecimalMachineInitialization.initialized 0 = 1 := rfl
example : color DecimalMachineInitialization.initialized 1 = 4 := rfl
example (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    color DecimalMachineInitialization.initialized x = 0 :=
  initialized_color_other x h0 h1

-- Live source state and optional halting destination are different notions.
example (cfg : Config 215) (q : Fin 215) (hq : cfg.state = some q)
    (hh : (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).next = none) :
    (WangTiles942StepConstruction.stepTile cfg q
      (WangTiles942StepConstruction.nextHead cfg q)).south =
      432 + (Tape.read cfg.tape
        (WangTiles942StepConstruction.nextHead cfg q)).toNat := by
  rw [WangTiles942StepConstruction.stepTile_south cfg q hq]
  exact WangMachineStep.color_step_enter_halt DecimalMachine215.machine cfg q hq hh

end DiophantineConsistency.Round3MachineScopeChecks

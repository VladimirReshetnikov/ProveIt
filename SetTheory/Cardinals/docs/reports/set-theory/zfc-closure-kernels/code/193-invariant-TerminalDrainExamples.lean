import BusyBeaver.ZFC.TerminalDrain
import BusyBeaver.ZFC.RegisterPartial

/-! Checked boundary cases for the simulation contract. -/

namespace SetTheory.BusyBeaver.ZFC.TerminalDrainExamples

open TerminalDrain

def sourceStop (_ : Unit) : Option Unit := none

def countdown : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

/-- Source stopping may correspond to two target transitions before stopping. -/
theorem delayed_finish : Simulation sourceStop countdown (fun _ n => n = 2) := by
  constructor
  · intro _ n hn _
    subst n
    exact ⟨2, 0, rfl, rfl⟩
  · intro a b a' _ h
    cases h

theorem delayed_halting_equivalence : Halts sourceStop () ↔ Halts countdown 2 :=
  delayed_finish.halts_iff rfl

/-- The old immediate-terminal contract cannot cover this related pair. -/
theorem immediate_terminal_agreement_fails :
    ¬ (sourceStop () = none ↔ countdown 2 = none) := by
  simp [sourceStop, countdown]

def sourceLoop (_ : Unit) : Option Unit := some ()

theorem source_loop_never_halts : ¬ Halts sourceLoop () := by
  rintro ⟨_, _, _, h⟩
  cases h

/-- Zero-length blocks can falsely match a looping source with a stopped target. -/
theorem zero_steps_are_insufficient :
    (∀ {a a' b : Unit}, sourceLoop a = some a' →
      ∃ k b', run sourceStop k b = some b' ∧ True) ∧
    Halts sourceStop () ∧ ¬ Halts sourceLoop () := by
  refine ⟨?_, halt_now rfl, source_loop_never_halts⟩
  intro a a' b _
  exact ⟨0, b, rfl, trivial⟩

/-- A malformed source decoder is stuck but has no literal halt leaf. -/
def badProgram : RegisterPath.Program :=
  ⟨fun _ => (.node 0, .node 0), 0, 0⟩

def badStart : RegisterPath.Configuration := ⟨[], fun _ => 0⟩

theorem stuck_is_not_source_halting :
    Halts (RegisterPath.step badProgram) badStart ∧
    ¬ RegisterPath.Halts badProgram badStart := by
  constructor
  · exact halt_now rfl
  · rintro ⟨_, c, _, d, hd⟩
    simp [badProgram, RegisterPath.walk] at hd

#print axioms delayed_halting_equivalence
#print axioms zero_steps_are_insufficient
#print axioms stuck_is_not_source_halting

end SetTheory.BusyBeaver.ZFC.TerminalDrainExamples

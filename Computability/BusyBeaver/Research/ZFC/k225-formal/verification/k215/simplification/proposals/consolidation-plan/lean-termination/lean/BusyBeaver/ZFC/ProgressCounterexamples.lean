import BusyBeaver.ZFC.TerminationTransport

/-! Concrete checks that the two simulation premises cannot be discarded. -/
namespace ProgressCounterexamples
open TerminationTransport

def spin (_ : Unit) : Option Unit := some ()
def stop (_ : Unit) : Option Unit := none

theorem spin_does_not_halt : ¬ Halts spin () := by
  rintro ⟨_, _, _, h⟩
  cases h

theorem stop_halts : Halts stop () := .stop rfl

/-- Zero-step simulation can relate an infinite source run to an already
halted target.  The terminal-drain premise is vacuous in this example. -/
theorem zero_step_simulation :
    (∀ a a' b : Unit, spin a = some a' → ∃ b', Reach stop b b') ∧
    ¬ (Halts spin () ↔ Halts stop ()) := by
  constructor
  · intro _ _ b _; exact ⟨b, .refl stop b⟩
  · intro h; exact spin_does_not_halt (h.mpr stop_halts)

/-- Positive step simulation alone reflects termination, but does not preserve
it: a stopped source has no transition obligations and can be related to a
target that loops forever.  The terminal-drain premise supplies this direction. -/
theorem missing_terminal_drain :
    (∀ a a' b : Unit, stop a = some a' → ∃ b', Reach1 spin b b') ∧
    ¬ (Halts stop () ↔ Halts spin ()) := by
  constructor
  · intro _ _ _ h; cases h
  · intro h; exact spin_does_not_halt (h.mp stop_halts)

#print axioms zero_step_simulation
#print axioms missing_terminal_drain
end ProgressCounterexamples

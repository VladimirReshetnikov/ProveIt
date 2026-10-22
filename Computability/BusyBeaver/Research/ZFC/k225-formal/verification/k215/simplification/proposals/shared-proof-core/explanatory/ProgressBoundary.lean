import Init

/-!
A minimal counterexample to replacing positive simulation by zero-or-more
steps in a reverse halting theorem.  The source loops; the target is already
terminal.  Every source transition can be matched by zero target transitions.
This file illustrates a contract requirement; it does not alter K215.
-/
namespace K215ProofSharing.ProgressBoundary

def sourceStep (_ : Unit) : Option Unit := some ()
def targetStep (_ : Unit) : Option Unit := none

def run (step : Unit → Option Unit) : Nat → Unit → Option Unit
  | 0, c => some c
  | n + 1, c => (step c).bind (run step n)

def Halts (step : Unit → Option Unit) (c : Unit) : Prop :=
  ∃ n d, run step n c = some d ∧ step d = none

def Reach (step : Unit → Option Unit) (c d : Unit) : Prop :=
  ∃ n, run step n c = some d

def ReachPositive (step : Unit → Option Unit) (c d : Unit) : Prop :=
  ∃ n, run step (n + 1) c = some d

theorem source_never_halts : ¬ Halts sourceStep () := by
  rintro ⟨_, _, _, h⟩
  cases h

theorem target_halts : Halts targetStep () :=
  ⟨0, (), rfl, rfl⟩

theorem zero_step_simulation :
    ∀ c d, sourceStep c = some d → Reach targetStep c d := by
  intro c d _
  cases c
  cases d
  exact ⟨0, rfl⟩

theorem no_positive_target_step : ¬ ReachPositive targetStep () () := by
  rintro ⟨n, h⟩
  simp [run, targetStep] at h

theorem zero_step_simulation_does_not_reflect_halting :
    (∀ c d, sourceStep c = some d → Reach targetStep c d) ∧
    Halts targetStep () ∧ ¬ Halts sourceStep () :=
  ⟨zero_step_simulation, target_halts, source_never_halts⟩

#print axioms zero_step_simulation_does_not_reflect_halting
#print axioms no_positive_target_step
end K215ProofSharing.ProgressBoundary

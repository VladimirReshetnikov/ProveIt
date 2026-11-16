module
public import M6.Source.Scheduler
public import M6.Source.CommandStore
@[expose] public section
namespace M6.Source.Scheduler
open Enumeration

/-- Arithmetic safety is about every actual schedule prefix. The PA project
proves this predicate for commandInitial using its explicit interpreter bridge. -/
def ArithmeticSafe : Prop :=
  ∀ n p rest, word n = p++rest → commandsEval (schedule n++p) commandInitial ≠ none

theorem frontier_safe (h : ArithmeticSafe) (hf : Frontier n l history) :
    commandsEval history commandInitial ≠ none := by
  obtain ⟨k,p,rest,rfl,hp⟩ := history_prefix hf
  exact h k p rest hp

/-- A safe schedule history has an actual next arithmetic result. The result
history is the same deterministic N/L frontier, not an existentially chosen word. -/
theorem next_result (h : ArithmeticSafe) (hf : Frontier n l history)
    (he : commandsEval history commandInitial = some s) :
    ∃ out, commandEval (parse (FetchDispatch.seed n l)).command s = some out ∧
      commandsEval (history++[(parse (FetchDispatch.seed n l)).command]) commandInitial = some out := by
  have hn := frontier_safe h (advance hf)
  rw [commandsEval_append,he] at hn
  simp only [Option.bind_some,commandsEval] at hn
  cases hx : commandEval (parse (FetchDispatch.seed n l)).command s with
  | none => simp [hx] at hn
  | some out =>
    refine ⟨out,rfl,?_⟩
    rw [commandsEval_append,he]
    simp [commandsEval,hx]
#print axioms next_result
end M6.Source.Scheduler


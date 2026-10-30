import DiophantineConsistency.ArithmeticCommandRunPerm222

/-! Exact head/tail evaluation for actual permuted C222 command words.
Stopped times are compared only in the absorbing word evaluator, where
successful completion stays positive. These laws supply the local execution
interface for later scheduler fairness; no append/compiler or scheduler
equivalence is asserted. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandEvaluationPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCommandWordPerm222 ArithmeticCommandStepPerm222
open ArithmeticCommandTickPerm222 ArithmeticCommandRunPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem run_eq_of_stopped_le (first second initial : V) (hle : first ≤ second)
    (hs : Stopped (run first initial)) : run second initial = run first initial := by
  have hdecomp : second = first+(second-first) := Arithmetic.sub_spec_of_ge hle
  rw [hdecomp, run_add, run_stopped _ _ hs]

theorem stopped_runs_eq (first second initial : V)
    (hf : Stopped (run first initial)) (hs : Stopped (run second initial)) :
    run first initial = run second initial := by
  by_cases hle : first ≤ second
  · exact (run_eq_of_stopped_le first second initial hle hf).symm
  · exact run_eq_of_stopped_le second first initial (le_of_not_ge hle) hs

theorem terminal_eq_run (word w time : V)
    (hs : Stopped (run time (liveValue word w))) :
    terminal word w = run time (liveValue word w) :=
  stopped_runs_eq word time _ (terminal_stopped word w) hs

/-- Shifted word1 executes the actual raw command0, which is NIP. -/
theorem run_one_succ (raw w : V) :
    run 1 (liveValue (raw+1) w) = nextValue raw w := by
  simpa only [zero_add,run_zero,tick_live_succ] using
    run_succ (0 : V) (liveValue (raw+1) w)

theorem terminal_succ (raw w : V) :
    terminal (raw+1) w =
      if stepValue raw w=0 then 0 else terminal (tailValue raw) (stepValue raw w-1) := by
  by_cases hs : stepValue raw w=0
  · have hfirst : run 1 (liveValue (raw+1) w)=0 := by
      simp only [run_one_succ,nextValue,hs,if_pos]
    have hstop : Stopped (run 1 (liveValue (raw+1) w)) := Or.inl hfirst
    rw [if_pos hs,terminal_eq_run _ _ 1 hstop,hfirst]
  · have hfirst : run 1 (liveValue (raw+1) w)=
        liveValue (tailValue raw) (stepValue raw w-1) := by
      simp only [run_one_succ,nextValue,hs,if_false]
    have hfinal : run (1+tailValue raw) (liveValue (raw+1) w)=
        terminal (tailValue raw) (stepValue raw w-1) := by
      rw [run_add,hfirst]
      rfl
    have hstop : Stopped (run (1+tailValue raw) (liveValue (raw+1) w)) := by
      rw [hfinal]
      exact terminal_stopped _ _
    rw [if_neg hs,terminal_eq_run _ _ (1+tailValue raw) hstop,hfinal]

/-- The predecessor is used only after a nonzero successful command result. -/
theorem eval_succ (raw w : V) :
    evalValue (raw+1) w =
      if stepValue raw w=0 then 0 else evalValue (tailValue raw) (stepValue raw w-1) := by
  by_cases hs : stepValue raw w=0 <;> simp [evalValue,terminal_succ,hs]

end DiophantineConsistency.ArithmeticCommandEvaluationPerm222

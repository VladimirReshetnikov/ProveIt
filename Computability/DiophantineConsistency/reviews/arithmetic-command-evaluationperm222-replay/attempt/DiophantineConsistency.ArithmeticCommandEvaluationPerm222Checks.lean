import DiophantineConsistency.ArithmeticCommandEvaluationPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandEvaluationPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCommandWordPerm222 ArithmeticCommandStepPerm222
open ArithmeticCommandTickPerm222 ArithmeticCommandRunPerm222
open ArithmeticCommandEvaluationPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (w : V) : run 1 (liveValue 1 w)=nextValue 0 w := by
  simpa only [zero_add] using run_one_succ (0 : V) w
example (raw w : V) (hh : stepValue raw w=0) : evalValue (raw+1) w=0 := by
  rw [eval_succ,if_pos hh]
example (raw w : V) (hh : stepValue raw w≠0) : evalValue (raw+1) w=
    evalValue (tailValue raw) (stepValue raw w-1) := by rw [eval_succ,if_neg hh]
example (word w time : V) (h : Stopped (run time (liveValue word w))) :
    terminal word w=run time (liveValue word w) := terminal_eq_run word w time h

#print axioms run_eq_of_stopped_le
#print axioms stopped_runs_eq
#print axioms terminal_eq_run
#print axioms run_one_succ
#print axioms terminal_succ
#print axioms eval_succ
end DiophantineConsistency.ArithmeticCommandEvaluationPerm222Checks

import DiophantineConsistency.ArithmeticCommandRunPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandRunPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCommandTickPerm222 ArithmeticCommandRunPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (time initial : V) : ∃! out, runDef.val.Evalb ![out,time,initial] :=
  run_total time initial
example (word w : V) : Stopped (run word (liveValue word w)) := drained word w
example (time w : V) : run time (liveValue 0 w)=liveValue 0 w := run_done time w
theorem empty_word_is_not_halt (w : V) : evalValue 0 w ≠ 0 := by simp
example (word w : V) : ∃! out, evalDef.val.Evalb ![out,word,w] := eval_total word w

#print axioms run_defined
#print axioms run_defined_delta
#print axioms run_zero
#print axioms run_succ
#print axioms run_total
#print axioms run_stopped
#print axioms run_add
#print axioms drain_bound
#print axioms drained
#print axioms terminal_defined
#print axioms eval_defined
#print axioms eval_defined_delta
#print axioms eval_zero_word
#print axioms terminal_stopped
#print axioms eval_eq_zero_iff
#print axioms terminal_total
#print axioms eval_total
#print axioms totalitySentence_true
#print axioms isigma1_proves_totality
#print axioms peano_proves_totality
#print axioms empty_word_is_not_halt
end DiophantineConsistency.ArithmeticCommandRunPerm222Checks

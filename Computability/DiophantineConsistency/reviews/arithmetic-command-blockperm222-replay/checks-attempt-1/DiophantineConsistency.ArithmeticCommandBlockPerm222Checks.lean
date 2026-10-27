import DiophantineConsistency.ArithmeticCommandBlockPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandBlockPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCode254
open ArithmeticCommandStepPerm222 ArithmeticCommandAppendPerm222
open ArithmeticCommandRunPerm222 ArithmeticCommandBlockPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (rest t S d : V) : evalValue (nipWord rest) (stateValue t S d 1)=0 := by
  simp [eval_nip]
example (t S d : V) :
    evalValue (nipsWord 1) (stateValue t (cantor 1 S) d 0)=someState t S d 1 := by
  simpa only [List.nil_append, List.length_nil, Nat.zero_add, pushL] using
    eval_nips t S d [] 0 1 (by simp) (by simp)
example (t S : V) : evalValue discardWord (stateValue t S 0 0)=someState 0 S 0 0 :=
  eval_discard t S
example (S rest : V) :
    evalValue (appendValue (Jword 0) rest) (stateValue 0 S 0 0)=
      evalValue rest (stateValue 0 S 0 0) := eval_J 0 S rest
/-- Executing MP0 is not the zero loader: its result has a pushed zero. -/
example (S : V) : evalValue (mpWord 0 0) (stateValue 0 S 0 0)=
    someState 0 (cantor 0 S) 0 0 := by
  simp [eval_mp, wim, tagged, someState]
example (a b c t S rest : V) :
    evalValue (appendValue discardWord
      (appendValue (Jword 0) (axWord c a b rest))) (stateValue t S 0 0)=
        evalValue rest (stateValue (gateValue a b c) (axStackValue a 0 b c 0 0 S) 0 0) := by
  simpa using eval_discard_ax t S a b c 0 rest (by simp)
example (u b t S rest : V) :
    evalValue (appendValue discardWord
      (appendValue (Jword u) (axWord u 0 b rest))) (stateValue t S 0 0)=
        evalValue rest (stateValue 0 (axStackValue u 0 b u u 0 S) 0 0) := by
  simpa using eval_discard_ax t S u b u u rest le_rfl
example (a h b c u : V) : (axList a h b c u).length=9 := rfl
example (u : V) : JwordDef.val.Evalb ![Jword u,u] := by simp

#print axioms eval_nip
#print axioms eval_drop
#print axioms eval_mp
#print axioms eval_ax
#print axioms pushL_append
#print axioms eval_nips
#print axioms eval_nips_cont
#print axioms wim_ne_one
#print axioms wal_ne_one
#print axioms wim_right_ne_zero
#print axioms gate_ne_one
#print axioms axStack_eq
#print axioms axList_ne_one
#print axioms eval_discard
#print axioms Jword_defined
#print axioms Jword_zero
#print axioms eval_J
#print axioms eval_discard_ax
end DiophantineConsistency.ArithmeticCommandBlockPerm222Checks

import DiophantineConsistency.ArithmeticCommandRulePerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandRulePerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCode254
open ArithmeticCommandStepPerm222 ArithmeticCommandAppendPerm222 ArithmeticCommandRunPerm222
open ArithmeticCommandBlockPerm222 ArithmeticCommandLeafPerm222 ArithmeticCommandRulePerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (S : V) : evalValue (genTail 0) (stateValue 1 S 0 0)=
    someState (wal 0 1) S 0 0 := eval_genTail 0 1 S
example (i S : V) : evalValue (genTail i) (stateValue 1 S 0 0)=
    someState (wal i 1) S 0 0 := eval_genTail i 1 S
example (H S : V) : evalValue (genTail 0) (stateValue H S 0 0)=
    someState (wal 0 H) S 0 0 := eval_genTail 0 H S
example (B S : V) : evalValue (mpTail B) (stateValue (wim 1 B) (cantor 1 S) 0 0)=0 := by
  simp [eval_mpTail]
example (A S : V) : evalValue (mpTail 1) (stateValue (wim A 1) (cantor A S) 0 0)=0 := by
  simp [eval_mpTail]
example (A S : V) (ha : A≠1) :
    evalValue (mpTail 0) (stateValue (wim A 0) (cantor A S) 0 0)=someState 0 S 0 0 := by
  simp [eval_mpTail,ha]
example (S : V) : evalValue (mpTail 0) (stateValue (wim 0 0) (cantor 0 S) 0 0)=
    someState 0 S 0 0 := by simp [eval_mpTail]
example (i p : V) (hp : Contract p 1) : Contract (genBlockWord i p) (wal i 1) :=
  gen_contract i hp
example (A B pa pab : V) (ha : Contract pa A) (hab : Contract pab (wim A B)) :
    Contract (mpBlockWord B pa pab) B := mp_contract ha hab
example (A B pab S : V) (hab : Contract pab (wim A B)) :
    evalValue pab (stateValue 0 (cantor A S) 0 0)=0 ∨
    evalValue pab (stateValue 0 (cantor A S) 0 0)=someState (wim A B) (cantor A S) 0 0 :=
  hab 0 (cantor A S)
example (B S : V) :
    evalValue (appendValue (nipsWord 10) terminatorWord)
      (stateValue 0 (axStackValue B 0 0 B B B (cantor 0 S)) 0 0)=
      if B=1 then 0 else someState B S 0 0 := mp_cleanup B S
example (i : V) : Contract (genBlockWord i discardWord) (wal i 0) :=
  gen_contract i truth_contract

#print axioms genPrefix_ne_one
#print axioms gen_cleanup
#print axioms eval_genTail
#print axioms mp_cleanup
#print axioms eval_mpTail
#print axioms gen_contract
#print axioms mp_contract
end DiophantineConsistency.ArithmeticCommandRulePerm222Checks

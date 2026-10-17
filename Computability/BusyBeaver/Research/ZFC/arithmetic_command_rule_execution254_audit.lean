import BusyBeaver.ZFC.ArithmeticCommandRuleExecution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticCommandStep254
open ArithmeticCommandBlocks254 ArithmeticCommandRun254 ArithmeticProofWordContract254
open ArithmeticCommandRuleExecution254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.circuit_terminator
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.circuit_genBlock
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.circuit_mpBlock
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.gen_cleanup
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.eval_genTail
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.mp_cleanup
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.eval_mpTail
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.gen_contract
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.mp_contract
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.circuit_gen_contract
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254.circuit_mp_contract
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (i p : Circuit) (a b c u : V) :
    (Circuit.genBlock i p).eval a b c u = genBlockWord (i.eval a b c u) (p.eval a b c u) :=
  circuit_genBlock i p a b c u
example (b pa pab : Circuit) (a d c u : V) :
    (Circuit.mpBlock b pa pab).eval a d c u =
      mpBlockWord (b.eval a d c u) (pa.eval a d c u) (pab.eval a d c u) :=
  circuit_mpBlock b pa pab a d c u
example (i h s : V) : evalValue (genTail i) (stateValue h s 0 0) = someState (wal i h) s 0 0 :=
  eval_genTail i h s
example (a b s : V) : evalValue (mpTail b) (stateValue (wim a b) (cantor a s) 0 0) =
    if a=1 ∨ b=1 then 0 else someState b s 0 0 := eval_mpTail a b s
example (i p h : V) (hp : Contract p h) : Contract (genBlockWord i p) (wal i h) := gen_contract i hp
example (a b pa pab : V) (hp : Contract pa a) (hq : Contract pab (wim a b)) :
    Contract (mpBlockWord b pa pab) b := mp_contract hp hq
example (i p : Circuit) (a b c u h : V) (hp : Contract (p.eval a b c u) h) :
    Contract ((Circuit.genBlock i p).eval a b c u) (wal (i.eval a b c u) h) :=
  circuit_gen_contract i p a b c u h hp
example (b pa pab : Circuit) (a d c u x : V)
    (hp : Contract (pa.eval a d c u) x) (hq : Contract (pab.eval a d c u) (wim x (b.eval a d c u))) :
    Contract ((Circuit.mpBlock b pa pab).eval a d c u) (b.eval a d c u) :=
  circuit_mp_contract b pa pab a d c u x hp hq

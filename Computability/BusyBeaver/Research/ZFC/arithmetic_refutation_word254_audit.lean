import BusyBeaver.ZFC.ArithmeticRefutationWord254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandRun254
open ArithmeticCommandAppend254 ArithmeticCommandRuleExecution254 ArithmeticProofWord254
open ArithmeticRefutationWord254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.resetCircuit_eval
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.refutationWord_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.refutationWord_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.refutationWord_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.eval_terminator_falsity
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.proof_then_terminator
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.eval_refutationWord_state
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.stateValue_projections
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.eval_refutationWord
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.represented_refutation
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRefutationWord254.refutation_exists
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (out code : V) : refutationWordDef.val.Evalb ![out,code] ↔ out=refutationWord code := by simp
example (code : V) : ∃! word, refutationWordDef.val.Evalb ![word,code] := refutationWord_total code
example (code : V) : refutationWord code≠0 := refutationWord_ne_zero code
example (stack : V) : evalValue terminatorWord (stateValue 1 stack 0 0)=0 := eval_terminator_falsity stack
example (code top stack : V) (hv : ArithmeticHistory254.value code=2) :
    evalValue (appendValue (rawWord code) terminatorWord) (stateValue top stack 0 0)=0 := proof_then_terminator code top stack hv
example (code top stack d h : V) (hv : ArithmeticHistory254.value code=2) :
    evalValue (refutationWord code) (stateValue top stack d h)=0 := eval_refutationWord_state code top stack d h hv
example (w : V) : stateValue (first w) (first (second w)) (first (second (second w))) (second (second (second w)))=w := stateValue_projections w
example (code w : V) (hv : ArithmeticHistory254.value code=2) : evalValue (refutationWord code) w=0 := eval_refutationWord code w hv
example (code : V) (hv : ArithmeticHistory254.value code=2) :
    ∃ word, refutationWordDef.val.Evalb ![word,code] ∧ word≠0 ∧ ∀ w, evalValue word w=0 := represented_refutation code hv
example (code : V) (hv : ArithmeticHistory254.value code=2) : ∃ word : V,∀ w : V,evalValue word w=0 := refutation_exists code hv
example (code : V) (hv : ArithmeticHistory254.value code=2) : evalValue (refutationWord code) 0=0 := eval_refutationWord code 0 hv
example (code : V) (hv : ArithmeticHistory254.value code=2) : evalValue (refutationWord code) (stateValue 1 1 1 1)=0 := eval_refutationWord_state code 1 1 1 1 hv

import BusyBeaver.ZFC.ArithmeticEnumeratorStep254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandWord254
open ArithmeticEnumeratorStep254
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.live_decode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.advance_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.step_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.step_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.step_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.step_live
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.step_boundary
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.step_active
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.advance_nonzero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.step_active_decreases
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.step_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.command_unpacked_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.advance_execAt_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorStep254.step_encode_nat
example (config : V) : ∃! out, stepDef.val.Evalb ![out,config] := step_total config
example (config : V) (hc : config ≠ 0) :
    liveValue (pointer config) (candidate config) (working config) = config := live_decode config hc
example : step (0 : V) = 0 := step_zero
example (np work : V) :
    step (liveValue 0 np work) = advanceValue np (np+1) work := step_boundary np work
example (pl np work : V) (hp : pl ≠ 0) :
    step (liveValue pl np work) = advanceValue (pl-1) np work := step_active pl np work hp
example (pl np work : V) (hp : pl ≠ 0) :
    step (liveValue pl np work) = 0 ∨
      (pointer (step (liveValue pl np work)) + 1 ≤ pl ∧
       candidate (step (liveValue pl np work)) = np) := step_active_decreases pl np work hp
example (raw np work : V) (hz : stepValue raw work = 0) : advanceValue raw np work = 0 := by
  simp [advanceValue, hz]
example (raw np work : V) (hz : advanceValue raw np work ≠ 0) :
    candidate (advanceValue raw np work) = np := by rw [advance_nonzero _ _ _ hz, candidate_live]
example (s : Enum254.St) :
    step (encodeSt s) = encodeResult (Enum254.enumStep s) := step_encode_nat s
example (pl np t stack d h : Nat) :
    step (encodeSt ⟨pl,np,t,stack,d,h⟩) =
      encodeResult (Enum254.enumStep ⟨pl,np,t,stack,d,h⟩) := step_encode_nat _
example (raw np : Nat) (s : Enum254.St) :
    advanceValue raw np (encodeW (Enum254.toW s)) = encodeResult (Enum254.execAt raw np s) :=
  advance_execAt_nat raw np s
example : step (encodeSt Enum254.s0) = encodeResult (some ⟨0,1,0,0,0,0⟩) := by
  rw [step_encode_nat]
  rfl

import BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCommandStep254 ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254
open ArithmeticEnumeratorRefutation254
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254.halts_of_accepted
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254.represented_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254.forwardSentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254.isigma1_proves_forward
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254.peano_proves_forward
example (code initialWork : V) (hv : ArithmeticHistory254.value code = 2) :
    ∃ time, run time (liveValue 0 0 initialWork) = 0 := halts_of_accepted code initialWork hv
example (code : V) (hv : ArithmeticHistory254.value code = 2) :
    ∃ time, run time (liveValue (0 : V) 0 0) = 0 := halts_of_accepted code 0 hv
example (code top stack d h : V) (hv : ArithmeticHistory254.value code = 2) :
    ∃ time, run time (liveValue 0 0 (stateValue top stack d h)) = 0 :=
  halts_of_accepted code _ hv
example (code initialWork : V) (hv : ArithmeticHistory254.value code = 2) :
    ∃ initial, liveDef.val.Evalb ![initial,0,0,initialWork] ∧
      ∃ time, runDef.val.Evalb ![0,time,initial] := represented_halt code initialWork hv
example : forwardSentence.Evalb (M := V) ![] := forwardSentence_true
example : 𝗜𝚺₁ ⊢ forwardSentence := isigma1_proves_forward
example : Peano ⊢ forwardSentence := peano_proves_forward
example : ArithmeticHistory254.value (0 : V) ≠ 2 := by simp
example (hn : ∀ time : V, run time (liveValue 0 0 0) ≠ 0) :
    ∀ code : V, ArithmeticHistory254.value code ≠ 2 := by
  intro code hv
  obtain ⟨time, ht⟩ := halts_of_accepted code 0 hv
  exact hn time ht

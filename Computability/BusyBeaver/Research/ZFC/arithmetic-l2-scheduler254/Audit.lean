import BusyBeaver.ZFC.ArithmeticL2Scheduler254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticL2 ArithmeticCantor ArithmeticDagRun
open ArithmeticCommandStep254 (stateValue)

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.reads_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.root_step

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (np pl1 tw ws d h : V) {y : V}
    (hd : IR (.node 141) (enc ⟨np, tw, ws, first pl1, d + first (second pl1), h, 0, 0,
      second (second pl1)⟩) .halt y) :
    IR (.node 139) (enc ⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩) .halt y :=
  ArithmeticL2.reads_halt np pl1 tw ws d h hd

example (pl np t s d h : V) :
    (ArithmeticEnumeratorStep254.step (ArithmeticEnumeratorStep254.liveValue pl np
        (stateValue t s d h)) = 0 ∧
      ∃ y, IR (.node 0) (enc (toAS pl np t s d h)) .halt y) ∨
    (∃ pl' np' t' s' d' h', ArithmeticEnumeratorStep254.step
        (ArithmeticEnumeratorStep254.liveValue pl np (stateValue t s d h)) =
        ArithmeticEnumeratorStep254.liveValue pl' np' (stateValue t' s' d' h') ∧
      Rn (.node 0) (toAS pl np t s d h) (toAS pl' np' t' s' d' h') ∧
      (pl' < pl ∨ np' = np + 1)) :=
  ArithmeticL2.root_step pl np t s d h


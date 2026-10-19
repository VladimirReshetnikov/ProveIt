import BusyBeaver.ZFC.ArithmeticL2Endpoint254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticL2 ArithmeticCantor ArithmeticDagRun
open ArithmeticCommandStep254 (stateValue)

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.root_occB
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.root_occ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.related_step
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.accepted_iff_dag_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticL2.accepted_iff_rotation_halts

example :
    occB Dag254.dag254 DagControl254.rowsLit 220 (.node 0) 1 (fun _ => 1) = true :=
  ArithmeticL2.root_occB

example : Occ Dag254.dag254 DagControl254.rowsLit 220 (.node 0) 1 (fun _ => 1) :=
  ArithmeticL2.root_occ

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (l b : V) (hr : Related l b)
    (hn : ArithmeticEnumeratorStep254.step l ≠ 0) :
    ∃ k, 0 < k ∧ Related (ArithmeticEnumeratorStep254.step l) (DagControl254.run k b) :=
  ArithmeticL2.related_step l b hr hn

example (pl np t s d h : V) :
    (∃ n, ArithmeticEnumeratorRun254.run n
        (ArithmeticEnumeratorStep254.liveValue pl np (stateValue t s d h)) = 0) ↔
      (∃ k, DagControl254.run k (binOf pl np t s d h) = 0) :=
  ArithmeticL2.halts_iff pl np t s d h

example :
    (∃ code : V, ArithmeticHistory254.value code = 2) ↔
      (∃ k, DagControl254.run k
        (ArithmeticControlFile.liveValue 1 (enc (⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩ : AS V))) = 0) :=
  ArithmeticL2.accepted_iff_dag_halts

example :
    (∃ code : V, ArithmeticHistory254.value code = 2) ↔
      (∃ k, ArithmeticControlTable.controlRun ControlBisimRotation240.tableR k
        (ArithmeticControlFile.liveValue 1 (enc (⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩ : AS V))) = 0) :=
  ArithmeticL2.accepted_iff_rotation_halts

example (h : ∃ code : V, ArithmeticHistory254.value code = 2) :
    ∃ k, ArithmeticControlTable.controlRun ControlBisimRotation240.tableR k
      (ArithmeticControlFile.liveValue 1 (enc (⟨3,0,0,0,3,0,0,0,0⟩ : AS V))) = 0 :=
  accepted_iff_rotation_halts.mp h
example (h : ∃ k : V, ArithmeticControlTable.controlRun ControlBisimRotation240.tableR k
    (ArithmeticControlFile.liveValue 1 (enc (⟨3,0,0,0,3,0,0,0,0⟩ : AS V))) = 0) :
    ∃ code : V, ArithmeticHistory254.value code = 2 := accepted_iff_rotation_halts.mpr h

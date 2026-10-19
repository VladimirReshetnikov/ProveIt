import BusyBeaver.ZFC.ControlBisimRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ControlBisimRotation240 ArithmeticControlBisim ArithmeticControlTable
open ArithmeticControlFile (regValue liveValue)

#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240.check0
#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240.check1
#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240.check2
#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240.check3
#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240.check_all
#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240.cert_zero
#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240.specR
#print axioms SetTheory.BusyBeaver.ZFC.ControlBisimRotation240.halts_iff

example : chunk 0 1000 = true :=
  ControlBisimRotation240.check0

example : chunk 1000 1000 = true :=
  ControlBisimRotation240.check1

example : chunk 2000 1000 = true :=
  ControlBisimRotation240.check2

example : chunk 3000 862 = true :=
  ControlBisimRotation240.check3

example (i : Nat) (hi : i < BisimCertRotation240.size) :
    entryOK DagControl254.rowsLit rowsLitR cert BisimCertRotation240.fuel
      BisimCertRotation240.size i = true :=
  ControlBisimRotation240.check_all i hi

example : cert 0 = some ⟨1, 1, [0,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0], 1, 2⟩ :=
  ControlBisimRotation240.cert_zero

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (c : Nat) (row : Row) (x : V) (h : rowsLitR c = some row) :
    stepValue tableR (liveValue (c : V) x) = sem regValue write liveValue row x :=
  ControlBisimRotation240.specR c row x h

example (x : V) :
    (∃ t, controlRun DagControl254.table t (liveValue 1 x) = 0) ↔
      (∃ t, controlRun tableR t (liveValue 1 x) = 0) :=
  ControlBisimRotation240.halts_iff x

example (x : V) (h : ∃ t, controlRun DagControl254.table t (liveValue 1 x) = 0) :
    ∃ t, controlRun tableR t (liveValue 1 x) = 0 := (ControlBisimRotation240.halts_iff x).mp h
example (x : V) (h : ∃ t, controlRun tableR t (liveValue 1 x) = 0) :
    ∃ t, controlRun DagControl254.table t (liveValue 1 x) = 0 :=
  (ControlBisimRotation240.halts_iff x).mpr h

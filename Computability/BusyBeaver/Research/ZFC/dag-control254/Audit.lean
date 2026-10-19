import BusyBeaver.ZFC.DagControl254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.DagControl254.spec

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (c : Nat) (row : ArithmeticControlBisim.Row) (x : V)
    (h : DagControl254.rowsLit c = some row) :
    ArithmeticControlTable.stepValue DagControl254.table
      (ArithmeticControlFile.liveValue (c : V) x) =
      ArithmeticControlBisim.sem ArithmeticControlFile.regValue ArithmeticControlTable.write
        ArithmeticControlFile.liveValue row x := DagControl254.spec c row x h

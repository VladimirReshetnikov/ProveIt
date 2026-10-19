import BusyBeaver.ZFC.BisimCertRotation240

/-! Data interface only. No full certificate, chunk, or table-equality evaluation. -/
open SetTheory.BusyBeaver.ZFC
open BisimCertRotation240

#print axioms SetTheory.BusyBeaver.ZFC.BisimCertRotation240.tableR
#print axioms SetTheory.BusyBeaver.ZFC.BisimCertRotation240.countR

example : Nat := tableR
example : countR = 6455 := rfl
example : List ArithmeticControlBisim.Row := PackedTables.table tableR countR
example : (PackedTables.table tableR countR).length = countR :=
  PackedTables.table_length tableR countR

import BusyBeaver.ZFC.PackedTables

open SetTheory.BusyBeaver.ZFC
open ArithmeticControlBisim PackedTables

#print axioms SetTheory.BusyBeaver.ZFC.PackedTables.rowsOf_some
#print axioms SetTheory.BusyBeaver.ZFC.PackedTables.table_length

example (packed count c : Nat) (row : Row) (h : rowsOf packed count c = some row) :
    c ≠ 0 ∧ getElem? (table packed count) (c-1) = some row :=
  rowsOf_some packed count c row h
example (packed count : Nat) : (table packed count).length = count := table_length packed count
example (packed count : Nat) : Nat → Option Row := rowsOf packed count
example (packed count : Nat) : Nat → Option Entry := certOf packed count

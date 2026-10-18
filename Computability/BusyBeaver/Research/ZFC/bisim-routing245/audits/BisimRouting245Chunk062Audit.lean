import BusyBeaver.ZFC.BisimRouting245Chunk062
open SetTheory.BusyBeaver.ZFC
open RMBisim
#print axioms BisimRouting245Chunk062.checked

example : allC BisimRouting245Data.test BisimRouting245Data.chunk062 = true := BisimRouting245Chunk062.checked
example {j : Nat} {e : Entry} (h : lookupC BisimRouting245Data.chunk062 j = some e) :
    entryOk ActualTree254.tree TreeRouting245.tree BisimRouting245Data.cert e = true :=
  lookupC_all h BisimRouting245Chunk062.checked

import BusyBeaver.ZFC.BisimRouting245Chunk094
open SetTheory.BusyBeaver.ZFC
open RMBisim
#print axioms BisimRouting245Chunk094.checked

example : allC BisimRouting245Data.test BisimRouting245Data.chunk094 = true := BisimRouting245Chunk094.checked
example {j : Nat} {e : Entry} (h : lookupC BisimRouting245Data.chunk094 j = some e) :
    entryOk ActualTree254.tree TreeRouting245.tree BisimRouting245Data.cert e = true :=
  lookupC_all h BisimRouting245Chunk094.checked

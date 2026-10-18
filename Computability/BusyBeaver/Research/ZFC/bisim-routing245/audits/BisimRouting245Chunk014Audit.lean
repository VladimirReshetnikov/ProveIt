import BusyBeaver.ZFC.BisimRouting245Chunk014
open SetTheory.BusyBeaver.ZFC
open RMBisim
#print axioms BisimRouting245Chunk014.checked

example : allC BisimRouting245Data.test BisimRouting245Data.chunk014 = true := BisimRouting245Chunk014.checked
example {j : Nat} {e : Entry} (h : lookupC BisimRouting245Data.chunk014 j = some e) :
    entryOk ActualTree254.tree TreeRouting245.tree BisimRouting245Data.cert e = true :=
  lookupC_all h BisimRouting245Chunk014.checked

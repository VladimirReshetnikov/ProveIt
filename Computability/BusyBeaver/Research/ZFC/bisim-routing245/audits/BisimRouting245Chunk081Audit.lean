import BusyBeaver.ZFC.BisimRouting245Chunk081
open SetTheory.BusyBeaver.ZFC
open RMBisim
#print axioms BisimRouting245Chunk081.checked

example : allC BisimRouting245Data.test BisimRouting245Data.chunk081 = true := BisimRouting245Chunk081.checked
example {j : Nat} {e : Entry} (h : lookupC BisimRouting245Data.chunk081 j = some e) :
    entryOk ActualTree254.tree TreeRouting245.tree BisimRouting245Data.cert e = true :=
  lookupC_all h BisimRouting245Chunk081.checked

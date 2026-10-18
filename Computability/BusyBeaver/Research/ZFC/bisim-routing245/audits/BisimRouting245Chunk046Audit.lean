import BusyBeaver.ZFC.BisimRouting245Chunk046
open SetTheory.BusyBeaver.ZFC
open RMBisim
#print axioms BisimRouting245Chunk046.checked

example : allC BisimRouting245Data.test BisimRouting245Data.chunk046 = true := BisimRouting245Chunk046.checked
example {j : Nat} {e : Entry} (h : lookupC BisimRouting245Data.chunk046 j = some e) :
    entryOk ActualTree254.tree TreeRouting245.tree BisimRouting245Data.cert e = true :=
  lookupC_all h BisimRouting245Chunk046.checked

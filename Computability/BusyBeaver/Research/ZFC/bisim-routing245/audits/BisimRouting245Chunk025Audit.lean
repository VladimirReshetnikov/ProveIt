import BusyBeaver.ZFC.BisimRouting245Chunk025
open SetTheory.BusyBeaver.ZFC
open RMBisim
#print axioms BisimRouting245Chunk025.checked

example : allC BisimRouting245Data.test BisimRouting245Data.chunk025 = true := BisimRouting245Chunk025.checked
example {j : Nat} {e : Entry} (h : lookupC BisimRouting245Data.chunk025 j = some e) :
    entryOk ActualTree254.tree TreeRouting245.tree BisimRouting245Data.cert e = true :=
  lookupC_all h BisimRouting245Chunk025.checked

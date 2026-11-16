module
public import M6.Source.AXFullPlan
public import M6.Source.AXComposition
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXCommand

/-- Actual AX command with explicitly supplied two encoded field values.
All3779 primitive source leaves are accounted for by the full macro Plan and gate. -/
theorem encoded (t c d h y x tail bottom : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n
      (AXMacro.configAt 25 ⟨t,c,d,h,Cantor.pair y (Cantor.pair x tail),[]⟩ bottom f)
      (AXMacro.configAt 3910
        ⟨ActualAXCode.gate (d+x) (h+y) c,0,0,0,tail,
          ActualAXCode.pa135Heads (d+x) (h+y) c d h ++ [t]⟩ bottom f) :=
  AXComposition.full_effect AXAll.full_plan t c d h y x tail bottom f

/-- Every natural field stack is covered, including zero and the Cantor zero alias. -/
theorem decoded (t c d h l bottom : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n
      (AXMacro.configAt 25 ⟨t,c,d,h,l,[]⟩ bottom f)
      (AXMacro.configAt 3910
        ⟨ActualAXCode.gate (d+(Cantor.decode (Cantor.decode l).2).1) (h+(Cantor.decode l).1) c,
          0,0,0,(Cantor.decode (Cantor.decode l).2).2,
          ActualAXCode.pa135Heads (d+(Cantor.decode (Cantor.decode l).2).1)
            (h+(Cantor.decode l).1) c d h ++ [t]⟩ bottom f) := by
  have hh := encoded t c d h (Cantor.decode l).1 (Cantor.decode (Cantor.decode l).2).1
    (Cantor.decode (Cantor.decode l).2).2 bottom f
  simpa only [Cantor.pair_decode] using hh

#print axioms encoded
#print axioms decoded
end M6.Source.AXCommand


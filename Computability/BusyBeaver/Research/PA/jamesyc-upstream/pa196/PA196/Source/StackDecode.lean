module
public import PA196.Source.Readers
public import PA196.Program
@[expose] public section
namespace PA196.Source.StackDecode
open M6.Source

private def relocation : UnpairRelocation := ⟨id, fun _ => rfl, 11, 25⟩

private theorem bound : Readers.Bound Program.sites relocation := by
  unfold Readers.Bound
  simp only [Program.resolve_tree]
  decide +kernel

/-- The stack decoder returns directly to the physical fetch port 25. -/
theorem unpair (n : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ Steps Program.sites m
      ⟨.at 11,Unpair.registers ⟨n,0,0,0,f⟩⟩
      ⟨.at 25,Unpair.registers ⟨(Cantor.decode n).2,(Cantor.decode n).1,0,0,f⟩⟩ := by
  obtain ⟨m,hm,_,hs⟩ := Readers.unpair_add relocation bound n 0 f
  refine ⟨m,hm,?_⟩
  change Steps Program.sites m
    ⟨.at 11,Unpair.registers ⟨n,0,0,0,f⟩⟩
    ⟨.at 25,Unpair.registers ⟨(Cantor.decode n).2,0+(Cantor.decode n).1,0,0,f⟩⟩ at hs
  simpa only [Nat.zero_add] using hs

#print axioms unpair
end PA196.Source.StackDecode

module
public import PA196.Source.Readers
public import PA196.Program
@[expose] public section
namespace PA196.Source.FetchUnpair
open M6.Source

def registers (l a x y : Nat) (frame : Registers) : Registers := fun r =>
  if r = 8 then l else if r = 3 then a else if r = 6 then x else if r = 7 then y else frame r

private def relocation : UnpairRelocation :=
  ⟨M6.Source.FetchUnpair.rename, M6.Source.FetchUnpair.rename_involution, 34, 48⟩

private theorem bound : Readers.Bound Program.sites relocation := by
  unfold Readers.Bound
  simp only [Program.resolve_tree]
  decide +kernel

private theorem register_bridge (l a x y : Nat) (f : Registers) :
    relocation.regs (Unpair.registers ⟨l,a,x,y,relocation.regs f⟩) =
      registers l a x y f := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- Exact selector decoding in the PA196 source, from physical port 34 to 48. -/
theorem fetch_decode (n : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ m ≤ Unpair.loopCost n (0,0) +
      (3*(Cantor.decode n).2+1) + (3*(Cantor.decode n).1+1) ∧
      Steps Program.sites m ⟨.at 34,registers n 0 0 0 f⟩
        ⟨.at 48,registers (Cantor.decode n).2 (Cantor.decode n).1 0 0 f⟩ := by
  obtain ⟨m,hm,hbound,hs⟩ := Readers.unpair_add relocation bound n 0 (relocation.regs f)
  refine ⟨m,hm,hbound,?_⟩
  change Steps Program.sites m
    ⟨.at 34,relocation.regs (Unpair.registers ⟨n,0,0,0,relocation.regs f⟩)⟩
    ⟨.at 48,relocation.regs
      (Unpair.registers ⟨(Cantor.decode n).2,0+(Cantor.decode n).1,0,0,relocation.regs f⟩)⟩ at hs
  simpa only [register_bridge,Nat.zero_add] using hs

#print axioms fetch_decode
end PA196.Source.FetchUnpair

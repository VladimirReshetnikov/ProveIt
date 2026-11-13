module
public import M6.Source.AXMacroRead
@[expose] public section
namespace PA196.Source.Readers
open M6.Source

/-- The old decoder's instruction schema, checked against any target source. -/
def Bound (sites : Array Site) (p : UnpairRelocation) : Prop :=
  ∀ j : Fin 14, resolveAt sites (p.base+j.val) =
    some (p.instruction unpairExpected[j.val])

theorem step_commutes {sites : Array Site} (p : UnpairRelocation)
    (hbound : Bound sites p) (c : Configuration) (hc : FetchUnpair.InBlock c)
    (hne : c.control ≠ .exited) :
    step sites (p.embed c) = p.embed (step exactSites c) := by
  rcases c with ⟨q,r⟩
  rcases hc with h | ⟨j,h⟩
  · exact False.elim (hne h)
  · simp only at h
    subst q
    change step sites ⟨.at (p.base+(3933+j.val-3933)),p.regs r⟩ = _
    have he : 3933+j.val-3933 = j.val := by omega
    rw [he,step_of_resolved (hbound j),step_of_resolved (unpair_resolved_at j)]
    exact p.execute_commutes _ r

/-- The transport is between distinct source arrays. All 14 target rows must
be proved; no old PA209 source equality is substituted for that obligation. -/
theorem unpair_add {sites : Array Site} (p : UnpairRelocation)
    (hbound : Bound sites p) (n h : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ m ≤ Unpair.loopCost n (0,0) +
      (3*(Cantor.decode n).2+1) + (3*(Cantor.decode n).1+1) ∧
      Steps sites m
        (p.embed (Unpair.configAt 3933 ⟨n,h,0,0,f⟩))
        (p.embed (Unpair.exitAt ⟨(Cantor.decode n).2,h+(Cantor.decode n).1,0,0,f⟩)) := by
  exact transfer_until_exit p.embed FetchUnpair.InBlock FetchUnpair.preserve
    (step_commutes p hbound) (Unpair.unpair_add n h f)
    (Or.inr ⟨⟨0,by decide⟩,rfl⟩) (by simp [Unpair.configAt]) rfl

open AXMacro
private theorem readerH_registers (base : Nat) (s : Store) (l v bottom : Nat) (f : Registers) :
    (readerH base).regs (Unpair.registers ⟨l,v,0,0,(readerH base).regs (registers s bottom f)⟩) =
      registers {s with l := l, h := v} bottom f := by
  funext j
  by_cases h1 : j=1 <;> by_cases h2 : j=2 <;> by_cases h3 : j=3 <;>
    by_cases h4 : j=4 <;> by_cases h5 : j=5 <;> by_cases h6 : j=6 <;>
    by_cases h7 : j=7 <;> by_cases h8 : j=8 <;>
    simp_all [readerH,renameH,UnpairRelocation.regs,Unpair.registers,registers]

theorem readH_realizes {sites : Array Site} (base : Nat)
    (hb : Bound sites (readerH base)) : Realizes sites .readH base (base+14) := by
  intro s s' he bottom f
  simp only [exec,Option.some.injEq] at he
  subst s'
  obtain ⟨n,hn,_,hs⟩ := unpair_add (readerH base) hb s.l s.h
    ((readerH base).regs (registers s bottom f))
  refine ⟨n,hn,?_⟩
  simpa only [UnpairRelocation.embed,Unpair.configAt,Unpair.exitAt,
    UnpairRelocation.control,readerH_registers,
    show (readerH base).base=base from rfl,
    show (readerH base).exitPort=base+14 from rfl,
    Nat.sub_self,Nat.add_zero,configAt] using hs

private theorem readerD_registers (base : Nat) (s : Store) (l v bottom : Nat) (f : Registers) :
    (readerD base).regs (Unpair.registers ⟨l,v,0,0,(readerD base).regs (registers s bottom f)⟩) =
      registers {s with l := l, d := v} bottom f := by
  funext j
  by_cases h1 : j=1 <;> by_cases h2 : j=2 <;> by_cases h3 : j=3 <;>
    by_cases h4 : j=4 <;> by_cases h5 : j=5 <;> by_cases h6 : j=6 <;>
    by_cases h7 : j=7 <;> by_cases h8 : j=8 <;>
    simp_all [readerD,renameD,UnpairRelocation.regs,Unpair.registers,registers]

theorem readD_realizes {sites : Array Site} (base : Nat)
    (hb : Bound sites (readerD base)) : Realizes sites .readD base (base+14) := by
  intro s s' he bottom f
  simp only [exec,Option.some.injEq] at he
  subst s'
  obtain ⟨n,hn,_,hs⟩ := unpair_add (readerD base) hb s.l s.d
    ((readerD base).regs (registers s bottom f))
  refine ⟨n,hn,?_⟩
  simpa only [UnpairRelocation.embed,Unpair.configAt,Unpair.exitAt,
    UnpairRelocation.control,readerD_registers,
    show (readerD base).base=base from rfl,
    show (readerD base).exitPort=base+14 from rfl,
    Nat.sub_self,Nat.add_zero,configAt] using hs

#print axioms readH_realizes
#print axioms readD_realizes
end PA196.Source.Readers

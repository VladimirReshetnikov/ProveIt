module
public import M6.Source.AXMacroSound
public import M6.Source.UnpairRelocation
@[expose] public section
namespace M6.Source.AXMacro

def renameH (r : Fin 9) : Fin 9 := if r=2 then 8 else if r=8 then 2 else r
def renameD (r : Fin 9) : Fin 9 :=
  if r=2 then 8 else if r=8 then 2 else if r=4 then 5 else if r=5 then 4 else r
def readerH (base : Nat) : UnpairRelocation := ⟨renameH,by decide,base,base+14⟩
def readerD (base : Nat) : UnpairRelocation := ⟨renameD,by decide,base,base+14⟩
private theorem readerH_registers (base : Nat) (s : Store) (l v bottom : Nat) (f : Registers) :
    (readerH base).regs (Unpair.registers ⟨l,v,0,0,(readerH base).regs (registers s bottom f)⟩) =
      registers {s with l := l, h := v} bottom f := by
  funext j
  by_cases h1 : j=1 <;> by_cases h2 : j=2 <;> by_cases h3 : j=3 <;>
    by_cases h4 : j=4 <;> by_cases h5 : j=5 <;> by_cases h6 : j=6 <;>
    by_cases h7 : j=7 <;> by_cases h8 : j=8 <;>
    simp_all [readerH,renameH,UnpairRelocation.regs,Unpair.registers,registers]

theorem readH_realizes (base : Nat) (hb : (readerH base).Bound) :
    Realizes exactSites .readH base (base+14) := by
  intro s s' he bottom f
  simp only [exec,Option.some.injEq] at he
  subst s'
  obtain ⟨n,hn,_,hs⟩ := (readerH base).unpair_add hb s.l s.h
    ((readerH base).regs (registers s bottom f))
  refine ⟨n,hn,?_⟩
  simpa only [UnpairRelocation.embed,Unpair.configAt,Unpair.exitAt,
    UnpairRelocation.control,readerH_registers,
    show (readerH base).base=base from rfl,
    show (readerH base).exitPort=base+14 from rfl,
    Nat.sub_self,Nat.add_zero,configAt] using hs
#print axioms readH_realizes
private theorem readerD_registers (base : Nat) (s : Store) (l v bottom : Nat) (f : Registers) :
    (readerD base).regs (Unpair.registers ⟨l,v,0,0,(readerD base).regs (registers s bottom f)⟩) =
      registers {s with l := l, d := v} bottom f := by
  funext j
  by_cases h1 : j=1 <;> by_cases h2 : j=2 <;> by_cases h3 : j=3 <;>
    by_cases h4 : j=4 <;> by_cases h5 : j=5 <;> by_cases h6 : j=6 <;>
    by_cases h7 : j=7 <;> by_cases h8 : j=8 <;>
    simp_all [readerD,renameD,UnpairRelocation.regs,Unpair.registers,registers]

theorem readD_realizes (base : Nat) (hb : (readerD base).Bound) :
    Realizes exactSites .readD base (base+14) := by
  intro s s' he bottom f
  simp only [exec,Option.some.injEq] at he
  subst s'
  obtain ⟨n,hn,_,hs⟩ := (readerD base).unpair_add hb s.l s.d
    ((readerD base).regs (registers s bottom f))
  refine ⟨n,hn,?_⟩
  simpa only [UnpairRelocation.embed,Unpair.configAt,Unpair.exitAt,
    UnpairRelocation.control,readerD_registers,
    show (readerD base).base=base from rfl,
    show (readerD base).exitPort=base+14 from rfl,
    Nat.sub_self,Nat.add_zero,configAt] using hs
#print axioms readD_realizes
end M6.Source.AXMacro


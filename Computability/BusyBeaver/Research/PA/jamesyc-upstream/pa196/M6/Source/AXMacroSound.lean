module
public import M6.Source.AXMacro
public import M6.Source.AXPushParam
public import M6.Source.AXCons
public import M6.Source.CopyToT
@[expose] public section
namespace M6.Source.AXMacro

/-- A macro's full physical source meaning; no correctness is assumed by the type. -/
def Realizes (sites : Array Site) (op : Op) (start stop : Nat) : Prop :=
  ∀ s s', exec op s = some s' → ∀ bottom f,
    ∃ n, 0 < n ∧ Steps sites n (configAt start s bottom f) (configAt stop s' bottom f)

private theorem push_registers (s : Store) (t : Nat) (stack : List Nat)
    (bottom : Nat) (f : Registers) :
    AXPush.registers ⟨t,AXCode.stackCode stack bottom,0,0,registers s bottom f⟩ =
      registers {s with t := t, stack := stack} bottom f := by
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
    by_cases h4 : r=4 <;> by_cases h5 : r=5 <;> by_cases h6 : r=6 <;>
    by_cases h7 : r=7 <;> by_cases h8 : r=8 <;>
    simp_all [registers,AXPush.registers]

theorem push_realizes {sites : Array Site} {offset : Nat}
    (hb : AXPushParam.Bound sites offset) : Realizes sites .push (offset+25) (offset+44) := by
  intro s s' he bottom f
  simp only [exec,Option.some.injEq] at he
  subst s'
  obtain ⟨n,hn,hs⟩ := AXPushParam.push hb s.t (AXCode.stackCode s.stack bottom) (registers s bottom f)
  refine ⟨n,hn,?_⟩
  have hw : Cantor.pair s.t (AXCode.stackCode s.stack bottom) =
      AXCode.stackCode (s.t::s.stack) bottom := rfl
  rw [hw] at hs
  simpa only [AXPushParam.configAt,AXPushParam.registers,push_registers,configAt] using hs

theorem cons_realizes {sites : Array Site} {offset : Nat}
    (hp : UnpairPartial.Bound sites (offset+20))
    (hq : AXPair.Bound sites offset)
    (hm : AXTimes4.Bound sites (offset+41)) :
    Realizes sites .cons (offset+20) (offset+47) := by
  intro s s' he bottom f
  cases hstack : s.stack with
  | nil => simp [exec,hstack] at he
  | cons v vs =>
    simp only [exec,hstack,Option.some.injEq] at he
    subst s'
    obtain ⟨n,hn,hs⟩ := AXCons.cons hp hq hm s.t
      (AXCode.stackCode s.stack bottom) (registers s bottom f)
    have hw : AXCode.stackCode s.stack bottom = Cantor.pair v (AXCode.stackCode vs bottom) := by
      rw [hstack]
      rfl
    have hd : Cantor.decode (AXCode.stackCode s.stack bottom) = (v,AXCode.stackCode vs bottom) := by
      rw [hw,Cantor.decode_pair]
    rw [hd] at hs
    refine ⟨n,hn,?_⟩
    simpa only [AXPushParam.configAt,AXPushParam.registers,push_registers,configAt] using hs

private theorem copy_registers (r : Fin 9) (h1 : r ≠ 1) (h6 : r ≠ 6)
    (s : Store) (t bottom : Nat) (f : Registers) :
    CopyToT.registers r (registers s bottom f r) t 0 (registers s bottom f) =
      registers {s with t := t} bottom f := by
  funext j
  by_cases hr : j=r <;> by_cases hj1 : j=1 <;> by_cases hj2 : j=2 <;>
    by_cases hj3 : j=3 <;> by_cases hj4 : j=4 <;> by_cases hj5 : j=5 <;>
    by_cases hj6 : j=6 <;> by_cases hj7 : j=7 <;> by_cases hj8 : j=8 <;>
    simp_all [CopyToT.registers,registers]

theorem copy_effect {sites : Array Site} {base : Nat} (r : Fin 9)
    (h1 : r ≠ 1) (h6 : r ≠ 6) (hb : CopyToT.Bound sites r base)
    (s : Store) (bottom : Nat) (f : Registers) :
    Steps sites (7*registers s bottom f r+2) (configAt base s bottom f)
      (configAt (base+7) {s with t := s.t+registers s bottom f r} bottom f) := by
  have hh := CopyToT.copy h1 h6 hb (registers s bottom f r) s.t (registers s bottom f)
  simpa only [CopyToT.config,copy_registers r h1 h6,configAt,Nat.add_zero] using hh

theorem copyA_realizes {sites : Array Site} {base : Nat}
    (hb : CopyToT.Bound sites 3 base) : Realizes sites .copyA base (base+7) := by
  intro s s' he bottom f
  simp only [exec,Option.some.injEq] at he
  subst s'
  refine ⟨7*s.a+2,by omega,?_⟩
  simpa [registers] using copy_effect 3 (by decide) (by decide) hb s bottom f

theorem copyD_realizes {sites : Array Site} {base : Nat}
    (hb : CopyToT.Bound sites 4 base) : Realizes sites .copyD base (base+7) := by
  intro s s' he bottom f
  simp only [exec,Option.some.injEq] at he
  subst s'
  refine ⟨7*s.d+2,by omega,?_⟩
  simpa [registers] using copy_effect 4 (by decide) (by decide) hb s bottom f

theorem copyH_realizes {sites : Array Site} {base : Nat}
    (hb : CopyToT.Bound sites 5 base) : Realizes sites .copyH base (base+7) := by
  intro s s' he bottom f
  simp only [exec,Option.some.injEq] at he
  subst s'
  refine ⟨7*s.h+2,by omega,?_⟩
  simpa [registers] using copy_effect 5 (by decide) (by decide) hb s bottom f

private theorem write_t (s : Store) (t bottom : Nat) (f : Registers) :
    write (registers s bottom f) 1 t = registers {s with t := t} bottom f := by
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
    by_cases h4 : r=4 <;> by_cases h5 : r=5 <;> by_cases h6 : r=6 <;>
    by_cases h7 : r=7 <;> by_cases h8 : r=8 <;> simp_all [write,registers]

theorem inc_realizes {sites : Array Site} {base : Nat}
    (hb : resolveAt sites base = some (.inc 1 (some (base+1)))) :
    Realizes sites .incT base (base+1) := by
  intro s s' he bottom f
  simp only [exec,Option.some.injEq] at he
  subst s'
  refine ⟨1,by omega,?_⟩
  apply Steps.cons
  change Steps sites 0 (step sites ⟨.at base,registers s bottom f⟩) _
  rw [step_of_resolved hb]
  simp only [execute,destination,registers,ite_true,write_t]
  exact Steps.refl _
#print axioms push_realizes
#print axioms cons_realizes
#print axioms copyA_realizes
#print axioms copyD_realizes
#print axioms copyH_realizes
#print axioms inc_realizes
end M6.Source.AXMacro


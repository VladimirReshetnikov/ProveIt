module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourcePair
public import M6.Source.AXPushParam
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

theorem push_pair_bound (offset : Nat) (bound : Source.AXPushParam.Bound PA196.Program.sites offset) :
    Source.AXPair.Bound PA196.Program.sites offset := by
  intro j
  have h := bound ⟨j.val+6,by omega⟩
  have hi : offset+(25+(j.val+6))=offset+(31+j.val) := by omega
  rw [hi] at h
  exact h

theorem push_drain_t (offset : Nat) (hb : offset+44<3812)
    (bound : Source.AXPushParam.Bound PA196.Program.sites offset)
    (n xs : V) (hv : ValidStore xs) (hr : registers xs 1=n) :
    ∃ cs, Trace (3*n+1) cs (stateCode ((offset+26:Nat):V) xs)
      (stateCode ((offset+29:Nat):V) (drainEnd 1 6 n xs)) := by
  have h0 := bound ⟨0,by decide⟩
  have h1 := bound ⟨1,by decide⟩
  have h2 := bound ⟨2,by decide⟩
  simp only [Source.AXPushParam.expected,Source.AXPush.expected,Source.AXPushParam.relocate,
    Option.map_some,Nat.reduceAdd] at h0 h1 h2
  simpa only [Nat.add_assoc,Nat.reduceAdd] using
    drain_loop (offset+25) (offset+26) (offset+27) (offset+28)
      1 6 (by decide) (by omega) (by omega) (by omega) h0 h1 h2 n xs hv hr

theorem push_drain_w (offset : Nat) (hb : offset+44<3812)
    (bound : Source.AXPushParam.Bound PA196.Program.sites offset)
    (n xs : V) (hv : ValidStore xs) (hr : registers xs 2=n) :
    ∃ cs, Trace (3*n+1) cs (stateCode ((offset+29:Nat):V) xs)
      (stateCode ((offset+32:Nat):V) (drainEnd 2 1 n xs)) := by
  have h0 := bound ⟨3,by decide⟩
  have h1 := bound ⟨4,by decide⟩
  have h2 := bound ⟨5,by decide⟩
  simp only [Source.AXPushParam.expected,Source.AXPush.expected,Source.AXPushParam.relocate,
    Option.map_some,Nat.reduceAdd] at h0 h1 h2
  simpa only [Nat.add_assoc,Nat.reduceAdd] using
    drain_loop (offset+28) (offset+29) (offset+30) (offset+31)
      2 1 (by decide) (by omega) (by omega) (by omega) h0 h1 h2 n xs hv hr

theorem push_drain_y (offset : Nat) (hb : offset+44<3812)
    (bound : Source.AXPushParam.Bound PA196.Program.sites offset)
    (n xs : V) (hv : ValidStore xs) (hr : registers xs 7=n) :
    ∃ cs, Trace (3*n+1) cs (stateCode ((offset+42:Nat):V) xs)
      (stateCode ((offset+45:Nat):V) (drainEnd 7 2 n xs)) := by
  have h0 := bound ⟨16,by decide⟩
  have h1 := bound ⟨17,by decide⟩
  have h2 := bound ⟨18,by decide⟩
  simp only [Source.AXPushParam.expected,Source.AXPush.expected,Source.AXPushParam.relocate,
    Option.map_some,Nat.reduceAdd] at h0 h1 h2
  simpa only [Nat.add_assoc,Nat.reduceAdd] using
    drain_loop (offset+41) (offset+42) (offset+43) (offset+44)
      7 2 (by decide) (by omega) (by omega) (by omega) h0 h1 h2 n xs hv hr
#print axioms push_pair_bound
#print axioms push_drain_t
#print axioms push_drain_w
#print axioms push_drain_y
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource


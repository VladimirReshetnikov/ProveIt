module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourcePairSpec
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

 theorem pair_drain_t (offset : Nat) (hb : offset+41<3947)
    (bound : Source.AXPair.Bound Source.exactSites offset)
    (n xs : V) (hv : ValidStore xs) (ht : registers xs 1=n) :
    ∃ cs, Trace (4*n+1) cs (stateCode ((offset+32:Nat):V) xs)
      (stateCode ((offset+36:Nat):V) (drainTwoEnd 1 7 6 n xs)) := by
  have h0 := bound ⟨0,by decide⟩
  have h1 := bound ⟨1,by decide⟩
  have h2 := bound ⟨2,by decide⟩
  have h3 := bound ⟨3,by decide⟩
  simp only [Source.AXPair.expected,Source.AXPush.expected,Source.AXPair.relocate,
    Option.map_some,Nat.reduceAdd] at h0 h1 h2 h3
  simpa only [Nat.add_assoc,Nat.reduceAdd] using
    drain_two_loop (offset+31) (offset+32) (offset+33) (offset+34) (offset+35)
      1 7 6 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega) (by omega) h0 h1 h2 h3 n xs hv ht

 theorem pair_drain_x (offset : Nat) (hb : offset+41<3947)
    (bound : Source.AXPair.Bound Source.exactSites offset)
    (n xs : V) (hv : ValidStore xs) (hx : registers xs 6=n) :
    ∃ cs, Trace (3*n+1) cs (stateCode ((offset+38:Nat):V) xs)
      (stateCode ((offset+41:Nat):V) (drainEnd 6 1 n xs)) := by
  have h0 := bound ⟨6,by decide⟩
  have h1 := bound ⟨7,by decide⟩
  have h2 := bound ⟨8,by decide⟩
  simp only [Source.AXPair.expected,Source.AXPush.expected,Source.AXPair.relocate,
    Option.map_some,Nat.reduceAdd] at h0 h1 h2
  simpa only [Nat.add_assoc,Nat.reduceAdd] using
    drain_loop (offset+37) (offset+38) (offset+39) (offset+40)
      6 1 (by decide) (by omega) (by omega) (by omega) h0 h1 h2 n xs hv hx
#print axioms pair_drain_t
#print axioms pair_drain_x
end M6.Arithmetic.PA.InternalTrace.CodedSource


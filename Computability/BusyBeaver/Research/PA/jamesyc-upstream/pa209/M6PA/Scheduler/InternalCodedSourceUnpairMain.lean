module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceUnpairIteration
public import M6.Source.UnpairPartial
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem unpair_main (r x y : Fin 9) (base : Nat) (hrx : r≠x) (hry : r≠y) (hxy : x≠y)
    (hbound : base+7<3947) (hb : UnpairLoopBound r x y base)
    (n xs : V) (hv : ValidStore xs) :
    ∃ t cs,0<t ∧ Trace t cs (stateCode ((base+1:Nat):V) (unpairStore r x y xs n 0 0))
      (stateCode ((base+8+1:Nat):V) (unpairDecodedStore r x y xs 0 n)) := by
  obtain ⟨t,cs,hc⟩ := unpair_iteration r x y base hrx hry hxy hbound hb n xs 0 0 hv
  simp only [zero_add,add_zero,unpairDecodedStore,decodeLeft,decodeRight,decodeState_zero,
    pi₁_pair,pi₂_pair] at hc
  have hs := unpair_step0 r x y base hrx hry hxy hbound hb xs 0 (decodeLeft n) (decodeRight n) hv
  simp only [Nat.add_zero,ite_true] at hs
  have ht := trace_one (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs 0 n))
  rw [show stepValue (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs 0 n))=
    stateCode ((base+8+1:Nat):V) (unpairDecodedStore r x y xs 0 n) from hs] at ht
  obtain ⟨ds,hd⟩ := trace_compose hc ht
  exact ⟨t+1,ds,by simp,hd⟩

lemma unpairLoopBound_of_partial (base : Nat) (hb : Source.UnpairPartial.Bound Source.exactSites base) :
    UnpairLoopBound 2 6 7 base := by
  intro ⟨j,hj⟩
  have h := hb ⟨j,by omega⟩
  have he : Source.UnpairPartial.expected base j=unpairLoopInstruction 2 6 7 base j := by
    have hcases : j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7 := by omega
    rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  exact h.trans (congrArg some he)
theorem actual_unpair_main (n xs : V) (hv : ValidStore xs) :
    ∃ t cs,0<t ∧ Trace t cs (stateCode 3934 (unpairStore 2 6 7 xs n 0 0))
      (stateCode 3942 (unpairDecodedStore 2 6 7 xs 0 n)) := by
  exact unpair_main 2 6 7 3933 (by decide) (by decide) (by decide) (by decide)
    (unpairLoopBound_of_partial 3933 Source.UnpairPartial.original_bound) n xs hv
#print axioms unpair_main
#print axioms actual_unpair_main
end M6.Arithmetic.PA.InternalTrace.CodedSource


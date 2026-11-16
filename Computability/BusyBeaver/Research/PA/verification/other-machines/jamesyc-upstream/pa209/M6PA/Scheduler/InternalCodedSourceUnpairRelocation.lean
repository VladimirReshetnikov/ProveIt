module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceUnpairFull
public import M6.Source.UnpairRelocation
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
lemma unpair_rename_ne (p : Source.UnpairRelocation) {r s : Fin 9} (hrs : r≠s) : p.rename r≠p.rename s := by
  intro h
  have he := congrArg p.rename h
  simp only [p.involution] at he
  exact hrs he
lemma unpairLoopBound_of_relocation (p : Source.UnpairRelocation) (hb : p.Bound) :
    UnpairLoopBound (p.rename 2) (p.rename 6) (p.rename 7) p.base := by
  intro ⟨j,hj⟩
  have h := hb ⟨j,by omega⟩
  have hcases : j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact h
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem unpair_relocated (p : Source.UnpairRelocation) (hb : p.Bound) (hbound : p.base+13<3947)
    (n xs : V) (hv : ValidStore xs) :
    ∃ t cs,0<t ∧ Trace t cs
      (stateCode ((p.base+1:Nat):V) (unpairStore (p.rename 2) (p.rename 6) (p.rename 7) xs n 0 0))
      (stateCode ((p.exitPort+1:Nat):V) (unpairFullEnd (p.rename 2) (p.rename 6) (p.rename 7) (p.rename 5) xs n)) := by
  have hrx := unpair_rename_ne p (show (2:Fin 9)≠6 by decide)
  have hry := unpair_rename_ne p (show (2:Fin 9)≠7 by decide)
  have hxy := unpair_rename_ne p (show (6:Fin 9)≠7 by decide)
  have hxh := unpair_rename_ne p (show (6:Fin 9)≠5 by decide)
  obtain ⟨t,cs,ht,hc⟩ := unpair_partial (p.rename 2) (p.rename 6) (p.rename 7) p.base hrx hry hxy
    (by omega) (unpairLoopBound_of_relocation p hb) (hb ⟨8,by decide⟩) (hb ⟨9,by decide⟩) (hb ⟨10,by decide⟩) n xs hv
  obtain ⟨ds,hd⟩ := unpair_full_tail (p.rename 2) (p.rename 6) (p.rename 7) (p.rename 5) p.base
    (some p.exitPort) hrx hry hxy hxh hbound (hb ⟨11,by decide⟩) (hb ⟨12,by decide⟩) (hb ⟨13,by decide⟩) n xs hv
  obtain ⟨es,he⟩ := trace_compose hc hd
  exact ⟨_,es,lt_of_lt_of_le ht (by simp),he⟩
#print axioms unpairLoopBound_of_relocation
#print axioms unpair_relocated
end M6.Arithmetic.PA.InternalTrace.CodedSource


module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalAXMacroReaders
public import M6.Source.AXTypedPlan
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.ModelAX
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem bound_realizes {op : Op} {first last : Nat} (hb : Source.AXTyped.Bound op first last) :
    Realizes (V:=V) op first last := by
  cases hb with
  | push offset hr hb => exact push_realizes offset hr hb
  | cons offset hr hp hq hm => exact cons_realizes offset hr hp hq hm
  | copyA => exact copyA_realizes _ ‹_› ‹_›
  | copyD => exact copyD_realizes _ ‹_› ‹_›
  | copyH => exact copyH_realizes _ ‹_› ‹_›
  | incT => exact inc_realizes _ ‹_› ‹_›
  | readH => exact readH_realizes _ ‹_› ‹_›
  | readD => exact readD_realizes _ ‹_› ‹_›

/-- Structural composition over a fixed finite macro plan, consuming actual
all-model source trace witnesses; it does not reuse old Nat Realizes proofs. -/
theorem plan_sound {first last : Nat} {ops : List Op}
    (hp : Source.AXTyped.Plan first last ops) (s s' : Store V)
    (he : run ops s=some s') (bottom n : V) :
    ∃ k cs,CodedSource.Trace k cs (config first s bottom n) (config last s' bottom n) := by
  induction hp generalizing s with
  | nil pc =>
    simp only [run,Option.some.injEq] at he
    subst s'
    exact ⟨0,?[config pc s bottom n],CodedSource.trace_zero _⟩
  | @cons pc next last op ops hb hp ih =>
    cases hx : exec op s with
    | none => simp [run,hx] at he
    | some mid =>
      simp only [run,hx,Option.bind_some] at he
      obtain ⟨k,cs,_,hc⟩ := bound_realizes hb s mid hx bottom n
      obtain ⟨l,ds,hd⟩ := ih mid he
      obtain ⟨es,hall⟩ := CodedSource.trace_compose hc hd
      exact ⟨k+l,es,hall⟩
theorem plan_positive {first last : Nat} {ops : List Op}
    (hp : Source.AXTyped.Plan first last ops) (hne : ops≠[]) (s s' : Store V)
    (he : run ops s=some s') (bottom n : V) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs (config first s bottom n) (config last s' bottom n) := by
  cases hp with
  | nil => exact False.elim (hne rfl)
  | @cons pc next last op ops hb hp =>
    cases hx : exec op s with
    | none => simp [run,hx] at he
    | some mid =>
      simp only [run,hx,Option.bind_some] at he
      obtain ⟨k,cs,hk,hc⟩ := bound_realizes hb s mid hx bottom n
      obtain ⟨l,ds,hd⟩ := plan_sound hp mid s' he bottom n
      obtain ⟨es,hall⟩ := CodedSource.trace_compose hc hd
      exact ⟨k+l,es,lt_of_lt_of_le hk (by simp),hall⟩

#print axioms bound_realizes
#print axioms plan_sound
end M6.Arithmetic.PA.InternalTrace.ModelAX


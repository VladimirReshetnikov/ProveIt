module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalAXMacroReaders
public import PA196.Arithmetic.Scheduler.AXTyped
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

theorem bound_realizes {op : Op} {first last : Nat} (hb : PA196.Arithmetic.Scheduler.AXTyped.Bound op first last) :
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
    (hp : PA196.Arithmetic.Scheduler.AXTyped.Plan first last ops) (s s' : Store V)
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
    (hp : PA196.Arithmetic.Scheduler.AXTyped.Plan first last ops) (hne : ops≠[]) (s s' : Store V)
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
end PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX


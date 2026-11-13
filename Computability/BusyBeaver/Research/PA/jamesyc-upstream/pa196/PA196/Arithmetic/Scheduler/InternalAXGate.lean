module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalAXGateStores
public import PA196.Arithmetic.Scheduler.AXGateRows
public import PA196.Source.AXGateBinding
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open PA196.Arithmetic.Scheduler.AXGateRows
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

lemma gate_copy_a (s : Store V) (bottom n : V) :
    ∃ cs,CodedSource.Trace (4*s.a+1) cs (CodedSource.stateCode 3659 (workCode s bottom n 0 0))
      (CodedSource.stateCode 3663 (workCode {s with a:=0} bottom n s.a s.a)) := by
  obtain ⟨cs,hc⟩ := CodedSource.drain_two_loop 3658 3659 3660 3661 3662 3 7 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    row3769 row3770 row3771 row3772 s.a _ (work_valid s bottom n 0 0)
    (by rw [work_registers];rfl)
  exact ⟨cs,by simpa only [copy_a_store,Nat.reduceAdd,Nat.cast_ofNat] using hc⟩
lemma gate_y_to_x (s : Store V) (bottom n y : V) :
    ∃ cs,CodedSource.Trace (3*y+1) cs (CodedSource.stateCode 3675 (workCode s bottom n 0 y))
      (CodedSource.stateCode 3678 (workCode s bottom n y 0)) := by
  obtain ⟨cs,hc⟩ := CodedSource.drain_loop 3674 3675 3676 3677 7 6
    (by decide) (by decide) (by decide) (by decide)
    row3785 row3786 row3787 y _ (work_valid s bottom n 0 y)
    (by rw [work_registers];rfl)
  exact ⟨cs,by simpa only [y_to_x_store,Nat.reduceAdd,Nat.cast_ofNat] using hc⟩
lemma gate_d_to_h (s : Store V) (bottom n x : V) (hh : s.h=0) :
    ∃ cs,CodedSource.Trace (3*s.d+1) cs (CodedSource.stateCode 3678 (workCode s bottom n x 0))
      (CodedSource.stateCode 3681 (workCode {s with d:=0,h:=s.d} bottom n x 0)) := by
  obtain ⟨cs,hc⟩ := CodedSource.drain_loop 3677 3678 3679 3680 4 5
    (by decide) (by decide) (by decide) (by decide)
    row3788 row3789 row3790 s.d _ (work_valid s bottom n x 0)
    (by rw [work_registers];rfl)
  exact ⟨cs,by simpa only [d_to_h_store s bottom n x hh,Nat.reduceAdd,Nat.cast_ofNat] using hc⟩
lemma gate_comparison (base : Nat) (hrange : base+12<3812)
    (hb : Source.AXGateCompare.Bound PA196.Program.sites base) (s : Store V) (bottom n x y : V) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs
      (CodedSource.stateCode ((base+1:Nat):V) (workCode s bottom n x y))
      (CodedSource.stateCode ((base+13:Nat):V)
        (workCode {s with t:=if s.h=x then 0 else s.t,h:=0} bottom n 0 y)) := by
  obtain ⟨k,cs,hk,hc⟩ := AXGateModel.compare_trace base hrange hb _ (work_valid s bottom n x y)
  exact ⟨k,cs,hk,by simpa only [compare_store] using hc⟩

/-- All35 final gate rows, including model-valued cleanup loops. -/
theorem gate (s : Store V) (bottom n : V) :
    ∃ k cs,0<k ∧ CodedSource.Trace k cs (config 3658 s bottom n)
      (config 3799 {s with t:=if s.d=s.a ∨ s.h=s.a then 0 else s.t,a:=0,d:=0,h:=0} bottom n) := by
  obtain ⟨as,ha⟩ := gate_copy_a s bottom n
  obtain ⟨k,bs,hk,hb⟩ := gate_comparison 3662 (by decide) PA196.Source.AXGateCompare.bound3662 {s with a:=0} bottom n s.a s.a
  obtain ⟨cs,hc⟩ := gate_y_to_x {s with t:=if s.h=s.a then 0 else s.t,a:=0,h:=0} bottom n s.a
  obtain ⟨ds,hd⟩ := gate_d_to_h {s with t:=if s.h=s.a then 0 else s.t,a:=0,h:=0} bottom n s.a rfl
  obtain ⟨l,es,hl,he⟩ := gate_comparison 3680 (by decide) PA196.Source.AXGateCompare.bound3680
    {s with t:=if s.h=s.a then 0 else s.t,a:=0,d:=0,h:=s.d} bottom n s.a 0
  let out : Store V := {s with t:=if s.d=s.a then 0 else if s.h=s.a then 0 else s.t,a:=0,d:=0,h:=0}
  have hj : CodedSource.stepValue (CodedSource.stateCode 3693 (workCode out bottom n 0 0))=
      CodedSource.stateCode 3800 (workCode out bottom n 0 0) := by
    have hj0 := CodedSource.literal_step (V:=V) 3692 (by decide) _ row3803 (workCode out bottom n 0 0)
    simpa only [CodedSource.instructionValue,CodedSource.destinationCode,Nat.reduceAdd,Nat.cast_ofNat] using hj0
  have ht := CodedSource.trace_one (CodedSource.stateCode 3693 (workCode out bottom n 0 0))
  rw [hj] at ht
  obtain ⟨abs,hab⟩ := CodedSource.trace_compose ha hb
  obtain ⟨acs,hac⟩ := CodedSource.trace_compose hab hc
  obtain ⟨ads,had⟩ := CodedSource.trace_compose hac hd
  obtain ⟨aes,hae⟩ := CodedSource.trace_compose had he
  obtain ⟨fs,hf⟩ := CodedSource.trace_compose hae ht
  refine ⟨(4*s.a+1)+k+(3*s.a+1)+(3*s.d+1)+l+1,fs,by simp,?_⟩
  by_cases hd : s.d=s.a <;> by_cases hh : s.h=s.a <;>
    simpa only [config,work_zero,out,hd,hh,ite_true,ite_false,true_or,false_or,or_true,or_false,
      Nat.reduceAdd,Nat.cast_ofNat] using hf
#print axioms gate
end PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX


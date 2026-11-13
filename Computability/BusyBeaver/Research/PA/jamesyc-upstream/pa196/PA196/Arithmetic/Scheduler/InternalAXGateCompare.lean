module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceMPGuard
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCompareBindings
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.AXGateModel
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open CodedSource
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def compareEnd (xs : V) : V :=
  if registers xs 5=registers xs 6 then replace 1 (guardStore xs 0 0) 0 else guardStore xs 0 0
lemma compareEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (compareEnd xs) := by
  unfold compareEnd
  split
  · exact replace_valid _ _ (guardStore_valid xs 0 0 hv) 1
  · exact guardStore_valid xs 0 0 hv

theorem compare_trace (base : Nat) (hrange : base+12<3812)
    (hb : Source.AXGateCompare.Bound PA196.Program.sites base) (xs : V) (hv : ValidStore xs) :
    ∃ k cs,0<k ∧ Trace k cs (stateCode ((base+1:Nat):V) xs)
      (stateCode ((base+13:Nat):V) (compareEnd xs)) := by
  obtain ⟨k,cs,hk,hc⟩ := compare_loop base (base+10) (base+12) (by omega)
    (compareBound_of_AX base hb) (registers xs 5) (registers xs 6) xs hv
  rw [guardStore_current xs hv] at hc
  by_cases he : registers xs 5=registers xs 6
  · rw [if_pos he] at hc
    have h0 := hb ⟨10,by decide⟩
    have h1 := hb ⟨11,by decide⟩
    simp only [Source.AXGateCompare.expected] at h0 h1
    obtain ⟨ds,hd⟩ := erase_loop (base+10) (base+11) (base+12) 1 (by omega) (by omega)
      h0 h1 (registers (guardStore xs 0 0) 1) _ (guardStore_valid xs 0 0 hv) rfl
    obtain ⟨es,hall⟩ := trace_compose hc hd
    refine ⟨k+(2*registers (guardStore xs 0 0) 1+1),es,lt_of_lt_of_le hk (by simp),?_⟩
    simpa only [compareEnd,if_pos he,Nat.add_assoc,Nat.reduceAdd,show (1:Fin 9).val=1 from rfl] using hall
  · rw [if_neg he] at hc
    refine ⟨k,cs,hk,?_⟩
    simpa only [compareEnd,if_neg he,Nat.add_assoc,Nat.reduceAdd] using hc
#print axioms compare_trace
end PA196.Arithmetic.Machine.PA.InternalTrace.AXGateModel


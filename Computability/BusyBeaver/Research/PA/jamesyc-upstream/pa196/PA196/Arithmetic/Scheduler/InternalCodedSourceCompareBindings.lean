module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCompare
public import M6.Source.AXGateCompareSteps
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
theorem mp_compare_bound : CompareBound 3763 3773 3799 := by
  unfold CompareBound
  simp only [Program.resolve_tree]
  decide +kernel
lemma compareBound_of_AX (base : Nat) (hb : Source.AXGateCompare.Bound PA196.Program.sites base) :
    CompareBound base (base+10) (base+12) := by
  intro ⟨j,hj⟩
  have h := hb ⟨j,by omega⟩
  have hcases : j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8∨j=9 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact h
#print axioms mp_compare_bound
#print axioms compareBound_of_AX
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource


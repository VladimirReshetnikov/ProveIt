module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCompareClear
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem compare_cleanup (base same diff : Nat) (hbound : base+9<3947) (hb : CompareBound base same diff)
    (xs h x : V) (hv : ValidStore xs) :
    ∃cs,Trace ((2*h+1)+(3*x+2)) cs (stateCode ((base+5+1:Nat):V) (guardStore xs h x))
      (stateCode ((diff+1:Nat):V) (guardStore xs 0 0)) := by
  have clearH : ∃cs,Trace (2*h+1) cs (stateCode ((base+5+1:Nat):V) (guardStore xs h x))
      (stateCode ((base+7+1:Nat):V) (guardStore xs 0 x)) := by
    have b5 : Source.resolveAt Source.exactSites (base+5)=some (.dec 5 (some (base+7)) (some (base+6))) := by
      simpa only [compareInstruction] using hb ⟨5,by decide⟩
    have b6 : Source.resolveAt Source.exactSites (base+6)=some (.jump (some (base+5))) := by
      simpa only [compareInstruction] using hb ⟨6,by decide⟩
    have hwh : replace (5:Fin 9).val (guardStore xs h x) 0=guardStore xs 0 x := guard_write_H xs h x 0
    have hc := erase_loop (base+5) (base+6) (base+7) 5 (by omega) (by omega)
      b5 b6 h (guardStore xs h x)
      (guardStore_valid xs h x hv) (guard_read_H xs h x hv)
    simpa only [hwh] using hc
  obtain ⟨cs,hc⟩ := clearH
  obtain ⟨ds,hd⟩ := compare_clear_X base same diff hbound hb x xs hv
  exact trace_compose hc hd
#print axioms compare_cleanup
end M6.Arithmetic.PA.InternalTrace.CodedSource


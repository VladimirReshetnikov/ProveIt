module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceConsStores
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- Literal 27-row formula-constructor prefix, shared by actual AX and MP. -/
theorem cons_block (offset : Nat) (hbound : offset+47<3947)
    (hpop : Source.UnpairPartial.Bound Source.exactSites (offset+20))
    (hpair : Source.AXPair.Bound Source.exactSites offset)
    (hfour : Source.AXTimes4.Bound Source.exactSites (offset+41))
    (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode ((offset+21:Nat):V) xs)
      (stateCode ((offset+48:Nat):V) (consEnd xs)) := by
  obtain ⟨a,acs,ha,hA⟩ := unpair_partial_store (offset+20) (by omega) hpop xs hv hx hy
  have hA' : Trace a acs (stateCode ((offset+21:Nat):V) xs)
      (stateCode ((offset+32:Nat):V) (consAfterPop xs)) := by
    simpa only [Nat.add_assoc,consAfterPop] using hA
  have hpy : registers (consAfterPop xs) 7=0 := by
    rw [consAfterPop_registers xs hv]
    simp [PhysicalRegisters.write]
  obtain ⟨b,bcs,hb,hB⟩ := pair offset (by omega) hpair (consAfterPop xs) (consAfterPop_valid xs hv) hpy
  have hB' : Trace b bcs (stateCode ((offset+32:Nat):V) (consAfterPop xs))
      (stateCode ((offset+42:Nat):V) (consAfterPair xs)) := hB
  obtain ⟨cs,hC⟩ := times4_loop (offset+41) (by omega) hfour (registers (consAfterPair xs) 7)
    (consAfterPair xs) (consAfterPair_valid xs hv) rfl
  have hC' : Trace (6*registers (consAfterPair xs) 7+1) cs
      (stateCode ((offset+42:Nat):V) (consAfterPair xs))
      (stateCode ((offset+48:Nat):V) (consEnd xs)) := by
    simpa only [Nat.add_assoc,consEnd] using hC
  obtain ⟨ds,hd⟩ := trace_compose hA' hB'
  obtain ⟨es,he⟩ := trace_compose hd hC'
  exact ⟨_,es,lt_of_lt_of_le ha (by simp),he⟩
#print axioms cons_block
end M6.Arithmetic.PA.InternalTrace.CodedSource


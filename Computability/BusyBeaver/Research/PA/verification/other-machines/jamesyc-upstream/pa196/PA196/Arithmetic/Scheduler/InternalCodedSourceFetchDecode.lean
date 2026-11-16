module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceUnpairApply
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal

def fetchRelocation : Source.UnpairRelocation :=
  ⟨Source.FetchUnpair.rename,Source.FetchUnpair.rename_involution,34,48⟩

theorem fetchRelocation_bound : PA196.Source.Readers.Bound Program.sites fetchRelocation := by
  unfold PA196.Source.Readers.Bound
  simp only [Program.resolve_tree]
  decide +kernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def fetchDecodeEnd (xs : V) : V := unpairFullEnd 8 6 7 3 xs (registers xs 8)

theorem fetch_decode (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 35 xs) (stateCode 49 (fetchDecodeEnd xs)) := by
  exact unpair_relocated_store fetchRelocation fetchRelocation_bound (by decide) xs hv hx hy

theorem fetchDecodeEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (fetchDecodeEnd xs) :=
  unpairFullEnd_valid 8 6 7 3 xs _ hv

theorem fetchDecodeEnd_effect (xs : V) (hv : ValidStore xs) :
    registers (fetchDecodeEnd xs)=
      PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
        (registers xs) 8 (decodeRight (registers xs 8))) 6 0) 7 0) 3 (registers xs 3+decodeLeft (registers xs 8)) := by
  exact unpairFullEnd_effect 8 6 7 3 xs _ hv (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
#print axioms fetchRelocation_bound
#print axioms fetch_decode
#print axioms fetchDecodeEnd_effect
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource


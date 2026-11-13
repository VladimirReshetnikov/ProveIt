module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceUnpairApply
public import M6.Source.FetchUnpairBinding
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal

def fetchRelocation : Source.UnpairRelocation :=
  ⟨Source.FetchUnpair.rename,Source.FetchUnpair.rename_involution,9,23⟩

theorem fetchRelocation_bound : fetchRelocation.Bound := by
  intro j
  have h := Source.fetch_unpair_resolved_at j
  have he : Source.fetchUnpairExpected[j.val]=fetchRelocation.instruction Source.unpairExpected[j.val] :=
    (by decide : ∀ j : Fin 14, Source.fetchUnpairExpected[j.val]=fetchRelocation.instruction Source.unpairExpected[j.val]) j
  exact h.trans (congrArg some he)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def fetchDecodeEnd (xs : V) : V := unpairFullEnd 8 6 7 3 xs (registers xs 8)

theorem fetch_decode (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 10 xs) (stateCode 24 (fetchDecodeEnd xs)) := by
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
end M6.Arithmetic.PA.InternalTrace.CodedSource


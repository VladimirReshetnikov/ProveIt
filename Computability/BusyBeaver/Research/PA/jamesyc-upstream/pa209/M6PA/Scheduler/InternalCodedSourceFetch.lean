module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceFetchPrefix
public import M6PA.Scheduler.InternalCodedSourceFetchDecode
public import M6PA.Scheduler.InternalCodedSourceCommandProjection
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def fetchPositiveEnd (xs l : V) : V := fetchDecodeEnd (replace 8 xs l)
noncomputable def fetchNextEnd (xs : V) : V := fetchDecodeEnd (fetchFreshEnd xs)

theorem fetch_positive_complete (xs l : V) (hv : ValidStore xs) (hl : registers xs 8=l+1)
    (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 1 xs) (stateCode 24 (fetchPositiveEnd xs l)) := by
  have hv' := replace_valid xs l hv (8:Fin 9)
  have ex : registers (replace 8 xs l) 6=0 := (registers_replace_other xs l hv 8 6 (by decide)).trans hx
  have ey : registers (replace 8 xs l) 7=0 := (registers_replace_other xs l hv 8 7 (by decide)).trans hy
  obtain ⟨ps,hp⟩ := fetch_positive xs l hv hl
  obtain ⟨n,cs,hn,hc⟩ := fetch_decode (replace 8 xs l) hv' ex ey
  obtain ⟨ds,hd⟩ := trace_compose hp hc
  exact ⟨2+n,ds,lt_of_lt_of_le hn (by simp),hd⟩

theorem fetch_next_complete (xs : V) (hv : ValidStore xs) (hl : registers xs 8=0)
    (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 1 xs) (stateCode 24 (fetchNextEnd xs)) := by
  have ee := fetchFreshEnd_effect xs hv hl hx
  have ex : registers (fetchFreshEnd xs) 6=0 := by rw [ee]; simp [PhysicalRegisters.write,hx]
  have ey : registers (fetchFreshEnd xs) 7=0 := by rw [ee]; simp [PhysicalRegisters.write,hy]
  obtain ⟨m,ps,hm,hp⟩ := fetch_fresh xs hv hl hx
  obtain ⟨n,cs,hn,hc⟩ := fetch_decode (fetchFreshEnd xs) (fetchFreshEnd_valid xs hv) ex ey
  obtain ⟨ds,hd⟩ := trace_compose hp hc
  exact ⟨m+n,ds,lt_of_lt_of_le hm (by simp),hd⟩

theorem fetchPositiveEnd_effect (xs l : V) (hv : ValidStore xs) :
    registers (fetchPositiveEnd xs l)=PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 8 (decodeRight l))
        6 0) 7 0) 3 (registers xs 3+decodeLeft l) := by
  have ee : registers (replace 8 xs l)=PhysicalRegisters.write (registers xs) 8 l := registers_replace xs l hv 8
  have hvp : ValidStore (replace 8 xs l) := replace_valid xs l hv 8
  rw [fetchPositiveEnd,fetchDecodeEnd_effect (replace 8 xs l) hvp,ee]
  funext r
  by_cases h3:r=3 <;> by_cases h6:r=6 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
    simp_all [PhysicalRegisters.write]

theorem fetchNextEnd_effect (xs : V) (hv : ValidStore xs) (hl : registers xs 8=0) (hx : registers xs 6=0) :
    registers (fetchNextEnd xs)=PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 0 (registers xs 0+1))
        8 (decodeRight (registers xs 0))) 6 0) 7 0) 3 (registers xs 3+decodeLeft (registers xs 0)) := by
  rw [fetchNextEnd,fetchDecodeEnd_effect _ (fetchFreshEnd_valid xs hv),fetchFreshEnd_effect xs hv hl hx]
  funext r
  by_cases h0:r=0 <;> by_cases h3:r=3 <;> by_cases h6:r=6 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
    simp_all [PhysicalRegisters.write]

theorem fetchPositiveEnd_commandState (xs l : V) (hv : ValidStore xs) :
    commandState (fetchPositiveEnd xs l)=commandState xs := by
  simp [commandState,fetchPositiveEnd_effect xs l hv,PhysicalRegisters.write]
theorem fetchNextEnd_commandState (xs : V) (hv : ValidStore xs) (hl : registers xs 8=0) (hx : registers xs 6=0) :
    commandState (fetchNextEnd xs)=commandState xs := by
  simp [commandState,fetchNextEnd_effect xs hv hl hx,PhysicalRegisters.write]
#print axioms fetch_positive_complete
#print axioms fetch_next_complete
#print axioms fetchPositiveEnd_effect
#print axioms fetchNextEnd_effect
end M6.Arithmetic.PA.InternalTrace.CodedSource


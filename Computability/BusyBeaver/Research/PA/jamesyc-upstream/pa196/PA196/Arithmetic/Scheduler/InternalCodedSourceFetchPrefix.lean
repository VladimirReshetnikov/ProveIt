module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDrainJumpInc
public import PA196.Arithmetic.Scheduler.InternalCodedSourceS36DrainPrefix
public import PA196.Source.FetchPrefixBinding
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

noncomputable def fetchCopyEnd (xs : V) : V := drainTwoEnd 0 8 6 (registers xs 0) xs
noncomputable def fetchIncEnd (xs : V) : V := replace 0 (fetchCopyEnd xs) 1
noncomputable def fetchFreshEnd (xs : V) : V := drainEnd 6 0 (registers xs 0) (fetchIncEnd xs)

theorem fetch_copy (xs : V) (hv : ValidStore xs) :
    ∃cs, Trace (4*registers xs 0+1) cs (stateCode 28 xs) (stateCode 32 (fetchCopyEnd xs)) := by
  apply drain_two_loop 27 28 29 30 31 0 8 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  · exact PA196.Source.fetch_prefix_at ⟨2,by decide⟩
  · exact PA196.Source.fetch_prefix_at ⟨3,by decide⟩
  · exact PA196.Source.fetch_prefix_at ⟨4,by decide⟩
  · exact PA196.Source.fetch_prefix_at ⟨5,by decide⟩
  · exact hv
  · rfl

theorem fetch_restore (n xs : V) (hv : ValidStore xs) (hx : registers xs 6=n) :
    ∃cs, Trace (3*n+1) cs (stateCode 33 xs) (stateCode 35 (drainEnd 6 0 n xs)) := by
  apply drain_loop_jump_inc 32 31 33 34 6 0 (by decide) (by decide) (by decide) (by decide)
  · exact PA196.Source.fetch_prefix_at ⟨7,by decide⟩
  · exact PA196.Source.fetch_prefix_at ⟨6,by decide⟩
  · exact PA196.Source.fetch_prefix_at ⟨8,by decide⟩
  · exact hv
  · exact hx

theorem fetchCopyEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (fetchCopyEnd xs) :=
  drainTwoEnd_valid 0 8 6 _ xs hv

theorem fetchIncEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (fetchIncEnd xs) :=
  replace_valid _ _ (fetchCopyEnd_valid xs hv) 0

theorem fetchFreshEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (fetchFreshEnd xs) :=
  drainEnd_valid 6 0 _ _ (fetchIncEnd_valid xs hv)

theorem fetch_fresh (xs : V) (hv : ValidStore xs) (hl : registers xs 8=0) (hx : registers xs 6=0) :
    ∃n cs, 0<n ∧ Trace n cs (stateCode 26 xs) (stateCode 35 (fetchFreshEnd xs)) := by
  have ecopy := drainTwoEnd_registers 0 8 6 (registers xs 0) xs hv
  change registers (fetchCopyEnd xs)=_ at ecopy
  have hn : registers (fetchCopyEnd xs) 0=0 := by rw [ecopy]; simp [PhysicalRegisters.write]
  have hX : registers (fetchIncEnd xs) 6=registers xs 0 := by
    have er : registers (fetchIncEnd xs)=PhysicalRegisters.write (registers (fetchCopyEnd xs)) 0 1 := registers_replace _ 1 (fetchCopyEnd_valid xs hv) 0
    rw [er,ecopy]
    simp [PhysicalRegisters.write,hx]
  have first : stepValue (stateCode 26 xs)=stateCode 28 xs := by
    have h := literal_step 25 (by decide) _ (PA196.Source.fetch_prefix_at ⟨0,by decide⟩) xs
    simpa [PA196.Source.fetchPrefixExpected,instructionValue,destinationCode,hl] using h
  have inc : stepValue (stateCode 32 (fetchCopyEnd xs))=stateCode 33 (fetchIncEnd xs) := by
    have h := literal_step 31 (by decide) _ (PA196.Source.fetch_prefix_at ⟨6,by decide⟩) (fetchCopyEnd xs)
    simpa [PA196.Source.fetchPrefixExpected,instructionValue,destinationCode,fetchIncEnd,hn] using h
  obtain ⟨as,ha⟩ := fetch_copy xs hv
  obtain ⟨bs,hb⟩ := fetch_restore (registers xs 0) (fetchIncEnd xs) (fetchIncEnd_valid xs hv) hX
  obtain ⟨cs,hc⟩ := trace_prepend _ inc hb
  obtain ⟨ds,hd⟩ := trace_compose ha hc
  obtain ⟨es,he⟩ := trace_prepend _ first hd
  exact ⟨(4*registers xs 0+1)+((3*registers xs 0+1)+1)+1,es,by simp,he⟩

theorem fetchFreshEnd_effect (xs : V) (hv : ValidStore xs) (hl : registers xs 8=0) (hx : registers xs 6=0) :
    registers (fetchFreshEnd xs)=PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 0 (registers xs 0+1)) 8 (registers xs 0) := by
  rw [fetchFreshEnd,drainEnd_registers 6 0 _ _ (fetchIncEnd_valid xs hv)]
  have er : registers (fetchIncEnd xs)=PhysicalRegisters.write (registers (fetchCopyEnd xs)) 0 1 := registers_replace _ 1 (fetchCopyEnd_valid xs hv) 0
  rw [er]
  rw [fetchCopyEnd,drainTwoEnd_registers 0 8 6 _ xs hv]
  funext r
  by_cases h0 : r=0 <;> by_cases h6 : r=6 <;> by_cases h8 : r=8 <;>
    simp_all [PhysicalRegisters.write,add_comm]

 theorem fetch_positive (xs l : V) (hv : ValidStore xs) (hl : registers xs 8=l+1) :
    ∃cs, Trace 2 cs (stateCode 26 xs) (stateCode 35 (replace 8 xs l)) := by
  have first : stepValue (stateCode 26 xs)=stateCode 27 (replace 8 xs l) := by
    have h := literal_step 25 (by decide) _ (PA196.Source.fetch_prefix_at ⟨0,by decide⟩) xs
    simpa [PA196.Source.fetchPrefixExpected,instructionValue,destinationCode,hl] using h
  have jump : stepValue (stateCode 27 (replace 8 xs l))=stateCode 35 (replace 8 xs l) := by
    have h := literal_step 26 (by decide) _ (PA196.Source.fetch_prefix_at ⟨1,by decide⟩) (replace 8 xs l)
    simpa [PA196.Source.fetchPrefixExpected,instructionValue,destinationCode] using h
  have hj : Trace 1 ?[stateCode 27 (replace 8 xs l),stateCode 35 (replace 8 xs l)]
      (stateCode 27 (replace 8 xs l)) (stateCode 35 (replace 8 xs l)) := by
    simpa only [jump] using trace_one (stateCode 27 (replace 8 xs l))
  simpa only [one_add_one_eq_two] using trace_prepend _ first hj
#print axioms fetch_fresh
#print axioms fetchFreshEnd_effect
#print axioms fetch_positive
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource


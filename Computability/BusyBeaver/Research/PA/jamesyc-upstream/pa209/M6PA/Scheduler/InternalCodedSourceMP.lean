module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceMPFinish
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def mpEnd (xs : V) : V :=
  if mpConstructor xs=registers xs 5 then mpSuccessEnd (mpAfterGuard xs) else mpAfterGuard xs
/-- All107 actual MP leaves, with arbitrary model-valued fields and caches. -/
theorem actual_mp (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃n cs,0<n ∧ Trace n cs (stateCode 3805 xs) (stateCode 1 (mpEnd xs)) := by
  obtain ⟨np,ps,hp,hP⟩ := actual_mp_prelude xs hv hx hy
  have kx : registers (mpAfterCons xs) 6=0 := by rw [mpAfterCons_registers xs hv]; simp [PhysicalRegisters.write]
  have kt : registers (mpAfterCons xs) 1=mpConstructor xs := by rw [mpAfterCons_registers xs hv]; simp [PhysicalRegisters.write]
  have kh : registers (mpAfterCons xs) 5=registers xs 5 := by rw [mpAfterCons_registers xs hv]; simp [PhysicalRegisters.write]
  obtain ⟨ng,gs,hg,hG⟩ := actual_mp_guard (mpAfterCons xs) (mpAfterCons_valid xs hv) kx
  rw [kt,kh] at hG
  obtain ⟨cs,hC⟩ := trace_compose hP hG
  by_cases heq : mpConstructor xs=registers xs 5
  · simp only [heq,ite_true] at hC
    have gx : registers (mpAfterGuard xs) 6=0 := by rw [mpAfterGuard_registers xs hv]; simp [PhysicalRegisters.write]
    have gy : registers (mpAfterGuard xs) 7=0 := by rw [mpAfterGuard_registers xs hv]; simp [PhysicalRegisters.write]
    obtain ⟨ns,ss,hs,hS⟩ := actual_mp_success (mpAfterGuard xs) (mpAfterGuard_valid xs hv) gx gy
    obtain ⟨ds,hd⟩ := trace_compose hC hS
    exact ⟨np+ng+ns,ds,lt_of_lt_of_le hp (by simp [add_assoc]),by simpa only [mpEnd,heq,ite_true] using hd⟩
  · simp only [heq,ite_false] at hC
    obtain ⟨ds,hd⟩ := trace_compose hC (mp_return_trace (mpAfterGuard xs))
    exact ⟨np+ng+1,ds,by simp,by simpa only [mpEnd,heq,ite_false] using hd⟩
theorem mpEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (mpEnd xs) := by
  unfold mpEnd
  split
  · exact mpSuccessEnd_valid (mpAfterGuard xs) (mpAfterGuard_valid xs hv)
  · exact mpAfterGuard_valid xs hv
theorem mpEnd_effect (xs : V) (hv : ValidStore xs) :
    registers (mpEnd xs)=PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (registers xs)
        1 (if mpConstructor xs=registers xs 5 then mpOffset xs else 0))
        2 (if mpConstructor xs=registers xs 5 then pairValue 0 (registers xs 2) else registers xs 2))
        4 (mpOffset xs)) 5 0) 8 (decodeRight (registers xs 8))) 6 0) 7 0 := by
  have gt : registers (mpAfterGuard xs) 1=0 := by rw [mpAfterGuard_registers xs hv]; simp [PhysicalRegisters.write]
  have gx : registers (mpAfterGuard xs) 6=0 := by rw [mpAfterGuard_registers xs hv]; simp [PhysicalRegisters.write]
  unfold mpEnd
  split
  · rw [mpSuccessEnd_registers _ (mpAfterGuard_valid xs hv) gt gx,mpAfterGuard_registers xs hv]
    funext j
    by_cases h1:j=1 <;> by_cases h2:j=2 <;> by_cases h4:j=4 <;> by_cases h5:j=5 <;> by_cases h6:j=6 <;> by_cases h7:j=7 <;> by_cases h8:j=8 <;>
      simp_all [PhysicalRegisters.write]
  · rw [mpAfterGuard_registers xs hv]
    funext j
    by_cases h1:j=1 <;> by_cases h2:j=2 <;> by_cases h4:j=4 <;> by_cases h5:j=5 <;> by_cases h6:j=6 <;> by_cases h7:j=7 <;> by_cases h8:j=8 <;>
      simp_all [PhysicalRegisters.write]
#print axioms actual_mp
#print axioms mpEnd_effect
end M6.Arithmetic.PA.InternalTrace.CodedSource


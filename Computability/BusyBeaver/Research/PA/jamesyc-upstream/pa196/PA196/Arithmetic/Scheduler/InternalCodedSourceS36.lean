module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceUnpairFull
public import PA196.Arithmetic.Scheduler.InternalCodedSourceS36Guard
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
lemma guardStore_registers (xs h x : V) (hv : ValidStore xs) :
    registers (guardStore xs h x)=PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 5 h) 6 x := by
  exact (registers_replace (replace 5 xs h) x (replace_valid xs h hv (5:Fin 9)) (6:Fin 9)).trans
    (congrArg (fun f=>PhysicalRegisters.write f 6 x) (registers_replace xs h hv (5:Fin 9)))
noncomputable def s36GuardEnd (xs : V) : V := guardStore (s36DrainFinal xs) 0 0
lemma s36GuardEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (s36GuardEnd xs) := by
  exact guardStore_valid _ 0 0 (drainEnd_valid 6 5 _ _ (drainTwoEnd_valid 5 1 6 _ _ (drainEnd_valid 1 6 _ xs hv)))
lemma s36GuardEnd_effect (xs : V) (hv : ValidStore xs) :
    registers (s36GuardEnd xs)=PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (registers xs) 1 (registers xs 5)) 5 0) 6 0 := by
  unfold s36GuardEnd
  have hvf : ValidStore (s36DrainFinal xs) := drainEnd_valid 6 5 _ _ (drainTwoEnd_valid 5 1 6 _ _ (drainEnd_valid 1 6 _ xs hv))
  rw [guardStore_registers _ 0 0 hvf,s36_drain_effect xs hv]
  funext j
  by_cases h1:j=1 <;> by_cases h5:j=5 <;> by_cases h6:j=6 <;> simp_all [PhysicalRegisters.write]
lemma unpairStore_current (r x y : Fin 9) (xs : V) (hv : ValidStore xs)
    (hx : registers xs x=0) (hy : registers xs y=0) :
    unpairStore r x y xs (registers xs r) 0 0=xs := by
  unfold unpairStore
  rw [replace_current r xs hv]
  have ex : replace x.val xs 0=xs := by simpa only [hx] using replace_current x xs hv
  have ey : replace y.val xs 0=xs := by simpa only [hy] using replace_current y xs hv
  rw [ex,ey]
noncomputable def s36End (xs : V) : V := unpairFullEnd 2 6 7 5 (s36GuardEnd xs) (registers xs 2)

/-- The complete shift block, including the additional jump, for arbitrary
PA-model register values. A normal return is coded PC26. -/
theorem actual_s36 (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃ n cs,0<n ∧ Trace n cs (stateCode 3801 xs)
      (if registers xs 1+registers xs 5=1 then stateCode 0 (s36GuardEnd xs) else stateCode 26 (s36End xs)) := by
  obtain ⟨n,cs,hn,hc⟩ := actual_s36_guard xs hv
  simp only [hx,zero_add] at hc
  by_cases hh : registers xs 1+registers xs 5=1
  · exact ⟨n,cs,hn,by simpa only [hh,ite_true,s36GuardEnd] using hc⟩
  · have hg : ValidStore (s36GuardEnd xs) := s36GuardEnd_valid xs hv
    have gx : registers (s36GuardEnd xs) 6=0 := by rw [s36GuardEnd_effect xs hv]; simp [PhysicalRegisters.write]
    have gy : registers (s36GuardEnd xs) 7=0 := by rw [s36GuardEnd_effect xs hv]; simp [PhysicalRegisters.write,hy]
    have gw : registers (s36GuardEnd xs) 2=registers xs 2 := by rw [s36GuardEnd_effect xs hv]; simp [PhysicalRegisters.write]
    have hu : unpairStore 2 6 7 (s36GuardEnd xs) (registers xs 2) 0 0=s36GuardEnd xs := by
      rw [←gw]
      exact unpairStore_current 2 6 7 _ hg gx gy
    obtain ⟨m,ds,hm,hd⟩ := actual_unpair_full (registers xs 2) (s36GuardEnd xs) hg
    rw [hu] at hd
    have hc' : Trace n cs (stateCode 3801 xs) (stateCode 12 (s36GuardEnd xs)) := by
      simpa only [hh,ite_false,s36GuardEnd] using hc
    obtain ⟨es,he⟩ := trace_compose hc' hd
    exact ⟨n+m,es,lt_of_lt_of_le hn (by simp),by simpa only [hh,ite_false,s36End] using he⟩
theorem s36End_effect (xs : V) (hv : ValidStore xs) :
    registers (s36End xs)=PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 (registers xs 5))
        2 (decodeRight (registers xs 2))) 5 (decodeLeft (registers xs 2))) 6 0) 7 0 := by
  unfold s36End
  rw [unpairFullEnd_effect 2 6 7 5 _ _ (s36GuardEnd_valid xs hv) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide),s36GuardEnd_effect xs hv]
  funext j
  by_cases h1:j=1 <;> by_cases h2:j=2 <;> by_cases h5:j=5 <;> by_cases h6:j=6 <;> by_cases h7:j=7 <;>
    simp_all [PhysicalRegisters.write]
#print axioms actual_s36
#print axioms s36End_effect
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource


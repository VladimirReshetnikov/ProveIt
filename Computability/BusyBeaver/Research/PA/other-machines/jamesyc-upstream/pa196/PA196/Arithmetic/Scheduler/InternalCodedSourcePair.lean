module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourcePairLoop
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

noncomputable def pairEnd (xs : V) : V :=
  replace 7 (replace 6 (replace 1 xs 0) 0)
    (SourceCantorInternal.pairValue (registers xs 6) (registers xs 1))
private lemma read6 (xs a : V) (hv : ValidStore xs) :
    registers (replace 6 xs a)=PhysicalRegisters.write (registers xs) 6 a := registers_replace xs a hv 6
private lemma read7 (xs a : V) (hv : ValidStore xs) :
    registers (replace 7 xs a)=PhysicalRegisters.write (registers xs) 7 a := registers_replace xs a hv 7
private lemma read1 (xs a : V) (hv : ValidStore xs) :
    registers (replace 1 xs a)=PhysicalRegisters.write (registers xs) 1 a := registers_replace xs a hv 1
private lemma drain_registers (xs : V) (hv : ValidStore xs) (hy : registers xs 7=0) :
    registers (drainTwoEnd 1 7 6 (registers xs 1) xs)=
      PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 0)
        7 (registers xs 1)) 6 (registers xs 6+registers xs 1) := by
  unfold drainTwoEnd drainEnd
  rw [registers_replace _ _ (replace_valid _ _ (replace_valid _ _ hv 1) 7) 6,
    registers_replace _ _ (replace_valid _ _ hv 1) 7,registers_replace _ _ hv 1,hy,zero_add]
private lemma end_composition (xs : V) (hv : ValidStore xs) (hy : registers xs 7=0) :
    pairLoopEnd (registers xs 6+registers xs 1) (drainTwoEnd 1 7 6 (registers xs 1) xs)=pairEnd xs := by
  have hd := drainTwoEnd_valid 1 7 6 (registers xs 1) xs hv
  apply registers_ext (ys := pairEnd xs) (pairLoopEnd_valid _ _ hd)
    (replace_valid _ _ (replace_valid _ _ (replace_valid _ _ hv 1) 6) 7)
  unfold pairLoopEnd pairEnd
  rw [read7 (replace 6 (drainTwoEnd 1 7 6 (registers xs 1) xs) 0) _ (replace_valid _ _ hd 6),read6 _ _ hd,
    read7 (replace 6 (replace 1 xs 0) 0) _ (replace_valid _ _ (replace_valid _ _ hv 1) 6),
    read6 (replace 1 xs 0) _ (replace_valid _ _ hv 1),read1 _ _ hv,drain_registers xs hv hy]
  funext r
  by_cases h1 : r=1 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
    simp_all [PhysicalRegisters.write,SourceCantorInternal.pairValue,add_comm]

/-- Exact ten-row pair core for arbitrary model-valued input and full store. -/
theorem pair (offset : Nat) (hb : offset+41<3812)
    (bound : Source.AXPair.Bound PA196.Program.sites offset)
    (xs : V) (hv : ValidStore xs) (hy : registers xs 7=0) :
    ∃ k cs, 0<k ∧ Trace k cs (stateCode ((offset+32:Nat):V) xs)
      (stateCode ((offset+42:Nat):V) (pairEnd xs)) := by
  let ys := drainTwoEnd 1 7 6 (registers xs 1) xs
  have hyv : ValidStore ys := drainTwoEnd_valid 1 7 6 _ xs hv
  have hyt : registers ys 1=0 := by rw [drain_registers xs hv hy];simp [PhysicalRegisters.write]
  have hyx : registers ys 6=registers xs 6+registers xs 1 := by
    rw [drain_registers xs hv hy];simp [PhysicalRegisters.write]
  obtain ⟨cs,hc⟩ := pair_drain_t offset hb bound (registers xs 1) xs hv rfl
  obtain ⟨k,ds,hk,hd⟩ := pair_loop offset hb bound _ ys hyv hyt hyx
  rw [show pairLoopEnd (registers xs 6+registers xs 1) ys=pairEnd xs from end_composition xs hv hy] at hd
  obtain ⟨es,he⟩ := trace_compose hc hd
  refine ⟨_,es,?_,he⟩
  have hp : 0 < 4*registers xs 1+1 := by simp
  exact lt_of_lt_of_le hp (by simp)
#print axioms pair
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource


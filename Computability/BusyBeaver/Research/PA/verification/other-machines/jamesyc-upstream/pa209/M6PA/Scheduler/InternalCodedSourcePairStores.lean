module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourcePairRows
public import M6PA.Scheduler.InternalCodedSourceS36DrainPrefix
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

private lemma readReplace1 (xs a : V) (hv : ValidStore xs) :
    registers (replace 1 xs a)=PhysicalRegisters.write (registers xs) 1 a :=
  registers_replace xs a hv 1

private lemma readReplace6 (xs a : V) (hv : ValidStore xs) :
    registers (replace 6 xs a)=PhysicalRegisters.write (registers xs) 6 a :=
  registers_replace xs a hv 6

private lemma readReplace7 (xs a : V) (hv : ValidStore xs) :
    registers (replace 7 xs a)=PhysicalRegisters.write (registers xs) 7 a :=
  registers_replace xs a hv 7

lemma pairLoopEnd_valid (n xs : V) (hv : ValidStore xs) :
    ValidStore (pairLoopEnd n xs) :=
  replace_valid _ _ (replace_valid _ _ hv 6) 7

noncomputable def pairAfterTwo (n xs : V) : V :=
  replace 7 (replace 6 xs n) (registers xs 7+1)
noncomputable def pairAfterDrain (n xs : V) : V := drainEnd 6 1 n (pairAfterTwo n xs)
noncomputable def pairAfterCycle (n xs : V) : V := drainTwoEnd 1 7 6 n (pairAfterDrain n xs)

lemma pairAfterTwo_valid (n xs : V) (hv : ValidStore xs) :
    ValidStore (pairAfterTwo n xs) := replace_valid _ _ (replace_valid _ _ hv 6) 7
lemma pairAfterDrain_valid (n xs : V) (hv : ValidStore xs) :
    ValidStore (pairAfterDrain n xs) := drainEnd_valid 6 1 n _ (pairAfterTwo_valid n xs hv)
lemma pairAfterCycle_valid (n xs : V) (hv : ValidStore xs) :
    ValidStore (pairAfterCycle n xs) := drainTwoEnd_valid 1 7 6 n _ (pairAfterDrain_valid n xs hv)

lemma pairAfterTwo_registers (n xs : V) (hv : ValidStore xs) :
    registers (pairAfterTwo n xs)=PhysicalRegisters.write
      (PhysicalRegisters.write (registers xs) 6 n) 7 (registers xs 7+1) := by
  rw [pairAfterTwo,readReplace7 (replace 6 xs n) _ (replace_valid _ _ hv 6),readReplace6 _ _ hv]
lemma pairAfterDrain_registers (n xs : V) (hv : ValidStore xs) (ht : registers xs 1=0) :
    registers (pairAfterDrain n xs)=PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 6 0) 7
        (registers xs 7+1)) 1 n := by
  unfold pairAfterDrain drainEnd
  rw [registers_replace _ _ (replace_valid _ _ (pairAfterTwo_valid n xs hv) 6) 1,
    registers_replace _ _ (pairAfterTwo_valid n xs hv) 6,pairAfterTwo_registers n xs hv]
  funext r
  by_cases h1 : r=1 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
    simp_all [PhysicalRegisters.write]
lemma pairAfterCycle_registers (n xs : V) (hv : ValidStore xs) (ht : registers xs 1=0) :
    registers (pairAfterCycle n xs)=PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 6 n) 7
        (registers xs 7+1+n)) 1 0 := by
  unfold pairAfterCycle drainTwoEnd drainEnd
  rw [registers_replace _ _ (replace_valid _ _ (replace_valid _ _ (pairAfterDrain_valid n xs hv) 1) 7) 6,
    registers_replace _ _ (replace_valid _ _ (pairAfterDrain_valid n xs hv) 1) 7,
    registers_replace _ _ (pairAfterDrain_valid n xs hv) 1,
    pairAfterDrain_registers n xs hv ht]
  funext r
  by_cases h1 : r=1 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
    simp_all [PhysicalRegisters.write]

lemma pairLoopEnd_cycle (n xs : V) (hv : ValidStore xs) (ht : registers xs 1=0) :
    pairLoopEnd n (pairAfterCycle n xs)=pairLoopEnd (n+1) xs := by
  apply registers_ext (pairLoopEnd_valid _ _ (pairAfterCycle_valid n xs hv)) (pairLoopEnd_valid _ _ hv)
  unfold pairLoopEnd
  rw [readReplace7 (replace 6 (pairAfterCycle n xs) 0) _ (replace_valid _ _ (pairAfterCycle_valid n xs hv) 6),
    readReplace6 _ _ (pairAfterCycle_valid n xs hv),
    readReplace7 (replace 6 xs 0) _ (replace_valid _ _ hv 6),readReplace6 _ _ hv,
    pairAfterCycle_registers n xs hv ht]
  funext r
  by_cases h1 : r=1 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
    simp_all [PhysicalRegisters.write,SourceCantorInternal.triangle_succ,add_assoc,add_comm,add_left_comm]
#print axioms pairLoopEnd_cycle
end M6.Arithmetic.PA.InternalTrace.CodedSource


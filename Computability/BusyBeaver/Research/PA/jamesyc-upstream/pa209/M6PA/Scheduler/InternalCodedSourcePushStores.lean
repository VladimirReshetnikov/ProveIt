module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourcePushRows
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

lemma pairEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (pairEnd xs) :=
  replace_valid _ _ (replace_valid _ _ (replace_valid _ _ hv 1) 6) 7
lemma pairEnd_registers (xs : V) (hv : ValidStore xs) :
    registers (pairEnd xs)=PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 0) 6 0) 7
      (SourceCantorInternal.pairValue (registers xs 6) (registers xs 1)) := by
  have h1 : registers (replace 1 xs 0)=PhysicalRegisters.write (registers xs) 1 0 := registers_replace xs 0 hv 1
  have h6 : registers (replace 6 (replace 1 xs 0) 0)=
    PhysicalRegisters.write (registers (replace 1 xs 0)) 6 0 := registers_replace _ _ (replace_valid _ _ hv 1) 6
  have h7 : registers (pairEnd xs)=PhysicalRegisters.write (registers (replace 6 (replace 1 xs 0) 0)) 7
    (SourceCantorInternal.pairValue (registers xs 6) (registers xs 1)) :=
    registers_replace _ _ (replace_valid _ _ (replace_valid _ _ hv 1) 6) 7
  rw [h7,h6,h1]

noncomputable def pushAfterT (xs : V) : V := drainEnd 1 6 (registers xs 1) xs
noncomputable def pushAfterW (xs : V) : V := drainEnd 2 1 (registers xs 2) (pushAfterT xs)
noncomputable def pushAfterPair (xs : V) : V := pairEnd (pushAfterW xs)
noncomputable def pushEnd (xs : V) : V := replace 2 (replace 1 xs 0)
  (SourceCantorInternal.pairValue (registers xs 1) (registers xs 2))
lemma pushAfterT_valid (xs : V) (hv : ValidStore xs) : ValidStore (pushAfterT xs) := drainEnd_valid 1 6 _ xs hv
lemma pushAfterW_valid (xs : V) (hv : ValidStore xs) : ValidStore (pushAfterW xs) := drainEnd_valid 2 1 _ _ (pushAfterT_valid xs hv)
lemma pushAfterPair_valid (xs : V) (hv : ValidStore xs) : ValidStore (pushAfterPair xs) := pairEnd_valid _ (pushAfterW_valid xs hv)
lemma pushAfterT_registers (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) :
    registers (pushAfterT xs)=PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 0) 6 (registers xs 1) := by
  rw [pushAfterT,drainEnd_registers _ _ _ _ hv,hx,zero_add]
lemma pushAfterW_registers (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) :
    registers (pushAfterW xs)=PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 (registers xs 2)) 2 0) 6 (registers xs 1) := by
  rw [pushAfterW,drainEnd_registers _ _ _ _ (pushAfterT_valid xs hv),pushAfterT_registers xs hv hx]
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h6 : r=6 <;>
    simp_all [PhysicalRegisters.write]
lemma pushAfterPair_registers (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) :
    registers (pushAfterPair xs)=PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 0) 2 0) 6 0) 7
      (SourceCantorInternal.pairValue (registers xs 1) (registers xs 2)) := by
  rw [pushAfterPair,pairEnd_registers _ (pushAfterW_valid xs hv),pushAfterW_registers xs hv hx]
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
    simp_all [PhysicalRegisters.write]
lemma pushEnd_composition (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    drainEnd 7 2 (SourceCantorInternal.pairValue (registers xs 1) (registers xs 2)) (pushAfterPair xs)=pushEnd xs := by
  have h1 : registers (replace 1 xs 0)=PhysicalRegisters.write (registers xs) 1 0 := registers_replace xs 0 hv 1
  have h2 : registers (pushEnd xs)=PhysicalRegisters.write (registers (replace 1 xs 0)) 2
    (SourceCantorInternal.pairValue (registers xs 1) (registers xs 2)) := registers_replace _ _ (replace_valid _ _ hv 1) 2
  apply registers_ext (ys:=pushEnd xs) (drainEnd_valid _ _ _ _ (pushAfterPair_valid xs hv))
    (replace_valid _ _ (replace_valid _ _ hv 1) 2)
  rw [drainEnd_registers _ _ _ _ (pushAfterPair_valid xs hv),pushAfterPair_registers xs hv hx,h2,h1]
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
    simp_all [PhysicalRegisters.write]
#print axioms pushEnd_composition
end M6.Arithmetic.PA.InternalTrace.CodedSource


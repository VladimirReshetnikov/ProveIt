import BusyBeaver.ZFC.ArithmeticControlSimulation254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlSimulation254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlData254 FiniteControlTable254 RegisterPath
open ArithmeticCantor ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.step_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.step_decnz_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.step_decnz_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.step_break
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.step_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.step_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.related_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.step_nonzero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.related_step
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulation254.related_halt

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (i : Control) (r : Nat) (he : (source i).2=.inc r) (file : V) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (incPath (source i).1)) : V)
        (writeValue ((Permutation252Frame.physOf r : Nat) : V)
          ((physicalValues file).getD (Permutation252Frame.physOf r) 0+1) file) :=
  step_inc i r he file
example (i : Control) (r : Nat) (he : (source i).2=.decnz r) (file : V)
    (hz : (physicalValues file).getD (Permutation252Frame.physOf r) 0=0) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (breakPath 1 (source i).1)) : V) file :=
  step_decnz_zero i r he file hz
example (i : Control) (r : Nat) (he : (source i).2=.decnz r) (file : V)
    (hn : (physicalValues file).getD (Permutation252Frame.physOf r) 0≠0) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (incPath (source i).1)) : V)
        (writeValue ((Permutation252Frame.physOf r : Nat) : V)
          ((physicalValues file).getD (Permutation252Frame.physOf r) 0-1) file) :=
  step_decnz_positive i r he file hn
example (i : Control) (k : Nat) (he : (source i).2=.brk k) (file : V) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (breakPath k (source i).1)) : V) file :=
  step_break i k he file
example (i : Control) (k : Nat) (he : (source i).2=.cont k) (file : V) :
    stepValue (liveValue (number i : V) file)=
      liveValue (number (resolveControl (continuePath k (source i).1)) : V) file :=
  step_continue i k he file
example (i : Control) (he : (source i).2=.halt) (file : V) :
    stepValue (liveValue (number i : V) file)=0 := step_halt i he file
example (i : Control) (file count gap : V) :
    Related (liveValue (number i : V) file) (entryValue (number i : V) file count gap) :=
  related_entry i file count gap
example (i : Control) (file : V) (hh : (source i).2≠.halt) :
    stepValue (liveValue (number i : V) file)≠0 := step_nonzero i file hh
example (logical binary : V) (h : Related logical binary) (hn : stepValue logical≠0) :
    ∃ time : V, 0<time ∧ Related (stepValue logical) (runFrom time binary) :=
  related_step logical binary h hn
example (logical binary : V) (h : Related logical binary) (hz : stepValue logical=0) :
    ∃ time : V, 0<time ∧ first (runFrom time binary)=0 :=
  related_halt logical binary h hz

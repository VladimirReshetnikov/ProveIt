import BusyBeaver.ZFC.ArithmeticControlFetch254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlFetch254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFrame254 FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.first_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.read_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.copyTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.restoreTest_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.readEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.next_copy_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.next_restore_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.copy_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.restore_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.fetch_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.fetch_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254.fetch_zero_initial

example : initialControl=fetchTest := first_entry
example : resolveControl [true]=readEntry := read_entry
example : source copyTest=([false,true,false,false],.decnz 0) := copyTest_source
example : source restoreTest=([false,true,true,false,false],.decnz 6) := restoreTest_source
example : source readEntry=([true,false,false,false,false],.decnz 8) := readEntry_source
example : resolveControl (continuePath 3 (source copyContinue).1)=copyTest := next_copy_continue
example : resolveControl (continuePath 2 (source restoreContinue).1)=restoreTest := next_restore_continue

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (file : V) :
    controlRun (4*regValue file npReg+1) (liveValue (number copyTest : V) file)=
      liveValue (number restoreTest : V) (copyFile file (regValue file npReg)) := copy_run file
example (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number restoreTest : V) file)=
      liveValue (number bumpNP : V) (restoreFile file (regValue file s1Reg)) := restore_run file
example (file : V) (hpl : regValue file plReg≠0) :
    controlRun 2 (liveValue (number fetchTest : V) file)=
      liveValue (number readEntry : V) (put plReg (regValue file plReg-1) file) := fetch_positive file hpl
example (file : V) (hpl : regValue file plReg=0) (hs1 : regValue file s1Reg=0) :
    controlRun (7*regValue file npReg+4) (liveValue (number fetchTest : V) file)=
      liveValue (number readEntry : V)
        (put npReg (regValue file npReg+1) (put plReg (regValue file npReg) file)) := fetch_zero file hpl hs1
example (file : V) (hpl : regValue file plReg=0) (hs1 : regValue file s1Reg=0) :
    controlRun (7*regValue file npReg+4) (liveValue (number initialControl : V) file)=
      liveValue (number readEntry : V)
        (put npReg (regValue file npReg+1) (put plReg (regValue file npReg) file)) := fetch_zero_initial file hpl hs1
example : controlRun (4 : V) (liveValue (number initialControl : V) 0)=
    liveValue (number readEntry : V) (put npReg 1 (put plReg 0 (0 : V))) := by
  have hn : regValue (0 : V) npReg=0 := projection_zero 8 npReg
  have hp : regValue (0 : V) plReg=0 := projection_zero 8 plReg
  have hs : regValue (0 : V) s1Reg=0 := projection_zero 8 s1Reg
  simpa only [hn,mul_zero,zero_add] using fetch_zero_initial (0 : V) hp hs
example (file : V) (hpl : regValue file plReg=0) (hs1 : regValue file s1Reg=0)
    (hnp : regValue file npReg=1) :
    controlRun (11 : V) (liveValue (number fetchTest : V) file)=
      liveValue (number readEntry : V) (put npReg 2 (put plReg 1 file)) := by
  have h := fetch_zero file hpl hs1
  simpa only [hnp,show 7*(1 : V)+4=11 by ring,show (1 : V)+1=2 by ring] using h
example (file : V) (hpl : regValue file plReg=1) :
    controlRun (2 : V) (liveValue (number fetchTest : V) file)=
      liveValue (number readEntry : V) (put plReg 0 file) := by
  have hn : regValue file plReg≠0 := by rw [hpl]; exact Arithmetic.one_ne_zero
  simpa only [hpl,tsub_self] using fetch_positive file hn

import BusyBeaver.ZFC.ArithmeticControlDispatch254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlDispatch254 ArithmeticControlFetch254
open ArithmeticControlRead254 (acReg)
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.dispatchEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.mpEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.dropEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.nipEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.nipHalt_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.next_nip_again
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.opcode_cases
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.dispatch_mp
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.dispatch_drop
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.dispatch_nip
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.dispatch_ax
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.nip_falsity
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.dispatch_nip_falsity
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254.dispatch_nip_falsity_binary_entry

example : source dispatchEntry=([true,true,true,false,false],.decnz 3) := dispatchEntry_source
example : source mpEntry=([true,true,true,true,false,false,false,false,false,false],.decnz 1) := mpEntry_source
example : source dropEntry=([true,true,true,false,true,false,true,false,false,false],.decnz 1) := dropEntry_source
example : source nipEntry=([true,true,true,false,true,false,false,true,false,true,false],.inc 6) := nipEntry_source
example : source nipHalt=([true,true,true,false,true,false,false,true,false,true,true,false,true],.halt) := nipHalt_source
example : resolveControl (continuePath 2 (source nipAgain).1)=nipTestS1 := next_nip_again

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (a : V) : a=0 ∨ a=1 ∨ a=2 ∨ ∃ c : V, a=c+3 := opcode_cases a
example (file : V) (ha : regValue file acReg=0) :
    controlRun 1 (liveValue (number dispatchEntry : V) file)=liveValue (number mpEntry : V) file := dispatch_mp file ha
example (file : V) (ha : regValue file acReg=1) :
    controlRun 2 (liveValue (number dispatchEntry : V) file)=
      liveValue (number dropEntry : V) (put acReg 0 file) := dispatch_drop file ha
example (file : V) (ha : regValue file acReg=2) :
    controlRun 3 (liveValue (number dispatchEntry : V) file)=
      liveValue (number nipEntry : V) (put acReg 0 file) := dispatch_nip file ha
example (file c : V) (ha : regValue file acReg=c+3) :
    controlRun 3 (liveValue (number dispatchEntry : V) file)=
      liveValue (number axEntry : V) (put acReg c file) := dispatch_ax file c ha
example (file : V) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=1) :
    controlRun 7 (liveValue (number nipEntry : V) file)=0 := nip_falsity file hs hh
example (file : V) (ha : regValue file acReg=2) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=1) :
    controlRun 10 (liveValue (number dispatchEntry : V) file)=0 := dispatch_nip_falsity file ha hs hh
example (file count gap : V) (ha : regValue file acReg=2)
    (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=1) :
    ∃ time : V, first (ArithmeticMachineRunFromPerm252.runFrom time
      (entryValue (number dispatchEntry : V) file count gap))=0 := dispatch_nip_falsity_binary_entry file count gap ha hs hh
example (file t : V) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=1) :
    controlRun (7+t) (liveValue (number nipEntry : V) file)=0 := by
  rw [controlRun_add,nip_falsity file hs hh,controlRun_halted]
example (file t : V) (ha : regValue file acReg=2) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=1) :
    controlRun (10+t) (liveValue (number dispatchEntry : V) file)=0 := by
  rw [controlRun_add,dispatch_nip_falsity file ha hs hh,controlRun_halted]
example (r : Fin 9 → V) (ha : r acReg=2) (hs : r s1Reg=0) (hh : r cacheReg=1) :
    controlRun 10 (liveValue (number dispatchEntry : V) (fileValue r))=0 := by
  apply dispatch_nip_falsity
  · simpa only [reg_file] using ha
  · simpa only [reg_file] using hs
  · simpa only [reg_file] using hh
example (file : V) (ha : regValue file acReg=2) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=1) :
    ∃ time : V, first (ArithmeticMachineRunFromPerm252.runFrom time
      (entryValue (number dispatchEntry : V) file 56 0))=0 := dispatch_nip_falsity_binary_entry file 56 0 ha hs hh
end Model

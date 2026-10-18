import BusyBeaver.ZFC.ArithmeticControlAXParamConstructor254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlParamPush254 (paramPushFile)
open ArithmeticControlConstructor254 (constructorFile)
open ArithmeticControlAXParamConstructor254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamConstructor254.param_constructor_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamConstructor254.constructor_after_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamConstructor254.axParamConstructorFile_tw
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamConstructor254.axParamConstructorFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamConstructor254.ax_param_constructor_run

example : ArithmeticControlAXParamPush254.exit = ArithmeticControlAXConstructor254.entry :=
  param_constructor_join

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) : constructorFile 0 (paramPushFile file) = axParamConstructorFile file :=
  constructor_after_push file

example (file : V) : regValue (axParamConstructorFile file) twReg =
    wim (regValue file twReg) (regValue file p1Reg) := axParamConstructorFile_tw file

example (file : V) (i : Fin 9) (ht : i ≠ twReg) :
    regValue (axParamConstructorFile file) i = regValue file i :=
  axParamConstructorFile_other file i ht

example (file : V) : regValue (axParamConstructorFile file) wsReg = regValue file wsReg :=
  axParamConstructorFile_other file wsReg (by decide)

example (file : V) : regValue (axParamConstructorFile file) p1Reg = regValue file p1Reg :=
  axParamConstructorFile_other file p1Reg (by decide)

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number ArithmeticControlAXParamPush254.entry : V) file) =
        liveValue (number ArithmeticControlAXConstructor254.exit : V)
          (put twReg (wim (regValue file twReg) (regValue file p1Reg)) file) :=
  ax_param_constructor_run file h1 h2

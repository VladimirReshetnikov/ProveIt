import BusyBeaver.ZFC.ArithmeticControlAXConstructor254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlAXConstructor254 FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor254.entry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor254.exit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor254.ax_constructor_run

example : (source entry).2 = .decnz 2 := entry_source
example : (source ArithmeticControlAXConstructor254.exit).2 = .decnz 1 := exit_source

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number ArithmeticControlAXConstructor254.exit : V)
        (put twReg (wim (first (regValue file wsReg)) (regValue file twReg))
          (put wsReg (second (regValue file wsReg)) file)) := ax_constructor_run file h1 h2

example (file left rest : V) (hw : regValue file wsReg = cantor left rest)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number ArithmeticControlAXConstructor254.exit : V)
        (put twReg (wim left (regValue file twReg)) (put wsReg rest file)) := by
  simpa only [hw, first_cantor, second_cantor] using ax_constructor_run file h1 h2

import BusyBeaver.ZFC.ArithmeticControlAXReadTW254

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlAXReadTW254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlPair254 (twReg)
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadTW254.entry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadTW254.exit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadTW254.twReadFile_tw
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadTW254.twReadFile_pl
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadTW254.twReadFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadTW254.read_tw_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadTW254.read_tw_pair_run

example : source entry =
    ([true,true,true,false,true,false,false,true,false,false,true,false,true,false,false,false,true,false,true,false,false,false,false], .decnz 8) :=
  entry_source

example : source exit =
    ([true,true,true,false,true,false,false,true,false,false,true,false,true,false,false,false,true,false,true,true,false,false,false], .decnz 2) :=
  exit_source

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) :
    regValue (twReadFile file) twReg =
      regValue file twReg + first (regValue file plReg) :=
  twReadFile_tw file

example (file : V) :
    regValue (twReadFile file) plReg = second (regValue file plReg) :=
  twReadFile_pl file

example (file : V) (i : Fin 9) (hc : i ≠ twReg) (hp : i ≠ plReg) :
    regValue (twReadFile file) i = regValue file i :=
  twReadFile_other file i hc hp

example (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number entry : V) file) =
        liveValue (number exit : V) (twReadFile file) :=
  read_tw_run file h1 h2

example (file x rest : V) (hp : regValue file plReg = cantor x rest)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number entry : V) file) =
        liveValue (number exit : V)
          (put twReg (regValue file twReg + x) (put plReg rest file)) :=
  read_tw_pair_run file x rest hp h1 h2

-- Cache and WS occupy physical fields7 and0; both remain unchanged.
example (file : V) :
    regValue (twReadFile file) (7 : Fin 9) = regValue file (7 : Fin 9) :=
  twReadFile_other file 7 (by decide) (by decide)

example (file : V) :
    regValue (twReadFile file) (0 : Fin 9) = regValue file (0 : Fin 9) :=
  twReadFile_other file 0 (by decide) (by decide)

example (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (twReadFile file) s1Reg = 0 :=
  (twReadFile_other file s1Reg (by decide) (by decide)).trans h1

example (file : V) (h2 : regValue file s2Reg = 0) :
    regValue (twReadFile file) s2Reg = 0 :=
  (twReadFile_other file s2Reg (by decide) (by decide)).trans h2

example (file : V) (ht : regValue file twReg = 0)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number entry : V) file) =
        liveValue (number exit : V)
          (put twReg (first (regValue file plReg))
            (put plReg (second (regValue file plReg)) file)) := by
  simpa only [twReadFile, ht, zero_add] using read_tw_run file h1 h2

end Model

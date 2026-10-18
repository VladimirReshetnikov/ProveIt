import BusyBeaver.ZFC.ArithmeticControlAXReadCache254

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlAXReadCache254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlDispatch254 (cacheReg)
open FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadCache254.entry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadCache254.exit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadCache254.cacheReadFile_cache
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadCache254.cacheReadFile_pl
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadCache254.cacheReadFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadCache254.read_cache_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadCache254.read_cache_pair_run

example : source entry =
    ([true,true,true,false,true,false,false,true,false,false,true,false,true,false,false,false,false,false,false,false], .decnz 8) :=
  entry_source

example : source exit =
    ([true,true,true,false,true,false,false,true,false,false,true,false,true,false,false,false,true,false,false,false,false,false,false], .decnz 1) :=
  exit_source

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) :
    regValue (cacheReadFile file) cacheReg =
      regValue file cacheReg + first (regValue file plReg) :=
  cacheReadFile_cache file

example (file : V) :
    regValue (cacheReadFile file) plReg = second (regValue file plReg) :=
  cacheReadFile_pl file

example (file : V) (i : Fin 9) (hc : i ≠ cacheReg) (hp : i ≠ plReg) :
    regValue (cacheReadFile file) i = regValue file i :=
  cacheReadFile_other file i hc hp

example (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number entry : V) file) =
        liveValue (number exit : V) (cacheReadFile file) :=
  read_cache_run file h1 h2

example (file x rest : V) (hp : regValue file plReg = cantor x rest)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number entry : V) file) =
        liveValue (number exit : V)
          (put cacheReg (regValue file cacheReg + x) (put plReg rest file)) :=
  read_cache_pair_run file x rest hp h1 h2

-- Logical TW=1 and WS=2 occupy physical fields2 and0. These clients need
-- no additional arithmetic-module imports beyond the checked ReadShape chain.
example (file : V) :
    regValue (cacheReadFile file) (2 : Fin 9) = regValue file (2 : Fin 9) :=
  cacheReadFile_other file 2 (by decide) (by decide)

example (file : V) :
    regValue (cacheReadFile file) (0 : Fin 9) = regValue file (0 : Fin 9) :=
  cacheReadFile_other file 0 (by decide) (by decide)

example (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (cacheReadFile file) s1Reg = 0 :=
  (cacheReadFile_other file s1Reg (by decide) (by decide)).trans h1

example (file : V) (h2 : regValue file s2Reg = 0) :
    regValue (cacheReadFile file) s2Reg = 0 :=
  (cacheReadFile_other file s2Reg (by decide) (by decide)).trans h2

end Model

import BusyBeaver.ZFC.ArithmeticControlAXGenRead254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlAXGenRead254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254.gen_read_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254.axGenReadFile_eq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254.axGenReadFile_tw
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254.axGenReadFile_ws
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254.axGenReadFile_cache
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254.axGenReadFile_pl
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254.axGenReadFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254.ax_gen_read_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXGenRead254.ax_gen_read_pair_run

example : ArithmeticControlGEN254.nextRead = ArithmeticControlAXReadCache254.entry := gen_read_join

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) : axGenReadFile file =
    put cacheReg (regValue file cacheReg + first (regValue file plReg))
      (put plReg (second (regValue file plReg))
        (put twReg (wal (regValue file p1Reg) (regValue file cacheReg))
          (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file))) :=
  axGenReadFile_eq file

example (file : V) : regValue (axGenReadFile file) twReg =
    wal (regValue file p1Reg) (regValue file cacheReg) := axGenReadFile_tw file

example (file : V) : regValue (axGenReadFile file) wsReg =
    cantor (regValue file twReg) (regValue file wsReg) := axGenReadFile_ws file

example (file : V) : regValue (axGenReadFile file) cacheReg =
    regValue file cacheReg + first (regValue file plReg) := axGenReadFile_cache file

example (file : V) : regValue (axGenReadFile file) plReg =
    second (regValue file plReg) := axGenReadFile_pl file

example (file : V) (i : Fin 9) (ht : i ≠ twReg) (hs : i ≠ wsReg)
    (hc : i ≠ cacheReg) (hp : i ≠ plReg) : regValue (axGenReadFile file) i = regValue file i :=
  axGenReadFile_other file i ht hs hc hp

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number ArithmeticControlAXReadCache254.exit : V) (axGenReadFile file) :=
  ax_gen_read_run file h1 h2

example (file x rest : V) (hp : regValue file plReg = cantor x rest)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number ArithmeticControlAXReadCache254.exit : V)
        (put cacheReg (regValue file cacheReg + x)
          (put plReg rest
            (put twReg (wal (regValue file p1Reg) (regValue file cacheReg))
              (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)))) :=
  ax_gen_read_pair_run file x rest hp h1 h2

example (file : V) (h1 : regValue file s1Reg = 0) : regValue (axGenReadFile file) s1Reg = 0 :=
  (axGenReadFile_other file s1Reg (by decide) (by decide) (by decide) (by decide)).trans h1

example (file : V) (h2 : regValue file s2Reg = 0) : regValue (axGenReadFile file) s2Reg = 0 :=
  (axGenReadFile_other file s2Reg (by decide) (by decide) (by decide) (by decide)).trans h2

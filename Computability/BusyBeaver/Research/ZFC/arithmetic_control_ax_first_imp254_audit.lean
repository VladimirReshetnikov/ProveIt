import BusyBeaver.ZFC.ArithmeticControlAXFirstImp254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlAXFirstImp254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.cache_argument_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.argument_read_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.read_constructor_join
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.firstImpFile_tw
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.firstImpFile_ws
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.firstImpFile_pl
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.firstImpFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.first_imp_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.axFirstImpFile_tw
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.axFirstImpFile_ws
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.axFirstImpFile_cache
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.axFirstImpFile_pl
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.axFirstImpFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254.ax_first_imp_run

example : ArithmeticControlAXReadCache254.exit = ArithmeticControlAXArgumentPush254.entry :=
  cache_argument_join
example : ArithmeticControlAXArgumentPush254.exit = ArithmeticControlAXReadTW254.entry :=
  argument_read_join
example : ArithmeticControlAXReadTW254.exit = ArithmeticControlConstructor254.impEntry :=
  read_constructor_join

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (file : V) : regValue (firstImpFile file) twReg =
    wim (regValue file acReg) (first (regValue file plReg)) := firstImpFile_tw file
example (file : V) : regValue (firstImpFile file) wsReg =
    cantor (regValue file twReg) (regValue file wsReg) := firstImpFile_ws file
example (file : V) : regValue (firstImpFile file) plReg =
    second (regValue file plReg) := firstImpFile_pl file
example (file : V) (i : Fin 9) (ht : i ≠ twReg) (hs : i ≠ wsReg) (hp : i ≠ plReg) :
    regValue (firstImpFile file) i = regValue file i := firstImpFile_other file i ht hs hp
example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number ArithmeticControlAXArgumentPush254.entry : V) file) =
        liveValue (number ArithmeticControlConstructor254.impExit : V) (firstImpFile file) :=
  first_imp_run file h1 h2

example (file : V) : regValue (axFirstImpFile file) twReg =
    wim (regValue file acReg) (first (second (regValue file plReg))) := axFirstImpFile_tw file
example (file : V) : regValue (axFirstImpFile file) wsReg =
    cantor (wal (regValue file p1Reg) (regValue file cacheReg))
      (cantor (regValue file twReg) (regValue file wsReg)) := axFirstImpFile_ws file
example (file : V) : regValue (axFirstImpFile file) cacheReg =
    regValue file cacheReg + first (regValue file plReg) := axFirstImpFile_cache file
example (file : V) : regValue (axFirstImpFile file) plReg =
    second (second (regValue file plReg)) := axFirstImpFile_pl file
example (file : V) (i : Fin 9) (ht : i ≠ twReg) (hs : i ≠ wsReg)
    (hc : i ≠ cacheReg) (hp : i ≠ plReg) :
    regValue (axFirstImpFile file) i = regValue file i := axFirstImpFile_other file i ht hs hc hp
example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number ArithmeticControlConstructor254.impExit : V) (axFirstImpFile file) :=
  ax_first_imp_run file h1 h2

example (file x y rest : V) (h : regValue file plReg = cantor x (cantor y rest)) :
    regValue (axFirstImpFile file) twReg = wim (regValue file acReg) y := by
  rw [axFirstImpFile_tw, h, second_cantor, first_cantor]
example (file x y rest : V) (h : regValue file plReg = cantor x (cantor y rest)) :
    regValue (axFirstImpFile file) plReg = rest := by
  rw [axFirstImpFile_pl, h, second_cantor, second_cantor]
example (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (axFirstImpFile file) s1Reg = 0 :=
  (axFirstImpFile_other file s1Reg (by decide) (by decide) (by decide) (by decide)).trans h1
example (file : V) (h2 : regValue file s2Reg = 0) :
    regValue (axFirstImpFile file) s2Reg = 0 :=
  (axFirstImpFile_other file s2Reg (by decide) (by decide) (by decide) (by decide)).trans h2

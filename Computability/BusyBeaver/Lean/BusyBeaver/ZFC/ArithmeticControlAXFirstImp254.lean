import BusyBeaver.ZFC.ArithmeticControlAXGenRead254
import BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254
import BusyBeaver.ZFC.ArithmeticControlAXReadTW254
import BusyBeaver.ZFC.ArithmeticControlConstructor254

set_option autoImplicit false
noncomputable section

/-!
Compose actual controls136→222 and then41→222 in arbitrary internal IΣ₁
models. Every file and positive runtime is internal. This is the first AX
implication prefix, not the complete axiom bundle or interpreter equivalence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254
open ArithmeticControlStep254 ArithmeticControlFrame254 FiniteControlTable254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlParamPush254 (pushFile)
open ArithmeticControlCopyBack254 (argumentPushFile argumentPushFile_other)
open ArithmeticControlAXReadTW254 (twReadFile)
open ArithmeticControlConstructor254 (constructorFile)
open ArithmeticControlAXGenRead254 (axGenReadFile)

theorem cache_argument_join : ArithmeticControlAXReadCache254.exit =
    ArithmeticControlAXArgumentPush254.entry := rfl

theorem argument_read_join : ArithmeticControlAXArgumentPush254.exit =
    ArithmeticControlAXReadTW254.entry := rfl

theorem read_constructor_join : ArithmeticControlAXReadTW254.exit =
    ArithmeticControlConstructor254.impEntry := rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) :
    regValue (put p x file) p = x := write_at file x p
private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h

private def pushedFile (file : V) : V := pushFile (argumentPushFile acReg file)

private theorem pushedFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (pushedFile file) i = regValue file i := by
  rw [pushedFile, pushFile, read_put_other _ _ wsReg i hs.symm,
    read_put_other _ _ twReg i ht.symm, argumentPushFile_other acReg i file ht hs]

private theorem pushedFile_tw (file : V) : regValue (pushedFile file) twReg = 0 := by
  rw [pushedFile, pushFile, read_put_other _ _ wsReg twReg (by decide), read_put_self]

private theorem pushedFile_ws (file : V) : regValue (pushedFile file) wsReg =
    cantor (regValue file acReg) (cantor (regValue file twReg) (regValue file wsReg)) := by
  rw [pushedFile, pushFile, read_put_self, argumentPushFile, read_put_self,
    read_put_other _ _ twReg wsReg (by decide), read_put_self]

/-- Whole-file result of actual136→222. -/
def firstImpFile (file : V) : V := constructorFile 0 (twReadFile (pushedFile file))

theorem firstImpFile_tw (file : V) : regValue (firstImpFile file) twReg =
    wim (regValue file acReg) (first (regValue file plReg)) := by
  rw [firstImpFile, constructorFile, read_put_self,
    ArithmeticControlAXReadTW254.twReadFile_other _ wsReg (by decide) (by decide),
    pushedFile_ws, first_cantor, ArithmeticControlAXReadTW254.twReadFile_tw,
    pushedFile_tw, pushedFile_other file plReg (by decide) (by decide), zero_add]
  rfl

theorem firstImpFile_ws (file : V) : regValue (firstImpFile file) wsReg =
    cantor (regValue file twReg) (regValue file wsReg) := by
  rw [firstImpFile, constructorFile, read_put_other _ _ twReg wsReg (by decide),
    read_put_self, ArithmeticControlAXReadTW254.twReadFile_other _ wsReg
      (by decide) (by decide), pushedFile_ws, second_cantor]

theorem firstImpFile_pl (file : V) : regValue (firstImpFile file) plReg =
    second (regValue file plReg) := by
  rw [firstImpFile, ArithmeticControlConstructor254.constructorFile_other _ _ plReg
    (by decide) (by decide), ArithmeticControlAXReadTW254.twReadFile_pl,
    pushedFile_other file plReg (by decide) (by decide)]

theorem firstImpFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) (hp : i ≠ plReg) :
    regValue (firstImpFile file) i = regValue file i := by
  rw [firstImpFile, ArithmeticControlConstructor254.constructorFile_other _ _ i ht hs,
    ArithmeticControlAXReadTW254.twReadFile_other _ i ht hp, pushedFile_other file i ht hs]

theorem first_imp_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number ArithmeticControlAXArgumentPush254.entry : V) file) =
        liveValue (number ArithmeticControlConstructor254.impExit : V) (firstImpFile file) := by
  have hg1 : regValue (pushedFile file) s1Reg = 0 :=
    (pushedFile_other file s1Reg (by decide) (by decide)).trans h1
  have hg2 : regValue (pushedFile file) s2Reg = 0 :=
    (pushedFile_other file s2Reg (by decide) (by decide)).trans h2
  have hr1 : regValue (twReadFile (pushedFile file)) s1Reg = 0 :=
    (ArithmeticControlAXReadTW254.twReadFile_other _ s1Reg (by decide) (by decide)).trans hg1
  have hr2 : regValue (twReadFile (pushedFile file)) s2Reg = 0 :=
    (ArithmeticControlAXReadTW254.twReadFile_other _ s2Reg (by decide) (by decide)).trans hg2
  obtain ⟨tp, htp, hp⟩ := ArithmeticControlAXArgumentPush254.two_pushes_run file h1 h2
  change controlRun tp
    (liveValue (number ArithmeticControlAXArgumentPush254.entry : V) file) =
      liveValue (number ArithmeticControlAXArgumentPush254.exit : V) (pushedFile file) at hp
  obtain ⟨tr, _, hr⟩ := ArithmeticControlAXReadTW254.read_tw_run (pushedFile file) hg1 hg2
  obtain ⟨tc, _, hc⟩ := ArithmeticControlConstructor254.constructor_run
    ArithmeticControlConstructor254.impConstructor (twReadFile (pushedFile file)) hr1 hr2
  change controlRun tc
    (liveValue (number ArithmeticControlConstructor254.impEntry : V) (twReadFile (pushedFile file))) =
      liveValue (number ArithmeticControlConstructor254.impExit : V) (firstImpFile file) at hc
  rw [argument_read_join] at hp
  rw [read_constructor_join] at hr
  refine ⟨(tp + tr) + tc, le_trans (le_trans htp
    (le_add_of_nonneg_right (Arithmetic.zero_le _)))
    (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, controlRun_add, hp, hr, hc]

/-- Whole-file result of the actual AX prefix through its first implication. -/
def axFirstImpFile (file : V) : V := firstImpFile (axGenReadFile file)

theorem axFirstImpFile_tw (file : V) : regValue (axFirstImpFile file) twReg =
    wim (regValue file acReg) (first (second (regValue file plReg))) := by
  rw [axFirstImpFile, firstImpFile_tw,
    ArithmeticControlAXGenRead254.axGenReadFile_other file acReg
      (by decide) (by decide) (by decide) (by decide),
    ArithmeticControlAXGenRead254.axGenReadFile_pl]

theorem axFirstImpFile_ws (file : V) : regValue (axFirstImpFile file) wsReg =
    cantor (wal (regValue file p1Reg) (regValue file cacheReg))
      (cantor (regValue file twReg) (regValue file wsReg)) := by
  rw [axFirstImpFile, firstImpFile_ws, ArithmeticControlAXGenRead254.axGenReadFile_tw,
    ArithmeticControlAXGenRead254.axGenReadFile_ws]

theorem axFirstImpFile_cache (file : V) : regValue (axFirstImpFile file) cacheReg =
    regValue file cacheReg + first (regValue file plReg) := by
  rw [axFirstImpFile, firstImpFile_other _ cacheReg (by decide) (by decide) (by decide),
    ArithmeticControlAXGenRead254.axGenReadFile_cache]

theorem axFirstImpFile_pl (file : V) : regValue (axFirstImpFile file) plReg =
    second (second (regValue file plReg)) := by
  rw [axFirstImpFile, firstImpFile_pl, ArithmeticControlAXGenRead254.axGenReadFile_pl]

theorem axFirstImpFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) (hc : i ≠ cacheReg) (hp : i ≠ plReg) :
    regValue (axFirstImpFile file) i = regValue file i := by
  rw [axFirstImpFile, firstImpFile_other _ i ht hs hp,
    ArithmeticControlAXGenRead254.axGenReadFile_other file i ht hs hc hp]

theorem ax_first_imp_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number ArithmeticControlConstructor254.impExit : V) (axFirstImpFile file) := by
  have hg1 : regValue (axGenReadFile file) s1Reg = 0 :=
    (ArithmeticControlAXGenRead254.axGenReadFile_other file s1Reg
      (by decide) (by decide) (by decide) (by decide)).trans h1
  have hg2 : regValue (axGenReadFile file) s2Reg = 0 :=
    (ArithmeticControlAXGenRead254.axGenReadFile_other file s2Reg
      (by decide) (by decide) (by decide) (by decide)).trans h2
  obtain ⟨tg, htg, hg⟩ := ArithmeticControlAXGenRead254.ax_gen_read_run file h1 h2
  obtain ⟨ti, _, hi⟩ := first_imp_run (axGenReadFile file) hg1 hg2
  rw [cache_argument_join] at hg
  refine ⟨tg + ti, le_trans htg (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hg]
  exact hi

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXFirstImp254

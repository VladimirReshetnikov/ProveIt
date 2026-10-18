import BusyBeaver.ZFC.ArithmeticControlAXNextParamPush254
import BusyBeaver.ZFC.ArithmeticControlAXACPush254
import BusyBeaver.ZFC.ArithmeticControlAXACConstructor254

set_option autoImplicit false
noncomputable section

/-!
Actual275→354: push P1, push AC, then form the implication constructor.
The intermediate push/pop cancels. The final TW is wim(oldP1,oldAC), and
WS retains the earlier push cantor(oldTW,oldWS). All other fields are retained.
Data and positive clocks range over an arbitrary internal IΣ1 model.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlParamPush254 (paramPushFile)
open ArithmeticControlCopyBack254 (argumentPushFile)
open ArithmeticControlConstructor254 (constructorFile)
open FiniteControlTable254

theorem param_ac_join :
    ArithmeticControlAXNextParamPush254.exit = ArithmeticControlAXACPush254.entry := rfl

theorem ac_constructor_join :
    ArithmeticControlAXACPush254.exit = ArithmeticControlAXACConstructor254.entry := rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) :
    regValue (put p x file) p = x := write_at file x p
private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h
private theorem put_same (p : Fin 9) (file : V) : put p (regValue file p) file = file :=
  write_same file p
private theorem put_twice (p : Fin 9) (x y file : V) :
    put p y (put p x file) = put p y file := write_overwrite file x y p
private theorem file_ext (x y : V) (h : ∀ i, regValue x i = regValue y i) : x = y := by
  rw [←file_reg x, ←file_reg y]
  exact congrArg fileValue (funext h)
private theorem put_commute (p q : Fin 9) (h : p ≠ q) (x y file : V) :
    put p x (put q y file) = put q y (put p x file) := by
  have hcast : (p.val : V) ≠ (q.val : V) := by
    intro he
    exact h (Fin.ext (by simpa only [Nat.cast_inj] using he))
  apply file_ext
  intro i
  simp only [put, reg_write]
  by_cases hp : (p.val : V) = (i.val : V)
  · by_cases hq : (q.val : V) = (i.val : V)
    · exact False.elim (hcast (hp.trans hq.symm))
    · simp only [hp, hq, if_true, if_false]
  · by_cases hq : (q.val : V) = (i.val : V) <;> simp only [hp, hq, if_true, if_false]

/-- Complete301→354 effect, restoring every coordinate except TW. -/
def acConstructorFile (file : V) : V :=
  put twReg (wim (regValue file twReg) (regValue file acReg)) file

/-- Complete275→354 effect, retaining the first push in WS. -/
def nextImpFile (file : V) : V :=
  put twReg (wim (regValue file p1Reg) (regValue file acReg))
    (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)

theorem constructor_after_ac_push (file : V) :
    constructorFile 0 (argumentPushFile acReg file) = acConstructorFile file := by
  have hws : regValue (argumentPushFile acReg file) wsReg =
      cantor (regValue file twReg) (regValue file wsReg) := by
    rw [argumentPushFile, read_put_other _ _ twReg wsReg (by decide), read_put_self]
  have htw : regValue (argumentPushFile acReg file) twReg = regValue file acReg := by
    rw [argumentPushFile, read_put_self]
  simp only [constructorFile, Fin.val_zero, Nat.cast_zero]
  rw [hws, htw, first_cantor, second_cantor]
  simp only [argumentPushFile, acConstructorFile, wim,
    put_commute wsReg twReg (by decide), put_twice, put_same]

theorem ac_constructor_after_param_push (file : V) :
    acConstructorFile (paramPushFile file) = nextImpFile file := by
  have htw : regValue (paramPushFile file) twReg = regValue file p1Reg := by
    rw [paramPushFile, read_put_self]
  have hac : regValue (paramPushFile file) acReg = regValue file acReg :=
    ArithmeticControlAXNextParamPush254.paramPushFile_other file acReg (by decide) (by decide)
  rw [acConstructorFile, htw, hac]
  dsimp only [paramPushFile, nextImpFile]
  rw [put_twice]

theorem nextImpFile_tw (file : V) :
    regValue (nextImpFile file) twReg =
      wim (regValue file p1Reg) (regValue file acReg) := by
  rw [nextImpFile, read_put_self]

theorem nextImpFile_ws (file : V) :
    regValue (nextImpFile file) wsReg =
      cantor (regValue file twReg) (regValue file wsReg) := by
  rw [nextImpFile, read_put_other _ _ twReg wsReg (by decide), read_put_self]

theorem nextImpFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (nextImpFile file) i = regValue file i := by
  rw [nextImpFile, read_put_other _ _ twReg i ht.symm,
    read_put_other _ _ wsReg i hs.symm]

/-- Actual301→354, using only the two occurrence contracts. -/
theorem ac_constructor_run (file : V)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number ArithmeticControlAXACPush254.entry : V) file) =
        liveValue (number ArithmeticControlAXACConstructor254.exit : V)
          (acConstructorFile file) := by
  have hp1 : regValue (argumentPushFile acReg file) s1Reg = 0 :=
    (ArithmeticControlAXACPush254.acPushFile_other file s1Reg (by decide) (by decide)).trans h1
  have hp2 : regValue (argumentPushFile acReg file) s2Reg = 0 :=
    (ArithmeticControlAXACPush254.acPushFile_other file s2Reg (by decide) (by decide)).trans h2
  obtain ⟨tp, htp, hp⟩ := ArithmeticControlAXACPush254.ac_push_run file h1 h2
  obtain ⟨tc, _, hc⟩ :=
    ArithmeticControlAXACConstructor254.ax_constructor_run (argumentPushFile acReg file) hp1 hp2
  have hc' : controlRun tc
      (liveValue (number ArithmeticControlAXACConstructor254.entry : V)
        (argumentPushFile acReg file)) =
        liveValue (number ArithmeticControlAXACConstructor254.exit : V)
          (constructorFile 0 (argumentPushFile acReg file)) := by
    simpa only [constructorFile, Fin.val_zero, Nat.cast_zero, wim] using hc
  rw [ac_constructor_join] at hp
  refine ⟨tp + tc, le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hp, hc', constructor_after_ac_push]

/-- Actual275→354, with exact full file and positive internal time. -/
theorem next_imp_run (file : V)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number ArithmeticControlAXNextParamPush254.entry : V) file) =
        liveValue (number ArithmeticControlAXACConstructor254.exit : V)
          (nextImpFile file) := by
  have hp1 : regValue (paramPushFile file) s1Reg = 0 :=
    (ArithmeticControlAXNextParamPush254.paramPushFile_other file s1Reg (by decide) (by decide)).trans h1
  have hp2 : regValue (paramPushFile file) s2Reg = 0 :=
    (ArithmeticControlAXNextParamPush254.paramPushFile_other file s2Reg (by decide) (by decide)).trans h2
  obtain ⟨tp, htp, hp⟩ := ArithmeticControlAXNextParamPush254.ax_param_push_run file h1 h2
  obtain ⟨tc, _, hc⟩ := ac_constructor_run (paramPushFile file) hp1 hp2
  rw [param_ac_join] at hp
  refine ⟨tp + tc, le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hp, hc, ac_constructor_after_param_push]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextImp254

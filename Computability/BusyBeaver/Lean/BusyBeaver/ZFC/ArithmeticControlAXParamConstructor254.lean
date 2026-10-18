import BusyBeaver.ZFC.ArithmeticControlAXParamPush254
import BusyBeaver.ZFC.ArithmeticControlAXConstructor254

set_option autoImplicit false
noncomputable section

/-!
The actual AX parameter1 push at222→248 followed by the implication constructor
at248→275. Their effects cancel the intermediate WS push. The resulting TW is
wim(oldTW,oldP1), with every other coordinate, including all of WS, restored.
All data and the positive total clock are arbitrary internal IΣ1 values.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamConstructor254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlParamPush254 (paramPushFile)
open ArithmeticControlConstructor254 (constructorFile)
open FiniteControlTable254

/-- The two literal occurrences meet at actual control248. -/
theorem param_constructor_join :
    ArithmeticControlAXParamPush254.exit = ArithmeticControlAXConstructor254.entry := rfl

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

/-- A single write expresses the complete222→275 file effect. -/
def axParamConstructorFile (file : V) : V :=
  put twReg (wim (regValue file twReg) (regValue file p1Reg)) file

/-- Cantor projections cancel the temporary push without any standardness premise. -/
theorem constructor_after_push (file : V) :
    constructorFile 0 (paramPushFile file) = axParamConstructorFile file := by
  have hws : regValue (paramPushFile file) wsReg =
      cantor (regValue file twReg) (regValue file wsReg) := by
    rw [paramPushFile, read_put_other _ _ twReg wsReg (by decide), read_put_self]
  have htw : regValue (paramPushFile file) twReg = regValue file p1Reg := by
    rw [paramPushFile, read_put_self]
  simp only [constructorFile, Fin.val_zero, Nat.cast_zero]
  rw [hws, htw, first_cantor, second_cantor]
  simp only [paramPushFile, axParamConstructorFile, wim,
    put_commute wsReg twReg (by decide), put_twice, put_same]

theorem axParamConstructorFile_tw (file : V) :
    regValue (axParamConstructorFile file) twReg =
      wim (regValue file twReg) (regValue file p1Reg) := by
  rw [axParamConstructorFile, read_put_self]

theorem axParamConstructorFile_other (file : V) (i : Fin 9) (ht : i ≠ twReg) :
    regValue (axParamConstructorFile file) i = regValue file i := by
  rw [axParamConstructorFile, read_put_other _ _ twReg i ht.symm]

/-- Actual222→275 with positive internal time and all nine output fields fixed. -/
theorem ax_param_constructor_run (file : V)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number ArithmeticControlAXParamPush254.entry : V) file) =
        liveValue (number ArithmeticControlAXConstructor254.exit : V)
          (axParamConstructorFile file) := by
  have hp1 : regValue (paramPushFile file) s1Reg = 0 := by
    rw [ArithmeticControlAXParamPush254.paramPushFile_other file s1Reg (by decide) (by decide)]
    exact h1
  have hp2 : regValue (paramPushFile file) s2Reg = 0 := by
    rw [ArithmeticControlAXParamPush254.paramPushFile_other file s2Reg (by decide) (by decide)]
    exact h2
  obtain ⟨tp, htp, hp⟩ := ArithmeticControlAXParamPush254.ax_param_push_run file h1 h2
  obtain ⟨tc, _, hc⟩ :=
    ArithmeticControlAXConstructor254.ax_constructor_run (paramPushFile file) hp1 hp2
  have hc' : controlRun tc
      (liveValue (number ArithmeticControlAXConstructor254.entry : V) (paramPushFile file)) =
        liveValue (number ArithmeticControlAXConstructor254.exit : V)
          (constructorFile 0 (paramPushFile file)) := by
    simpa only [constructorFile, Fin.val_zero, Nat.cast_zero, wim] using hc
  rw [param_constructor_join] at hp
  refine ⟨tp + tc, le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hp, hc', constructor_after_push]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamConstructor254

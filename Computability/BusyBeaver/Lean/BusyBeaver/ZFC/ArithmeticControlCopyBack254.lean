import BusyBeaver.ZFC.ArithmeticControlParamPush254

set_option autoImplicit false
noncomputable section

/-!
Copy any literal argument register into TW and restore that register.
The generic contracts describe complete internal files and clocks. Their
premises are instruction shapes and interface equalities, not execution
assumptions. No particular AX occurrence is asserted in this module.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlCopyBack254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlClear254
open ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlUnpair254 (wsReg)
open FiniteControlTable254

structure CopyBackShape where
  copy : CopyShape
  restore : MoveShape
  first_target : copy.firstIndex = twReg
  second_target : copy.secondIndex = s1Reg
  restore_source : restore.sourceIndex = s1Reg
  restore_target : restore.targetIndex = copy.sourceIndex
  join : copy.exit = restore.test

theorem source_ne_tw (c : CopyBackShape) : c.copy.sourceIndex ≠ twReg := by
  simpa only [c.first_target] using c.copy.source_ne_first

theorem source_ne_s1 (c : CopyBackShape) : c.copy.sourceIndex ≠ s1Reg := by
  simpa only [c.second_target] using c.copy.source_ne_second

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) :
    regValue (put p x file) p = x := write_at file x p

private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h

private theorem file_ext (x y : V) (h : ∀ i, regValue x i = regValue y i) : x = y := by
  rw [←file_reg x, ←file_reg y]
  exact congrArg fileValue (funext h)

private theorem read_put (p q : Fin 9) (x file : V) :
    regValue (put p x file) q = if p = q then x else regValue file q := by
  by_cases h : p = q
  · subst q
    rw [if_pos rfl]
    exact read_put_self file x p
  · simpa only [if_neg h] using read_put_other file x p q h

/-- Exact internal clock; only scratch1 must initially vanish. -/
theorem copy_back_run (c : CopyBackShape) (file : V)
    (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file c.copy.sourceIndex + 2)
      (liveValue (number c.copy.test : V) file) =
      liveValue (number c.restore.exit : V)
        (put twReg (regValue file twReg + regValue file c.copy.sourceIndex) file) := by
  let h := regValue file c.copy.sourceIndex
  let g := put s1Reg h
    (put twReg (regValue file twReg + h) (put c.copy.sourceIndex 0 file))
  have hcopy : controlRun (4 * h + 1) (liveValue (number c.copy.test : V) file) =
      liveValue (number c.restore.test : V) g := by
    simpa only [c.first_target, c.second_target, c.join, h1, zero_add, h, g]
      using copy_run c.copy file
  have hgs1 : regValue g s1Reg = h := by
    dsimp only [g]
    rw [read_put_self]
  have hgp : regValue g c.copy.sourceIndex = 0 := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg c.copy.sourceIndex (source_ne_s1 c).symm,
      read_put_other _ _ twReg c.copy.sourceIndex (source_ne_tw c).symm, read_put_self]
  have hf : put c.copy.sourceIndex h (put s1Reg 0 g) =
      put twReg (regValue file twReg + regValue file c.copy.sourceIndex) file := by
    apply file_ext
    intro i
    by_cases ht : i = twReg
    · subst i
      dsimp only [g, h]
      rw [read_put_other _ _ c.copy.sourceIndex twReg (source_ne_tw c),
        read_put_other _ _ s1Reg twReg (by decide),
        read_put_other _ _ s1Reg twReg (by decide), read_put_self, read_put_self]
    by_cases hp : i = c.copy.sourceIndex
    · subst i
      simp [read_put, g, h, (source_ne_tw c).symm]
    by_cases hs : i = s1Reg
    · subst i
      rw [read_put_other _ _ c.copy.sourceIndex s1Reg (source_ne_s1 c),
        read_put_self, read_put_other _ _ twReg s1Reg (by decide), h1]
    simp [read_put, g, Ne.symm ht, Ne.symm hp, Ne.symm hs]
  have hrestore : controlRun (3 * h + 1)
      (liveValue (number c.restore.test : V) g) =
      liveValue (number c.restore.exit : V)
        (put twReg (regValue file twReg + regValue file c.copy.sourceIndex) file) := by
    simpa only [c.restore_source, c.restore_target, hgs1, hgp, zero_add, hf]
      using move_run c.restore g
  rw [show 7 * regValue file c.copy.sourceIndex + 2 = (4 * h + 1) + (3 * h + 1) by
      dsimp only [h]; ring, controlRun_add, hcopy, hrestore]

def argumentPushFile (argument : Fin 9) (file : V) : V :=
  put twReg (regValue file argument)
    (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)

theorem argumentPushFile_other (argument i : Fin 9) (file : V)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (argumentPushFile argument file) i = regValue file i := by
  rw [argumentPushFile, read_put_other _ _ twReg i ht.symm,
    read_put_other _ _ wsReg i hs.symm]

/-- A clean push followed by copy/restore, for any distinct argument field. -/
theorem argument_push_run (push : PushShape) (c : CopyBackShape)
    (join : push.output.exit = c.copy.test) (hw : c.copy.sourceIndex ≠ wsReg)
    (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number push.first.test : V) file) =
        liveValue (number c.restore.exit : V) (argumentPushFile c.copy.sourceIndex file) := by
  let g := pushFile file
  have hg1 : regValue g s1Reg = 0 := by
    dsimp only [g, pushFile]
    rw [read_put_other _ _ wsReg s1Reg (by decide),
      read_put_other _ _ twReg s1Reg (by decide)]
    exact h1
  have hgtw : regValue g twReg = 0 := by
    dsimp only [g, pushFile]
    rw [read_put_other _ _ wsReg twReg (by decide), read_put_self]
  have hgp : regValue g c.copy.sourceIndex = regValue file c.copy.sourceIndex := by
    dsimp only [g, pushFile]
    rw [read_put_other _ _ wsReg c.copy.sourceIndex hw.symm,
      read_put_other _ _ twReg c.copy.sourceIndex (source_ne_tw c).symm]
  have hf : put twReg (regValue g twReg + regValue g c.copy.sourceIndex) g =
      argumentPushFile c.copy.sourceIndex file := by
    rw [hgtw, hgp, zero_add]
    apply file_ext
    intro i
    by_cases ht : i = twReg
    · subst i
      simp [read_put, g, pushFile, argumentPushFile, twReg, wsReg]
    by_cases hs : i = wsReg
    · subst i
      simp [read_put, g, pushFile, argumentPushFile, twReg, wsReg]
    simp [read_put, g, pushFile, argumentPushFile, Ne.symm ht, Ne.symm hs]
  obtain ⟨tp, htp, hp⟩ := push_run push file h1 h2
  rw [join] at hp
  have hc := copy_back_run c g hg1
  rw [hf, hgp] at hc
  refine ⟨tp + (7 * regValue file c.copy.sourceIndex + 2),
    le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hp, hc]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlCopyBack254

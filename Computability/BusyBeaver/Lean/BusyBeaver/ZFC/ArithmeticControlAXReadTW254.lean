import BusyBeaver.ZFC.ArithmeticControlPair254

set_option autoImplicit false
noncomputable section

/-!
The actual AX parameter read at controls181..194, exiting at195. The
checked internal ReadShape theorem supplies unbounded execution; all
fourteen literal edges and nineteen resolved successors are bound here.
The next PL component is added to the old TW, with every other field except
PL retained. Both scratch registers initially vanish; TW is arbitrary.
The following constructor and remaining AX composition are separate.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadTW254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlReadTemplate254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlPair254 (twReg)
open FiniteControlTable254 RegisterPath

def entry : Control := ⟨181, by decide⟩
def exit : Control := ⟨195, by decide⟩

theorem entry_source : source entry =
    ([true,true,true,false,true,false,false,true,false,false,true,false,true,false,false,false,true,false,true,false,false,false,false], .decnz 8) := by rfl

theorem exit_source : source exit =
    ([true,true,true,false,true,false,false,true,false,false,true,false,true,false,false,false,true,false,true,true,false,false,false], .decnz 2) := by rfl

/-- Resolve a literal target through its finite tree path, avoiding catalogue search. -/
private theorem literal_target (P : List Bool) (q : Control)
    (hw : RMBisim.twalk ActualTree254.tree P 0 =
      some ((source q).2, (source q).1.length))
    (hc : consume P (source q).1.length = (source q).1) : resolveControl P = q := by
  have hw' : walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 =
      some ((source q).2, (source q).1.length) := by
    rw [RMBisim.walk_root, ActualTree254.tree_eq]
    exact hw
  apply source_injective
  rw [resolve_source _ _ _ hw', hc]

private def twReadShape : ReadShape where
  readEntry := entry
  bodyIncS2 := ⟨182, by decide⟩
  bodyTestS1 := ⟨183, by decide⟩
  bodyBreak := ⟨184, by decide⟩
  bodyMoveTest := ⟨185, by decide⟩
  bodyMoveInc := ⟨186, by decide⟩
  bodyMoveContinue := ⟨187, by decide⟩
  bodyContinue := ⟨188, by decide⟩
  restorePLTest := ⟨189, by decide⟩
  restorePLInc := ⟨190, by decide⟩
  restorePLContinue := ⟨191, by decide⟩
  outputTest := ⟨192, by decide⟩
  outputInc := ⟨193, by decide⟩
  outputContinue := ⟨194, by decide⟩
  nextRead := exit
  targetLogical := 1
  targetIndex := twReg
  target_physical := rfl
  target_ne_s1 := by decide
  target_ne_s2 := by decide
  target_ne_pl := by decide
  read_edge := by rfl
  body_inc_edge := by rfl
  body_test_edge := by rfl
  body_break_edge := by rfl
  body_move_test_edge := by rfl
  body_move_inc_edge := by rfl
  body_move_continue_edge := by rfl
  body_continue_edge := by rfl
  restore_test_edge := by rfl
  restore_inc_edge := by rfl
  restore_continue_edge := by rfl
  output_test_edge := by rfl
  output_inc_edge := by rfl
  output_continue_edge := by rfl
  next_read_positive := by
    apply literal_target <;> rfl
  next_read_zero := by
    apply literal_target <;> rfl
  next_body_inc := by
    apply literal_target <;> rfl
  next_body_test_positive := by
    apply literal_target <;> rfl
  next_body_test_zero := by
    apply literal_target <;> rfl
  next_body_break := by
    apply literal_target <;> rfl
  next_body_move_positive := by
    apply literal_target <;> rfl
  next_body_move_inc := by
    apply literal_target <;> rfl
  next_body_move_continue := by
    apply literal_target <;> rfl
  next_body_move_zero := by
    apply literal_target <;> rfl
  next_body_continue := by
    apply literal_target <;> rfl
  next_restore_pl_positive := by
    apply literal_target <;> rfl
  next_restore_pl_inc := by
    apply literal_target <;> rfl
  next_restore_pl_continue := by
    apply literal_target <;> rfl
  next_restore_pl_zero := by
    apply literal_target <;> rfl
  next_output_positive := by
    apply literal_target <;> rfl
  next_output_inc := by
    apply literal_target <;> rfl
  next_output_continue := by
    apply literal_target <;> rfl
  next_output_zero := by
    apply literal_target <;> rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Consume PL's first Cantor component into the existing TW. -/
def twReadFile (file : V) : V :=
  put twReg (regValue file twReg + first (regValue file plReg))
    (put plReg (second (regValue file plReg)) file)

private theorem read_put_self (file x : V) (p : Fin 9) :
    regValue (put p x file) p = x := write_at file x p

private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h

theorem twReadFile_tw (file : V) :
    regValue (twReadFile file) twReg =
      regValue file twReg + first (regValue file plReg) := by
  rw [twReadFile, read_put_self]

theorem twReadFile_pl (file : V) :
    regValue (twReadFile file) plReg = second (regValue file plReg) := by
  rw [twReadFile, read_put_other _ _ twReg plReg (by decide), read_put_self]

theorem twReadFile_other (file : V) (i : Fin 9)
    (hc : i ≠ twReg) (hp : i ≠ plReg) :
    regValue (twReadFile file) i = regValue file i := by
  rw [twReadFile, read_put_other _ _ twReg i hc.symm,
    read_put_other _ _ plReg i hp.symm]

/-- All values and the positive runtime belong to the ambient IΣ₁ model. -/
theorem read_tw_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number entry : V) file) =
        liveValue (number exit : V) (twReadFile file) := by
  exact read_shape twReadShape file h1 h2

/-- A parameter-stream client, allowing arbitrary old TW and remaining tail. -/
theorem read_tw_pair_run (file x rest : V)
    (hp : regValue file plReg = cantor x rest)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number entry : V) file) =
        liveValue (number exit : V)
          (put twReg (regValue file twReg + x) (put plReg rest file)) := by
  simpa only [twReadFile, hp, first_cantor, second_cantor] using
    read_tw_run file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadTW254

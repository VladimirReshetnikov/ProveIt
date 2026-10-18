import BusyBeaver.ZFC.ArithmeticControlConstructor254

set_option autoImplicit false
noncomputable section

/-!
Actual AX implication constructor at controls248→275. All 27 instruction edges
and 35 successor branches are bound directly to the existing finite catalogue.
The generic constructor contract supplies the unbounded internal execution.
This occurrence is the constructor immediately after the parameter1 push.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254
open ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticControlPair254 ArithmeticControlConstructor254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlUnpairCore254 (UnpairCoreShape)
open ArithmeticControlMP254 (Scale4Shape)
open FiniteControlTable254 RegisterPath

/-- The next actual AX implication constructor starts at control248. -/
def entry : Control := ⟨248, by decide⟩
/-- Its zero-tag exit is immediately the next push, at control275. -/
def exit : Control := ⟨275, by decide⟩

private def c249 : Control := ⟨249, by decide⟩
private def c250 : Control := ⟨250, by decide⟩
private def c251 : Control := ⟨251, by decide⟩
private def c252 : Control := ⟨252, by decide⟩
private def c253 : Control := ⟨253, by decide⟩
private def c254 : Control := ⟨254, by decide⟩
private def c255 : Control := ⟨255, by decide⟩
private def c256 : Control := ⟨256, by decide⟩
private def c257 : Control := ⟨257, by decide⟩
private def c258 : Control := ⟨258, by decide⟩
private def c259 : Control := ⟨259, by decide⟩
private def c260 : Control := ⟨260, by decide⟩
private def c261 : Control := ⟨261, by decide⟩
private def c262 : Control := ⟨262, by decide⟩
private def c263 : Control := ⟨263, by decide⟩
private def c264 : Control := ⟨264, by decide⟩
private def c265 : Control := ⟨265, by decide⟩
private def c266 : Control := ⟨266, by decide⟩
private def c267 : Control := ⟨267, by decide⟩
private def c268 : Control := ⟨268, by decide⟩
private def c269 : Control := ⟨269, by decide⟩
private def c270 : Control := ⟨270, by decide⟩
private def c271 : Control := ⟨271, by decide⟩
private def c272 : Control := ⟨272, by decide⟩
private def c273 : Control := ⟨273, by decide⟩
private def c274 : Control := ⟨274, by decide⟩

theorem entry_source : (source entry).2 = .decnz 2 := by rfl
theorem exit_source : (source exit).2 = .decnz 1 := by rfl

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

private def impPop : UnpairCoreShape where
  readEntry := entry
  bodyIncS2 := c249
  bodyTestS1 := c250
  bodyBreak := c251
  bodyMoveTest := c252
  bodyMoveInc := c253
  bodyMoveContinue := c254
  bodyContinue := c255
  restoreMainTest := c256
  restoreMainInc := c257
  restoreMainContinue := c258
  exit := c259
  mainLogical := 2
  mainIndex := wsReg
  main_physical := rfl
  main_ne_s1 := by decide
  main_ne_s2 := by decide
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
  next_restore_main_positive := by
    apply literal_target <;> rfl
  next_restore_main_inc := by
    apply literal_target <;> rfl
  next_restore_main_continue := by
    apply literal_target <;> rfl
  next_restore_main_zero := by
    apply literal_target <;> rfl

private def impCopy : CopyShape where
  test := c259
  firstInc := c260
  secondInc := c261
  again := c262
  exit := c263
  sourceLogical := 1
  firstLogical := 7
  secondLogical := 6
  sourceIndex := twReg
  firstIndex := s2Reg
  secondIndex := s1Reg
  source_physical := rfl
  first_physical := rfl
  second_physical := rfl
  source_ne_first := by decide
  source_ne_second := by decide
  first_ne_second := by decide
  test_edge := by rfl
  first_edge := by rfl
  second_edge := by rfl
  again_edge := by rfl
  positive_target := by
    apply literal_target <;> rfl
  first_target := by
    apply literal_target <;> rfl
  second_target := by
    apply literal_target <;> rfl
  repeat_target := by
    apply literal_target <;> rfl
  zero_target := by
    apply literal_target <;> rfl

private def impMove : MoveShape where
  test := c265
  increment := c266
  again := c267
  exit := c268
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := by rfl
  increment_edge := by rfl
  again_edge := by rfl
  positive_target := by
    apply literal_target <;> rfl
  increment_target := by
    apply literal_target <;> rfl
  repeat_target := by
    apply literal_target <;> rfl
  zero_target := by
    apply literal_target <;> rfl

private def impPair : PairShape where
  copy := impCopy
  testS1 := c263
  incS2 := c264
  move := impMove
  again := c268
  exit := c269
  copy_source := by rfl
  copy_first := by rfl
  copy_second := by rfl
  copy_exit := by rfl
  move_source := by rfl
  move_target := by rfl
  move_exit := by rfl
  test_edge := by rfl
  increment_edge := by rfl
  again_edge := by rfl
  positive_target := by
    apply literal_target <;> rfl
  zero_target := by
    apply literal_target <;> rfl
  increment_target := by
    apply literal_target <;> rfl
  repeat_target := by
    apply literal_target <;> rfl

private def impScale : Scale4Shape where
  test := c269
  inc1 := c270
  inc2 := c271
  inc3 := c272
  inc4 := c273
  again := c274
  exit := exit
  test_edge := by rfl
  inc1_edge := by rfl
  inc2_edge := by rfl
  inc3_edge := by rfl
  inc4_edge := by rfl
  again_edge := by rfl
  positive_target := by
    apply literal_target <;> rfl
  zero_target := by
    apply literal_target <;> rfl
  next_inc1 := by
    apply literal_target <;> rfl
  next_inc2 := by
    apply literal_target <;> rfl
  next_inc3 := by
    apply literal_target <;> rfl
  next_inc4 := by
    apply literal_target <;> rfl
  repeat_target := by
    apply literal_target <;> rfl

/-- Every field is a literal edge/target equality or interface equality. -/
def occurrence : ConstructorShape where
  pop := impPop
  pair := impPair
  scale := impScale
  tag := 0
  exit := exit
  pop_main := rfl
  pop_to_pair := rfl
  pair_to_scale := rfl
  tag_steps := TagChain.nil exit

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Actual248→275 has the complete implication-constructor file effect. -/
theorem ax_constructor_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number exit : V)
        (put twReg (wim (first (regValue file wsReg)) (regValue file twReg))
          (put wsReg (second (regValue file wsReg)) file)) := by
  simpa only [show occurrence.pop.readEntry = entry from rfl,
    show occurrence.exit = exit from rfl,
    show occurrence.tag = (0 : Fin 4) from rfl,
    constructorFile, Fin.val_zero, Nat.cast_zero, wim] using constructor_run occurrence file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor254

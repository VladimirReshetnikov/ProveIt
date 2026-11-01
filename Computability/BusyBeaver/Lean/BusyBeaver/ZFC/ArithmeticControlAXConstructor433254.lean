import BusyBeaver.ZFC.ArithmeticControlConstructor254
import BusyBeaver.ZFC.ArithmeticControlSourceRank254

set_option autoImplicit false
noncomputable section

/-!
Actual AX implication constructor at controls433→460. All 27 instruction edges
and 35 successor branches reuse cached full equalities for the existing catalogue.
The generic constructor contract supplies the unbounded internal execution.
This occurrence follows the constructor ending at control433.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor433254
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
open ArithmeticControlSourceRank254 (literal_target cached_target)

/-- The next actual AX implication constructor starts at control433. -/
def entry : Control := ⟨433, by decide⟩
/-- Its zero-tag exit is the next constructor, at control460. -/
def exit : Control := ⟨460, by decide⟩

private def c434 : Control := ⟨434, by decide⟩
private def c435 : Control := ⟨435, by decide⟩
private def c436 : Control := ⟨436, by decide⟩
private def c437 : Control := ⟨437, by decide⟩
private def c438 : Control := ⟨438, by decide⟩
private def c439 : Control := ⟨439, by decide⟩
private def c440 : Control := ⟨440, by decide⟩
private def c441 : Control := ⟨441, by decide⟩
private def c442 : Control := ⟨442, by decide⟩
private def c443 : Control := ⟨443, by decide⟩
private def c444 : Control := ⟨444, by decide⟩
private def c445 : Control := ⟨445, by decide⟩
private def c446 : Control := ⟨446, by decide⟩
private def c447 : Control := ⟨447, by decide⟩
private def c448 : Control := ⟨448, by decide⟩
private def c449 : Control := ⟨449, by decide⟩
private def c450 : Control := ⟨450, by decide⟩
private def c451 : Control := ⟨451, by decide⟩
private def c452 : Control := ⟨452, by decide⟩
private def c453 : Control := ⟨453, by decide⟩
private def c454 : Control := ⟨454, by decide⟩
private def c455 : Control := ⟨455, by decide⟩
private def c456 : Control := ⟨456, by decide⟩
private def c457 : Control := ⟨457, by decide⟩
private def c458 : Control := ⟨458, by decide⟩
private def c459 : Control := ⟨459, by decide⟩

/-- Cache each complete catalogue equality before checking finite paths. -/
private theorem source_433 :
    source entry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, false], .decnz 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_434 :
    source c434 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, false], .inc 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_435 :
    source c435 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false], .decnz 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_436 :
    source c436 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true], .brk 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_437 :
    source c437 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false], .decnz 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_438 :
    source c438 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, true, false], .inc 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_439 :
    source c439 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, true, true], .cont 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_440 :
    source c440 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, true], .cont 3) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_441 :
    source c441 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, true, false], .decnz 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_442 :
    source c442 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, true, true, false], .inc 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_443 :
    source c443 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, true, true, true], .cont 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_444 :
    source c444 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, false], .decnz 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_445 :
    source c445 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, false], .inc 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_446 :
    source c446 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, false], .inc 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_447 :
    source c447 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true], .cont 3) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_448 :
    source c448 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, false], .decnz 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_449 :
    source c449 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, false], .inc 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_450 :
    source c450 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, true, false], .decnz 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_451 :
    source c451 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_452 :
    source c452 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true], .cont 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_453 :
    source c453 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, true], .cont 3) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_454 :
    source c454 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, false], .decnz 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_455 :
    source c455 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, false, false, false], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_456 :
    source c456 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, false, false, true], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_457 :
    source c457 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, false, true, false], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_458 :
    source c458 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, false, true, true], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_459 :
    source c459 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, true], .cont 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_460 :
    source exit =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, false], .decnz 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

theorem entry_source : (source entry).2 = .decnz 2 := congrArg Prod.snd source_433
theorem exit_source : (source exit).2 = .decnz 2 := congrArg Prod.snd source_460

private def impPop : UnpairCoreShape where
  readEntry := entry
  bodyIncS2 := c434
  bodyTestS1 := c435
  bodyBreak := c436
  bodyMoveTest := c437
  bodyMoveInc := c438
  bodyMoveContinue := c439
  bodyContinue := c440
  restoreMainTest := c441
  restoreMainInc := c442
  restoreMainContinue := c443
  exit := c444
  mainLogical := 2
  mainIndex := wsReg
  main_physical := rfl
  main_ne_s1 := by decide
  main_ne_s2 := by decide
  read_edge := congrArg Prod.snd source_433
  body_inc_edge := congrArg Prod.snd source_434
  body_test_edge := congrArg Prod.snd source_435
  body_break_edge := congrArg Prod.snd source_436
  body_move_test_edge := congrArg Prod.snd source_437
  body_move_inc_edge := congrArg Prod.snd source_438
  body_move_continue_edge := congrArg Prod.snd source_439
  body_continue_edge := congrArg Prod.snd source_440
  restore_test_edge := congrArg Prod.snd source_441
  restore_inc_edge := congrArg Prod.snd source_442
  restore_continue_edge := congrArg Prod.snd source_443
  next_read_positive := cached_target source_433 source_434 incPath (by rfl) (by rfl)
  next_read_zero := cached_target source_433 source_441 (breakPath 1) (by rfl) (by rfl)
  next_body_inc := cached_target source_434 source_435 incPath (by rfl) (by rfl)
  next_body_test_positive := cached_target source_435 source_436 incPath (by rfl) (by rfl)
  next_body_test_zero := cached_target source_435 source_437 (breakPath 1) (by rfl) (by rfl)
  next_body_break := cached_target source_436 source_440 (breakPath 1) (by rfl) (by rfl)
  next_body_move_positive := cached_target source_437 source_438 incPath (by rfl) (by rfl)
  next_body_move_inc := cached_target source_438 source_439 incPath (by rfl) (by rfl)
  next_body_move_continue := cached_target source_439 source_437 (continuePath 2) (by rfl) (by rfl)
  next_body_move_zero := cached_target source_437 source_440 (breakPath 1) (by rfl) (by rfl)
  next_body_continue := cached_target source_440 source_433 (continuePath 3) (by rfl) (by rfl)
  next_restore_main_positive := cached_target source_441 source_442 incPath (by rfl) (by rfl)
  next_restore_main_inc := cached_target source_442 source_443 incPath (by rfl) (by rfl)
  next_restore_main_continue := cached_target source_443 source_441 (continuePath 2) (by rfl) (by rfl)
  next_restore_main_zero := cached_target source_441 source_444 (breakPath 1) (by rfl) (by rfl)

private def impCopy : CopyShape where
  test := c444
  firstInc := c445
  secondInc := c446
  again := c447
  exit := c448
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
  test_edge := congrArg Prod.snd source_444
  first_edge := congrArg Prod.snd source_445
  second_edge := congrArg Prod.snd source_446
  again_edge := congrArg Prod.snd source_447
  positive_target := cached_target source_444 source_445 incPath (by rfl) (by rfl)
  first_target := cached_target source_445 source_446 incPath (by rfl) (by rfl)
  second_target := cached_target source_446 source_447 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_447 source_444 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_444 source_448 (breakPath 1) (by rfl) (by rfl)

private def impMove : MoveShape where
  test := c450
  increment := c451
  again := c452
  exit := c453
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_450
  increment_edge := congrArg Prod.snd source_451
  again_edge := congrArg Prod.snd source_452
  positive_target := cached_target source_450 source_451 incPath (by rfl) (by rfl)
  increment_target := cached_target source_451 source_452 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_452 source_450 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_450 source_453 (breakPath 1) (by rfl) (by rfl)

private def impPair : PairShape where
  copy := impCopy
  testS1 := c448
  incS2 := c449
  move := impMove
  again := c453
  exit := c454
  copy_source := by rfl
  copy_first := by rfl
  copy_second := by rfl
  copy_exit := by rfl
  move_source := by rfl
  move_target := by rfl
  move_exit := by rfl
  test_edge := congrArg Prod.snd source_448
  increment_edge := congrArg Prod.snd source_449
  again_edge := congrArg Prod.snd source_453
  positive_target := cached_target source_448 source_449 incPath (by rfl) (by rfl)
  zero_target := cached_target source_448 source_454 (breakPath 1) (by rfl) (by rfl)
  increment_target := cached_target source_449 source_450 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_453 source_444 (continuePath 3) (by rfl) (by rfl)

private def impScale : Scale4Shape where
  test := c454
  inc1 := c455
  inc2 := c456
  inc3 := c457
  inc4 := c458
  again := c459
  exit := exit
  test_edge := congrArg Prod.snd source_454
  inc1_edge := congrArg Prod.snd source_455
  inc2_edge := congrArg Prod.snd source_456
  inc3_edge := congrArg Prod.snd source_457
  inc4_edge := congrArg Prod.snd source_458
  again_edge := congrArg Prod.snd source_459
  positive_target := cached_target source_454 source_455 incPath (by rfl) (by rfl)
  zero_target := cached_target source_454 source_460 (breakPath 1) (by rfl) (by rfl)
  next_inc1 := cached_target source_455 source_456 incPath (by rfl) (by rfl)
  next_inc2 := cached_target source_456 source_457 incPath (by rfl) (by rfl)
  next_inc3 := cached_target source_457 source_458 incPath (by rfl) (by rfl)
  next_inc4 := cached_target source_458 source_459 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_459 source_454 (continuePath 2) (by rfl) (by rfl)

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

/-- Actual433→460 has the complete implication-constructor file effect. -/
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
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor433254

import BusyBeaver.ZFC.ArithmeticControlConstructor254
import BusyBeaver.ZFC.ArithmeticControlSourceRank254

set_option autoImplicit false
noncomputable section

/-!
Actual AX implication constructor at controls460→487. All 27 instruction edges
and 35 successor branches reuse cached full equalities for the existing catalogue.
The generic constructor contract supplies the unbounded internal execution.
This occurrence follows the constructor ending at control460.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor460254
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

/-- The next actual AX implication constructor starts at control460. -/
def entry : Control := ⟨460, by decide⟩
/-- Its zero-tag exit is the actual TW decrement at control487. -/
def exit : Control := ⟨487, by decide⟩

private def c461 : Control := ⟨461, by decide⟩
private def c462 : Control := ⟨462, by decide⟩
private def c463 : Control := ⟨463, by decide⟩
private def c464 : Control := ⟨464, by decide⟩
private def c465 : Control := ⟨465, by decide⟩
private def c466 : Control := ⟨466, by decide⟩
private def c467 : Control := ⟨467, by decide⟩
private def c468 : Control := ⟨468, by decide⟩
private def c469 : Control := ⟨469, by decide⟩
private def c470 : Control := ⟨470, by decide⟩
private def c471 : Control := ⟨471, by decide⟩
private def c472 : Control := ⟨472, by decide⟩
private def c473 : Control := ⟨473, by decide⟩
private def c474 : Control := ⟨474, by decide⟩
private def c475 : Control := ⟨475, by decide⟩
private def c476 : Control := ⟨476, by decide⟩
private def c477 : Control := ⟨477, by decide⟩
private def c478 : Control := ⟨478, by decide⟩
private def c479 : Control := ⟨479, by decide⟩
private def c480 : Control := ⟨480, by decide⟩
private def c481 : Control := ⟨481, by decide⟩
private def c482 : Control := ⟨482, by decide⟩
private def c483 : Control := ⟨483, by decide⟩
private def c484 : Control := ⟨484, by decide⟩
private def c485 : Control := ⟨485, by decide⟩
private def c486 : Control := ⟨486, by decide⟩

/-- Cache each complete catalogue equality before checking finite paths. -/
private theorem source_460 :
    source entry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, false], .decnz 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_461 :
    source c461 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, false], .inc 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_462 :
    source c462 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, true, false, false, false], .decnz 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_463 :
    source c463 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, true, false, false, true], .brk 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_464 :
    source c464 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, true, false, true, false], .decnz 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_465 :
    source c465 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, true, false, true, true, false], .inc 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_466 :
    source c466 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, true, false, true, true, true], .cont 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_467 :
    source c467 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, true, true, true], .cont 3) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_468 :
    source c468 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, true, false], .decnz 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_469 :
    source c469 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, true, true, false], .inc 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_470 :
    source c470 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, true, true, true], .cont 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_471 :
    source c471 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, false, false], .decnz 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_472 :
    source c472 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, false, true, false], .inc 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_473 :
    source c473 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, false, true, true, false], .inc 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_474 :
    source c474 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, false, true, true, true], .cont 3) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_475 :
    source c475 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, true, false], .decnz 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_476 :
    source c476 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, true, true, false, false], .inc 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_477 :
    source c477 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, true, true, false, true, false], .decnz 6) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_478 :
    source c478 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, true, true, false, true, true, false], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_479 :
    source c479 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, true, true, false, true, true, true], .cont 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_480 :
    source c480 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true], .cont 3) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_481 :
    source c481 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, true, false], .decnz 7) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_482 :
    source c482 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, true, true, false, false, false], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_483 :
    source c483 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, true, true, false, false, true], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_484 :
    source c484 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, true, true, false, true, false], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_485 :
    source c485 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, true, true, false, true, true], .inc 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_486 :
    source c486 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, true, true, true], .cont 2) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

private theorem source_487 :
    source exit =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, false, false, false, false], .decnz 1) :=
  ArithmeticControlSourceRank254.source_of_path (by rfl) (by rfl)

theorem entry_source : (source entry).2 = .decnz 2 := congrArg Prod.snd source_460
theorem exit_source : (source exit).2 = .decnz 1 := congrArg Prod.snd source_487

private def impPop : UnpairCoreShape where
  readEntry := entry
  bodyIncS2 := c461
  bodyTestS1 := c462
  bodyBreak := c463
  bodyMoveTest := c464
  bodyMoveInc := c465
  bodyMoveContinue := c466
  bodyContinue := c467
  restoreMainTest := c468
  restoreMainInc := c469
  restoreMainContinue := c470
  exit := c471
  mainLogical := 2
  mainIndex := wsReg
  main_physical := rfl
  main_ne_s1 := by decide
  main_ne_s2 := by decide
  read_edge := congrArg Prod.snd source_460
  body_inc_edge := congrArg Prod.snd source_461
  body_test_edge := congrArg Prod.snd source_462
  body_break_edge := congrArg Prod.snd source_463
  body_move_test_edge := congrArg Prod.snd source_464
  body_move_inc_edge := congrArg Prod.snd source_465
  body_move_continue_edge := congrArg Prod.snd source_466
  body_continue_edge := congrArg Prod.snd source_467
  restore_test_edge := congrArg Prod.snd source_468
  restore_inc_edge := congrArg Prod.snd source_469
  restore_continue_edge := congrArg Prod.snd source_470
  next_read_positive := cached_target source_460 source_461 incPath (by rfl) (by rfl)
  next_read_zero := cached_target source_460 source_468 (breakPath 1) (by rfl) (by rfl)
  next_body_inc := cached_target source_461 source_462 incPath (by rfl) (by rfl)
  next_body_test_positive := cached_target source_462 source_463 incPath (by rfl) (by rfl)
  next_body_test_zero := cached_target source_462 source_464 (breakPath 1) (by rfl) (by rfl)
  next_body_break := cached_target source_463 source_467 (breakPath 1) (by rfl) (by rfl)
  next_body_move_positive := cached_target source_464 source_465 incPath (by rfl) (by rfl)
  next_body_move_inc := cached_target source_465 source_466 incPath (by rfl) (by rfl)
  next_body_move_continue := cached_target source_466 source_464 (continuePath 2) (by rfl) (by rfl)
  next_body_move_zero := cached_target source_464 source_467 (breakPath 1) (by rfl) (by rfl)
  next_body_continue := cached_target source_467 source_460 (continuePath 3) (by rfl) (by rfl)
  next_restore_main_positive := cached_target source_468 source_469 incPath (by rfl) (by rfl)
  next_restore_main_inc := cached_target source_469 source_470 incPath (by rfl) (by rfl)
  next_restore_main_continue := cached_target source_470 source_468 (continuePath 2) (by rfl) (by rfl)
  next_restore_main_zero := cached_target source_468 source_471 (breakPath 1) (by rfl) (by rfl)

private def impCopy : CopyShape where
  test := c471
  firstInc := c472
  secondInc := c473
  again := c474
  exit := c475
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
  test_edge := congrArg Prod.snd source_471
  first_edge := congrArg Prod.snd source_472
  second_edge := congrArg Prod.snd source_473
  again_edge := congrArg Prod.snd source_474
  positive_target := cached_target source_471 source_472 incPath (by rfl) (by rfl)
  first_target := cached_target source_472 source_473 incPath (by rfl) (by rfl)
  second_target := cached_target source_473 source_474 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_474 source_471 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_471 source_475 (breakPath 1) (by rfl) (by rfl)

private def impMove : MoveShape where
  test := c477
  increment := c478
  again := c479
  exit := c480
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_477
  increment_edge := congrArg Prod.snd source_478
  again_edge := congrArg Prod.snd source_479
  positive_target := cached_target source_477 source_478 incPath (by rfl) (by rfl)
  increment_target := cached_target source_478 source_479 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_479 source_477 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_477 source_480 (breakPath 1) (by rfl) (by rfl)

private def impPair : PairShape where
  copy := impCopy
  testS1 := c475
  incS2 := c476
  move := impMove
  again := c480
  exit := c481
  copy_source := by rfl
  copy_first := by rfl
  copy_second := by rfl
  copy_exit := by rfl
  move_source := by rfl
  move_target := by rfl
  move_exit := by rfl
  test_edge := congrArg Prod.snd source_475
  increment_edge := congrArg Prod.snd source_476
  again_edge := congrArg Prod.snd source_480
  positive_target := cached_target source_475 source_476 incPath (by rfl) (by rfl)
  zero_target := cached_target source_475 source_481 (breakPath 1) (by rfl) (by rfl)
  increment_target := cached_target source_476 source_477 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_480 source_471 (continuePath 3) (by rfl) (by rfl)

private def impScale : Scale4Shape where
  test := c481
  inc1 := c482
  inc2 := c483
  inc3 := c484
  inc4 := c485
  again := c486
  exit := exit
  test_edge := congrArg Prod.snd source_481
  inc1_edge := congrArg Prod.snd source_482
  inc2_edge := congrArg Prod.snd source_483
  inc3_edge := congrArg Prod.snd source_484
  inc4_edge := congrArg Prod.snd source_485
  again_edge := congrArg Prod.snd source_486
  positive_target := cached_target source_481 source_482 incPath (by rfl) (by rfl)
  zero_target := cached_target source_481 source_487 (breakPath 1) (by rfl) (by rfl)
  next_inc1 := cached_target source_482 source_483 incPath (by rfl) (by rfl)
  next_inc2 := cached_target source_483 source_484 incPath (by rfl) (by rfl)
  next_inc3 := cached_target source_484 source_485 incPath (by rfl) (by rfl)
  next_inc4 := cached_target source_485 source_486 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_486 source_481 (continuePath 2) (by rfl) (by rfl)

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

/-- Actual460→487 has the complete implication-constructor file effect. -/
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
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor460254

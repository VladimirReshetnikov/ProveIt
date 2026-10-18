import BusyBeaver.ZFC.ArithmeticControlCopyBack254

set_option autoImplicit false
noncomputable section

/-!
Actual AC push380→406. All26 instruction edges and34 successor branches are
bound to the literal catalogue. Generic CopyBack and Push contracts give the
unbounded internal execution. The next constructor is a separate occurrence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextACPush254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlCopyBack254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlUnpair254 (wsReg)
open FiniteControlTable254 RegisterPath

def entry : Control := ⟨380, by decide⟩
def copyEntry : Control := ⟨399, by decide⟩
def exit : Control := ⟨406, by decide⟩
private def c381 : Control := ⟨381, by decide⟩
private def c382 : Control := ⟨382, by decide⟩
private def c383 : Control := ⟨383, by decide⟩
private def c384 : Control := ⟨384, by decide⟩
private def c385 : Control := ⟨385, by decide⟩
private def c386 : Control := ⟨386, by decide⟩
private def c387 : Control := ⟨387, by decide⟩
private def c388 : Control := ⟨388, by decide⟩
private def c389 : Control := ⟨389, by decide⟩
private def c390 : Control := ⟨390, by decide⟩
private def c391 : Control := ⟨391, by decide⟩
private def c392 : Control := ⟨392, by decide⟩
private def c393 : Control := ⟨393, by decide⟩
private def c394 : Control := ⟨394, by decide⟩
private def c395 : Control := ⟨395, by decide⟩
private def c396 : Control := ⟨396, by decide⟩
private def c397 : Control := ⟨397, by decide⟩
private def c398 : Control := ⟨398, by decide⟩
private def c400 : Control := ⟨400, by decide⟩
private def c401 : Control := ⟨401, by decide⟩
private def c402 : Control := ⟨402, by decide⟩
private def c403 : Control := ⟨403, by decide⟩
private def c404 : Control := ⟨404, by decide⟩
private def c405 : Control := ⟨405, by decide⟩

/-- Compute each complete catalogue source once, then reuse the proved equality. -/
private theorem source_380 :
    source entry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, false, false], .decnz 1) := by rfl

private theorem source_381 :
    source c381 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, false, true, false], .inc 6) := by rfl

private theorem source_382 :
    source c382 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, false, true, true], .cont 2) := by rfl

private theorem source_383 :
    source c383 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false, false], .decnz 2) := by rfl

private theorem source_384 :
    source c384 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false, true, false], .inc 1) := by rfl

private theorem source_385 :
    source c385 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false, true, true], .cont 2) := by rfl

private theorem source_386 :
    source c386 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, false, false], .decnz 1) := by rfl

private theorem source_387 :
    source c387 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, false, true, false], .inc 7) := by rfl

private theorem source_388 :
    source c388 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, false, true, true, false], .inc 6) := by rfl

private theorem source_389 :
    source c389 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, false, true, true, true], .cont 3) := by rfl

private theorem source_390 :
    source c390 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false], .decnz 6) := by rfl

private theorem source_391 :
    source c391 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false, false], .inc 7) := by rfl

private theorem source_392 :
    source c392 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false], .decnz 6) := by rfl

private theorem source_393 :
    source c393 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false], .inc 1) := by rfl

private theorem source_394 :
    source c394 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true], .cont 2) := by rfl

private theorem source_395 :
    source c395 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, true], .cont 3) := by rfl

private theorem source_396 :
    source c396 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true, false], .decnz 7) := by rfl

private theorem source_397 :
    source c397 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, false], .inc 2) := by rfl

private theorem source_398 :
    source c398 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, true], .cont 2) := by rfl

private theorem source_399 :
    source copyEntry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false], .decnz 3) := by rfl

private theorem source_400 :
    source c400 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, true, false], .inc 1) := by rfl

private theorem source_401 :
    source c401 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, true, true, false], .inc 6) := by rfl

private theorem source_402 :
    source c402 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, true, true, true], .cont 3) := by rfl

private theorem source_403 :
    source c403 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, true, false], .decnz 6) := by rfl

private theorem source_404 :
    source c404 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, true, true, false], .inc 3) := by rfl

private theorem source_405 :
    source c405 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, true, true, true, true], .cont 2) := by rfl

private theorem source_406 :
    source exit =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, false, false], .decnz 2) := by rfl

theorem entry_source : (source entry).2 = .decnz 1 := congrArg Prod.snd source_380
theorem copyEntry_source : (source copyEntry).2 = .decnz 3 := congrArg Prod.snd source_399
theorem exit_source : (source exit).2 = .decnz 2 := congrArg Prod.snd source_406

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

/-- Rewrite only abstract source equalities before checking the finite path. -/
private theorem cached_target {a b : Control} {P Q : List Bool} {e f : Edge}
    (ha : source a = (P, e)) (hb : source b = (Q, f))
    (next : List Bool → List Bool)
    (hw : RMBisim.twalk ActualTree254.tree (next P) 0 = some (f, Q.length))
    (hc : consume (next P) Q.length = Q) :
    resolveControl (next (source a).1) = b := by
  rw [ha]
  apply literal_target
  · simpa only [hb] using hw
  · simpa only [hb] using hc

private def topToScratch : MoveShape where
  test := entry
  increment := c381
  again := c382
  exit := c383
  sourceLogical := 1
  targetLogical := 6
  sourceIndex := twReg
  targetIndex := s1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_380
  increment_edge := congrArg Prod.snd source_381
  again_edge := congrArg Prod.snd source_382
  positive_target := cached_target source_380 source_381 incPath (by rfl) (by rfl)
  increment_target := cached_target source_381 source_382 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_382 source_380 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_380 source_383 (breakPath 1) (by rfl) (by rfl)

private def stackToTop : MoveShape where
  test := c383
  increment := c384
  again := c385
  exit := c386
  sourceLogical := 2
  targetLogical := 1
  sourceIndex := wsReg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_383
  increment_edge := congrArg Prod.snd source_384
  again_edge := congrArg Prod.snd source_385
  positive_target := cached_target source_383 source_384 incPath (by rfl) (by rfl)
  increment_target := cached_target source_384 source_385 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_385 source_383 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_383 source_386 (breakPath 1) (by rfl) (by rfl)

private def pairCopy : CopyShape where
  test := c386
  firstInc := c387
  secondInc := c388
  again := c389
  exit := c390
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
  test_edge := congrArg Prod.snd source_386
  first_edge := congrArg Prod.snd source_387
  second_edge := congrArg Prod.snd source_388
  again_edge := congrArg Prod.snd source_389
  positive_target := cached_target source_386 source_387 incPath (by rfl) (by rfl)
  first_target := cached_target source_387 source_388 incPath (by rfl) (by rfl)
  second_target := cached_target source_388 source_389 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_389 source_386 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_386 source_390 (breakPath 1) (by rfl) (by rfl)

private def pairMove : MoveShape where
  test := c392
  increment := c393
  again := c394
  exit := c395
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_392
  increment_edge := congrArg Prod.snd source_393
  again_edge := congrArg Prod.snd source_394
  positive_target := cached_target source_392 source_393 incPath (by rfl) (by rfl)
  increment_target := cached_target source_393 source_394 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_394 source_392 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_392 source_395 (breakPath 1) (by rfl) (by rfl)

private def pairing : PairShape where
  copy := pairCopy
  testS1 := c390
  incS2 := c391
  move := pairMove
  again := c395
  exit := c396
  copy_source := by rfl
  copy_first := by rfl
  copy_second := by rfl
  copy_exit := by rfl
  move_source := by rfl
  move_target := by rfl
  move_exit := by rfl
  test_edge := congrArg Prod.snd source_390
  increment_edge := congrArg Prod.snd source_391
  again_edge := congrArg Prod.snd source_395
  positive_target := cached_target source_390 source_391 incPath (by rfl) (by rfl)
  zero_target := cached_target source_390 source_396 (breakPath 1) (by rfl) (by rfl)
  increment_target := cached_target source_391 source_392 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_395 source_386 (continuePath 3) (by rfl) (by rfl)

private def pairOutput : MoveShape where
  test := c396
  increment := c397
  again := c398
  exit := copyEntry
  sourceLogical := 7
  targetLogical := 2
  sourceIndex := s2Reg
  targetIndex := wsReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_396
  increment_edge := congrArg Prod.snd source_397
  again_edge := congrArg Prod.snd source_398
  positive_target := cached_target source_396 source_397 incPath (by rfl) (by rfl)
  increment_target := cached_target source_397 source_398 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_398 source_396 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_396 source_399 (breakPath 1) (by rfl) (by rfl)

private def argumentCopy : CopyShape where
  test := copyEntry
  firstInc := c400
  secondInc := c401
  again := c402
  exit := c403
  sourceLogical := 3
  firstLogical := 1
  secondLogical := 6
  sourceIndex := acReg
  firstIndex := twReg
  secondIndex := s1Reg
  source_physical := rfl
  first_physical := rfl
  second_physical := rfl
  source_ne_first := by decide
  source_ne_second := by decide
  first_ne_second := by decide
  test_edge := congrArg Prod.snd source_399
  first_edge := congrArg Prod.snd source_400
  second_edge := congrArg Prod.snd source_401
  again_edge := congrArg Prod.snd source_402
  positive_target := cached_target source_399 source_400 incPath (by rfl) (by rfl)
  first_target := cached_target source_400 source_401 incPath (by rfl) (by rfl)
  second_target := cached_target source_401 source_402 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_402 source_399 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_399 source_403 (breakPath 1) (by rfl) (by rfl)

private def argumentRestore : MoveShape where
  test := c403
  increment := c404
  again := c405
  exit := exit
  sourceLogical := 6
  targetLogical := 3
  sourceIndex := s1Reg
  targetIndex := acReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_403
  increment_edge := congrArg Prod.snd source_404
  again_edge := congrArg Prod.snd source_405
  positive_target := cached_target source_403 source_404 incPath (by rfl) (by rfl)
  increment_target := cached_target source_404 source_405 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_405 source_403 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_403 source_406 (breakPath 1) (by rfl) (by rfl)

private def initialPush : PushShape where
  first := topToScratch
  second := stackToTop
  pairing := pairing
  output := pairOutput
  first_source := rfl
  first_target := rfl
  second_source := rfl
  second_target := rfl
  output_source := rfl
  output_target := rfl
  first_exit := rfl
  second_exit := rfl
  pair_exit := rfl

private def argumentCopyBack : CopyBackShape where
  copy := argumentCopy
  restore := argumentRestore
  first_target := rfl
  second_target := rfl
  restore_source := rfl
  restore_target := rfl
  join := rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- All coordinates except TW and WS are retained. -/
theorem acPushFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (argumentPushFile acReg file) i = regValue file i :=
  argumentPushFile_other acReg i file ht hs

/-- Copy/restore tail399→406, for arbitrary TW and only S1=0. -/
theorem copy_tail_run (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file acReg + 2) (liveValue (number copyEntry : V) file) =
      liveValue (number exit : V)
        (put twReg (regValue file twReg + regValue file acReg) file) := by
  simpa only [show argumentCopyBack.copy.sourceIndex = acReg from rfl,
    show argumentCopyBack.copy.test = copyEntry from rfl,
    show argumentCopyBack.restore.exit = exit from rfl] using
      copy_back_run argumentCopyBack file h1

/-- Actual380→406, with positive internal clock and the complete file effect. -/
theorem ac_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number exit : V) (argumentPushFile acReg file) := by
  exact argument_push_run initialPush argumentCopyBack rfl (by decide) file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextACPush254

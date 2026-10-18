import BusyBeaver.ZFC.ArithmeticControlCopyBack254

set_option autoImplicit false
noncomputable section

/-!
Actual P2/cache push354→380 (logical5, physical7). All26 instruction edges and34 successor branches are
bound to the literal catalogue. Generic CopyBack and Push contracts give the
unbounded internal execution. The following AC push is a separate occurrence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextCachePush254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlCopyBack254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlDispatch254 (cacheReg)
open ArithmeticControlUnpair254 (wsReg)
open FiniteControlTable254 RegisterPath

def entry : Control := ⟨354, by decide⟩
def copyEntry : Control := ⟨373, by decide⟩
def exit : Control := ⟨380, by decide⟩
private def c355 : Control := ⟨355, by decide⟩
private def c356 : Control := ⟨356, by decide⟩
private def c357 : Control := ⟨357, by decide⟩
private def c358 : Control := ⟨358, by decide⟩
private def c359 : Control := ⟨359, by decide⟩
private def c360 : Control := ⟨360, by decide⟩
private def c361 : Control := ⟨361, by decide⟩
private def c362 : Control := ⟨362, by decide⟩
private def c363 : Control := ⟨363, by decide⟩
private def c364 : Control := ⟨364, by decide⟩
private def c365 : Control := ⟨365, by decide⟩
private def c366 : Control := ⟨366, by decide⟩
private def c367 : Control := ⟨367, by decide⟩
private def c368 : Control := ⟨368, by decide⟩
private def c369 : Control := ⟨369, by decide⟩
private def c370 : Control := ⟨370, by decide⟩
private def c371 : Control := ⟨371, by decide⟩
private def c372 : Control := ⟨372, by decide⟩
private def c374 : Control := ⟨374, by decide⟩
private def c375 : Control := ⟨375, by decide⟩
private def c376 : Control := ⟨376, by decide⟩
private def c377 : Control := ⟨377, by decide⟩
private def c378 : Control := ⟨378, by decide⟩
private def c379 : Control := ⟨379, by decide⟩

/-- Compute each complete catalogue source once, then reuse the proved equality. -/
private theorem source_354 :
    source entry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, false, false], .decnz 1) := by rfl

private theorem source_355 :
    source c355 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, false, true, false], .inc 6) := by rfl

private theorem source_356 :
    source c356 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, false, true, true], .cont 2) := by rfl

private theorem source_357 :
    source c357 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, false, false], .decnz 2) := by rfl

private theorem source_358 :
    source c358 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, false, true, false], .inc 1) := by rfl

private theorem source_359 :
    source c359 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, false, true, true], .cont 2) := by rfl

private theorem source_360 :
    source c360 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, false, false], .decnz 1) := by rfl

private theorem source_361 :
    source c361 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, false, true, false], .inc 7) := by rfl

private theorem source_362 :
    source c362 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, false, true, true, false], .inc 6) := by rfl

private theorem source_363 :
    source c363 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, false, true, true, true], .cont 3) := by rfl

private theorem source_364 :
    source c364 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, true, false], .decnz 6) := by rfl

private theorem source_365 :
    source c365 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, true, true, false, false], .inc 7) := by rfl

private theorem source_366 :
    source c366 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, true, true, false, true, false], .decnz 6) := by rfl

private theorem source_367 :
    source c367 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, true, true, false, true, true, false], .inc 1) := by rfl

private theorem source_368 :
    source c368 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, true, true, false, true, true, true], .cont 2) := by rfl

private theorem source_369 :
    source c369 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false, true, true, true], .cont 3) := by rfl

private theorem source_370 :
    source c370 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, true, false], .decnz 7) := by rfl

private theorem source_371 :
    source c371 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, true, true, false], .inc 2) := by rfl

private theorem source_372 :
    source c372 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, true, true, true, true], .cont 2) := by rfl

private theorem source_373 :
    source copyEntry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, false, false], .decnz 5) := by rfl

private theorem source_374 :
    source c374 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, false, true, false], .inc 1) := by rfl

private theorem source_375 :
    source c375 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, false, true, true, false], .inc 6) := by rfl

private theorem source_376 :
    source c376 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, false, true, true, true], .cont 3) := by rfl

private theorem source_377 :
    source c377 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, false], .decnz 6) := by rfl

private theorem source_378 :
    source c378 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, true, false], .inc 5) := by rfl

private theorem source_379 :
    source c379 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, true, true], .cont 2) := by rfl

private theorem source_380 :
    source exit =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, false, false], .decnz 1) := by rfl

theorem entry_source : (source entry).2 = .decnz 1 := congrArg Prod.snd source_354
theorem copyEntry_source : (source copyEntry).2 = .decnz 5 := congrArg Prod.snd source_373
theorem exit_source : (source exit).2 = .decnz 1 := congrArg Prod.snd source_380

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
  increment := c355
  again := c356
  exit := c357
  sourceLogical := 1
  targetLogical := 6
  sourceIndex := twReg
  targetIndex := s1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_354
  increment_edge := congrArg Prod.snd source_355
  again_edge := congrArg Prod.snd source_356
  positive_target := cached_target source_354 source_355 incPath (by rfl) (by rfl)
  increment_target := cached_target source_355 source_356 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_356 source_354 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_354 source_357 (breakPath 1) (by rfl) (by rfl)

private def stackToTop : MoveShape where
  test := c357
  increment := c358
  again := c359
  exit := c360
  sourceLogical := 2
  targetLogical := 1
  sourceIndex := wsReg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_357
  increment_edge := congrArg Prod.snd source_358
  again_edge := congrArg Prod.snd source_359
  positive_target := cached_target source_357 source_358 incPath (by rfl) (by rfl)
  increment_target := cached_target source_358 source_359 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_359 source_357 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_357 source_360 (breakPath 1) (by rfl) (by rfl)

private def pairCopy : CopyShape where
  test := c360
  firstInc := c361
  secondInc := c362
  again := c363
  exit := c364
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
  test_edge := congrArg Prod.snd source_360
  first_edge := congrArg Prod.snd source_361
  second_edge := congrArg Prod.snd source_362
  again_edge := congrArg Prod.snd source_363
  positive_target := cached_target source_360 source_361 incPath (by rfl) (by rfl)
  first_target := cached_target source_361 source_362 incPath (by rfl) (by rfl)
  second_target := cached_target source_362 source_363 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_363 source_360 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_360 source_364 (breakPath 1) (by rfl) (by rfl)

private def pairMove : MoveShape where
  test := c366
  increment := c367
  again := c368
  exit := c369
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_366
  increment_edge := congrArg Prod.snd source_367
  again_edge := congrArg Prod.snd source_368
  positive_target := cached_target source_366 source_367 incPath (by rfl) (by rfl)
  increment_target := cached_target source_367 source_368 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_368 source_366 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_366 source_369 (breakPath 1) (by rfl) (by rfl)

private def pairing : PairShape where
  copy := pairCopy
  testS1 := c364
  incS2 := c365
  move := pairMove
  again := c369
  exit := c370
  copy_source := by rfl
  copy_first := by rfl
  copy_second := by rfl
  copy_exit := by rfl
  move_source := by rfl
  move_target := by rfl
  move_exit := by rfl
  test_edge := congrArg Prod.snd source_364
  increment_edge := congrArg Prod.snd source_365
  again_edge := congrArg Prod.snd source_369
  positive_target := cached_target source_364 source_365 incPath (by rfl) (by rfl)
  zero_target := cached_target source_364 source_370 (breakPath 1) (by rfl) (by rfl)
  increment_target := cached_target source_365 source_366 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_369 source_360 (continuePath 3) (by rfl) (by rfl)

private def pairOutput : MoveShape where
  test := c370
  increment := c371
  again := c372
  exit := copyEntry
  sourceLogical := 7
  targetLogical := 2
  sourceIndex := s2Reg
  targetIndex := wsReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_370
  increment_edge := congrArg Prod.snd source_371
  again_edge := congrArg Prod.snd source_372
  positive_target := cached_target source_370 source_371 incPath (by rfl) (by rfl)
  increment_target := cached_target source_371 source_372 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_372 source_370 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_370 source_373 (breakPath 1) (by rfl) (by rfl)

private def argumentCopy : CopyShape where
  test := copyEntry
  firstInc := c374
  secondInc := c375
  again := c376
  exit := c377
  sourceLogical := 5
  firstLogical := 1
  secondLogical := 6
  sourceIndex := cacheReg
  firstIndex := twReg
  secondIndex := s1Reg
  source_physical := rfl
  first_physical := rfl
  second_physical := rfl
  source_ne_first := by decide
  source_ne_second := by decide
  first_ne_second := by decide
  test_edge := congrArg Prod.snd source_373
  first_edge := congrArg Prod.snd source_374
  second_edge := congrArg Prod.snd source_375
  again_edge := congrArg Prod.snd source_376
  positive_target := cached_target source_373 source_374 incPath (by rfl) (by rfl)
  first_target := cached_target source_374 source_375 incPath (by rfl) (by rfl)
  second_target := cached_target source_375 source_376 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_376 source_373 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_373 source_377 (breakPath 1) (by rfl) (by rfl)

private def argumentRestore : MoveShape where
  test := c377
  increment := c378
  again := c379
  exit := exit
  sourceLogical := 6
  targetLogical := 5
  sourceIndex := s1Reg
  targetIndex := cacheReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_377
  increment_edge := congrArg Prod.snd source_378
  again_edge := congrArg Prod.snd source_379
  positive_target := cached_target source_377 source_378 incPath (by rfl) (by rfl)
  increment_target := cached_target source_378 source_379 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_379 source_377 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_377 source_380 (breakPath 1) (by rfl) (by rfl)

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
theorem cachePushFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (argumentPushFile cacheReg file) i = regValue file i :=
  argumentPushFile_other cacheReg i file ht hs

/-- Copy/restore tail373→380, for arbitrary TW and only S1=0. -/
theorem copy_tail_run (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file cacheReg + 2) (liveValue (number copyEntry : V) file) =
      liveValue (number exit : V)
        (put twReg (regValue file twReg + regValue file cacheReg) file) := by
  simpa only [show argumentCopyBack.copy.sourceIndex = cacheReg from rfl,
    show argumentCopyBack.copy.test = copyEntry from rfl,
    show argumentCopyBack.restore.exit = exit from rfl] using
      copy_back_run argumentCopyBack file h1

/-- Actual354→380, with positive internal clock and the complete file effect. -/
theorem cache_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number exit : V) (argumentPushFile cacheReg file) := by
  exact argument_push_run initialPush argumentCopyBack rfl (by decide) file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextCachePush254

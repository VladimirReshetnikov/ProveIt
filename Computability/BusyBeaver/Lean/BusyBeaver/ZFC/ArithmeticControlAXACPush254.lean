import BusyBeaver.ZFC.ArithmeticControlCopyBack254

set_option autoImplicit false
noncomputable section

/-!
Actual AC push301→327. All26 instruction edges and34 successor branches are
bound to the literal catalogue. Generic CopyBack and Push contracts give the
unbounded internal execution. The next constructor is a separate occurrence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXACPush254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlCopyBack254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlUnpair254 (wsReg)
open FiniteControlTable254 RegisterPath

def entry : Control := ⟨301, by decide⟩
def copyEntry : Control := ⟨320, by decide⟩
def exit : Control := ⟨327, by decide⟩
private def c302 : Control := ⟨302, by decide⟩
private def c303 : Control := ⟨303, by decide⟩
private def c304 : Control := ⟨304, by decide⟩
private def c305 : Control := ⟨305, by decide⟩
private def c306 : Control := ⟨306, by decide⟩
private def c307 : Control := ⟨307, by decide⟩
private def c308 : Control := ⟨308, by decide⟩
private def c309 : Control := ⟨309, by decide⟩
private def c310 : Control := ⟨310, by decide⟩
private def c311 : Control := ⟨311, by decide⟩
private def c312 : Control := ⟨312, by decide⟩
private def c313 : Control := ⟨313, by decide⟩
private def c314 : Control := ⟨314, by decide⟩
private def c315 : Control := ⟨315, by decide⟩
private def c316 : Control := ⟨316, by decide⟩
private def c317 : Control := ⟨317, by decide⟩
private def c318 : Control := ⟨318, by decide⟩
private def c319 : Control := ⟨319, by decide⟩
private def c321 : Control := ⟨321, by decide⟩
private def c322 : Control := ⟨322, by decide⟩
private def c323 : Control := ⟨323, by decide⟩
private def c324 : Control := ⟨324, by decide⟩
private def c325 : Control := ⟨325, by decide⟩
private def c326 : Control := ⟨326, by decide⟩

/-- Compute each complete catalogue source once, then reuse the proved equality. -/
private theorem source_301 :
    source entry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, false, false], .decnz 1) := by rfl

private theorem source_302 :
    source c302 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, false, true, false], .inc 6) := by rfl

private theorem source_303 :
    source c303 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, false, true, true], .cont 2) := by rfl

private theorem source_304 :
    source c304 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, false, false], .decnz 2) := by rfl

private theorem source_305 :
    source c305 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, false, true, false], .inc 1) := by rfl

private theorem source_306 :
    source c306 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, false, true, true], .cont 2) := by rfl

private theorem source_307 :
    source c307 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false], .decnz 1) := by rfl

private theorem source_308 :
    source c308 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false], .inc 7) := by rfl

private theorem source_309 :
    source c309 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false], .inc 6) := by rfl

private theorem source_310 :
    source c310 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true], .cont 3) := by rfl

private theorem source_311 :
    source c311 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false], .decnz 6) := by rfl

private theorem source_312 :
    source c312 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false], .inc 7) := by rfl

private theorem source_313 :
    source c313 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], .decnz 6) := by rfl

private theorem source_314 :
    source c314 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], .inc 1) := by rfl

private theorem source_315 :
    source c315 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], .cont 2) := by rfl

private theorem source_316 :
    source c316 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true], .cont 3) := by rfl

private theorem source_317 :
    source c317 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true, false], .decnz 7) := by rfl

private theorem source_318 :
    source c318 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false], .inc 2) := by rfl

private theorem source_319 :
    source c319 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true], .cont 2) := by rfl

private theorem source_320 :
    source copyEntry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, true, false, false], .decnz 3) := by rfl

private theorem source_321 :
    source c321 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, true, false, true, false], .inc 1) := by rfl

private theorem source_322 :
    source c322 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, true, false, true, true, false], .inc 6) := by rfl

private theorem source_323 :
    source c323 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, true, false, true, true, true], .cont 3) := by rfl

private theorem source_324 :
    source c324 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, true, true, false], .decnz 6) := by rfl

private theorem source_325 :
    source c325 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, true, true, true, false], .inc 3) := by rfl

private theorem source_326 :
    source c326 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, true, true, true, true], .cont 2) := by rfl

private theorem source_327 :
    source exit =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false, false, false], .decnz 2) := by rfl

theorem entry_source : (source entry).2 = .decnz 1 := congrArg Prod.snd source_301
theorem copyEntry_source : (source copyEntry).2 = .decnz 3 := congrArg Prod.snd source_320
theorem exit_source : (source exit).2 = .decnz 2 := congrArg Prod.snd source_327

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
  increment := c302
  again := c303
  exit := c304
  sourceLogical := 1
  targetLogical := 6
  sourceIndex := twReg
  targetIndex := s1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_301
  increment_edge := congrArg Prod.snd source_302
  again_edge := congrArg Prod.snd source_303
  positive_target := cached_target source_301 source_302 incPath (by rfl) (by rfl)
  increment_target := cached_target source_302 source_303 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_303 source_301 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_301 source_304 (breakPath 1) (by rfl) (by rfl)

private def stackToTop : MoveShape where
  test := c304
  increment := c305
  again := c306
  exit := c307
  sourceLogical := 2
  targetLogical := 1
  sourceIndex := wsReg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_304
  increment_edge := congrArg Prod.snd source_305
  again_edge := congrArg Prod.snd source_306
  positive_target := cached_target source_304 source_305 incPath (by rfl) (by rfl)
  increment_target := cached_target source_305 source_306 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_306 source_304 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_304 source_307 (breakPath 1) (by rfl) (by rfl)

private def pairCopy : CopyShape where
  test := c307
  firstInc := c308
  secondInc := c309
  again := c310
  exit := c311
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
  test_edge := congrArg Prod.snd source_307
  first_edge := congrArg Prod.snd source_308
  second_edge := congrArg Prod.snd source_309
  again_edge := congrArg Prod.snd source_310
  positive_target := cached_target source_307 source_308 incPath (by rfl) (by rfl)
  first_target := cached_target source_308 source_309 incPath (by rfl) (by rfl)
  second_target := cached_target source_309 source_310 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_310 source_307 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_307 source_311 (breakPath 1) (by rfl) (by rfl)

private def pairMove : MoveShape where
  test := c313
  increment := c314
  again := c315
  exit := c316
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_313
  increment_edge := congrArg Prod.snd source_314
  again_edge := congrArg Prod.snd source_315
  positive_target := cached_target source_313 source_314 incPath (by rfl) (by rfl)
  increment_target := cached_target source_314 source_315 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_315 source_313 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_313 source_316 (breakPath 1) (by rfl) (by rfl)

private def pairing : PairShape where
  copy := pairCopy
  testS1 := c311
  incS2 := c312
  move := pairMove
  again := c316
  exit := c317
  copy_source := by rfl
  copy_first := by rfl
  copy_second := by rfl
  copy_exit := by rfl
  move_source := by rfl
  move_target := by rfl
  move_exit := by rfl
  test_edge := congrArg Prod.snd source_311
  increment_edge := congrArg Prod.snd source_312
  again_edge := congrArg Prod.snd source_316
  positive_target := cached_target source_311 source_312 incPath (by rfl) (by rfl)
  zero_target := cached_target source_311 source_317 (breakPath 1) (by rfl) (by rfl)
  increment_target := cached_target source_312 source_313 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_316 source_307 (continuePath 3) (by rfl) (by rfl)

private def pairOutput : MoveShape where
  test := c317
  increment := c318
  again := c319
  exit := copyEntry
  sourceLogical := 7
  targetLogical := 2
  sourceIndex := s2Reg
  targetIndex := wsReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_317
  increment_edge := congrArg Prod.snd source_318
  again_edge := congrArg Prod.snd source_319
  positive_target := cached_target source_317 source_318 incPath (by rfl) (by rfl)
  increment_target := cached_target source_318 source_319 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_319 source_317 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_317 source_320 (breakPath 1) (by rfl) (by rfl)

private def argumentCopy : CopyShape where
  test := copyEntry
  firstInc := c321
  secondInc := c322
  again := c323
  exit := c324
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
  test_edge := congrArg Prod.snd source_320
  first_edge := congrArg Prod.snd source_321
  second_edge := congrArg Prod.snd source_322
  again_edge := congrArg Prod.snd source_323
  positive_target := cached_target source_320 source_321 incPath (by rfl) (by rfl)
  first_target := cached_target source_321 source_322 incPath (by rfl) (by rfl)
  second_target := cached_target source_322 source_323 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_323 source_320 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_320 source_324 (breakPath 1) (by rfl) (by rfl)

private def argumentRestore : MoveShape where
  test := c324
  increment := c325
  again := c326
  exit := exit
  sourceLogical := 6
  targetLogical := 3
  sourceIndex := s1Reg
  targetIndex := acReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_324
  increment_edge := congrArg Prod.snd source_325
  again_edge := congrArg Prod.snd source_326
  positive_target := cached_target source_324 source_325 incPath (by rfl) (by rfl)
  increment_target := cached_target source_325 source_326 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_326 source_324 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_324 source_327 (breakPath 1) (by rfl) (by rfl)

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

/-- Copy/restore tail320→327, for arbitrary TW and only S1=0. -/
theorem copy_tail_run (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file acReg + 2) (liveValue (number copyEntry : V) file) =
      liveValue (number exit : V)
        (put twReg (regValue file twReg + regValue file acReg) file) := by
  simpa only [show argumentCopyBack.copy.sourceIndex = acReg from rfl,
    show argumentCopyBack.copy.test = copyEntry from rfl,
    show argumentCopyBack.restore.exit = exit from rfl] using
      copy_back_run argumentCopyBack file h1

/-- Actual301→327, with positive internal clock and the complete file effect. -/
theorem ac_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number exit : V) (argumentPushFile acReg file) := by
  exact argument_push_run initialPush argumentCopyBack rfl (by decide) file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXACPush254

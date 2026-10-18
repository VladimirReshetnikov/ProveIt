import BusyBeaver.ZFC.ArithmeticControlParamPush254

set_option autoImplicit false
noncomputable section

/-!
Actual AX parameter1 push at controls275..300, exiting at301. The checked
internal ParamPushShape contract supplies all unbounded execution. The old TW
is pushed onto WS and parameter1 is copied into TW while being restored.
Both scratch registers initially vanish. The following AC push is separate.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextParamPush254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlUnpair254 (wsReg)
open FiniteControlTable254 RegisterPath

def entry : Control := ⟨275, by decide⟩
def copyEntry : Control := ⟨294, by decide⟩
def exit : Control := ⟨301, by decide⟩
private def c276 : Control := ⟨276, by decide⟩
private def c277 : Control := ⟨277, by decide⟩
private def c278 : Control := ⟨278, by decide⟩
private def c279 : Control := ⟨279, by decide⟩
private def c280 : Control := ⟨280, by decide⟩
private def c281 : Control := ⟨281, by decide⟩
private def c282 : Control := ⟨282, by decide⟩
private def c283 : Control := ⟨283, by decide⟩
private def c284 : Control := ⟨284, by decide⟩
private def c285 : Control := ⟨285, by decide⟩
private def c286 : Control := ⟨286, by decide⟩
private def c287 : Control := ⟨287, by decide⟩
private def c288 : Control := ⟨288, by decide⟩
private def c289 : Control := ⟨289, by decide⟩
private def c290 : Control := ⟨290, by decide⟩
private def c291 : Control := ⟨291, by decide⟩
private def c292 : Control := ⟨292, by decide⟩
private def c293 : Control := ⟨293, by decide⟩
private def c295 : Control := ⟨295, by decide⟩
private def c296 : Control := ⟨296, by decide⟩
private def c297 : Control := ⟨297, by decide⟩
private def c298 : Control := ⟨298, by decide⟩
private def c299 : Control := ⟨299, by decide⟩
private def c300 : Control := ⟨300, by decide⟩

theorem entry_source : (source entry).2 = .decnz 1 := by rfl
theorem copyEntry_source : (source copyEntry).2 = .decnz 4 := by rfl
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

private def topToScratch : MoveShape where
  test := entry
  increment := c276
  again := c277
  exit := c278
  sourceLogical := 1
  targetLogical := 6
  sourceIndex := twReg
  targetIndex := s1Reg
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

private def stackToTop : MoveShape where
  test := c278
  increment := c279
  again := c280
  exit := c281
  sourceLogical := 2
  targetLogical := 1
  sourceIndex := wsReg
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

private def pairCopy : CopyShape where
  test := c281
  firstInc := c282
  secondInc := c283
  again := c284
  exit := c285
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

private def pairMove : MoveShape where
  test := c287
  increment := c288
  again := c289
  exit := c290
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

private def pairing : PairShape where
  copy := pairCopy
  testS1 := c285
  incS2 := c286
  move := pairMove
  again := c290
  exit := c291
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

private def pairOutput : MoveShape where
  test := c291
  increment := c292
  again := c293
  exit := copyEntry
  sourceLogical := 7
  targetLogical := 2
  sourceIndex := s2Reg
  targetIndex := wsReg
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

private def parameterCopy : CopyShape where
  test := copyEntry
  firstInc := c295
  secondInc := c296
  again := c297
  exit := c298
  sourceLogical := 4
  firstLogical := 1
  secondLogical := 6
  sourceIndex := p1Reg
  firstIndex := twReg
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

private def parameterRestore : MoveShape where
  test := c298
  increment := c299
  again := c300
  exit := exit
  sourceLogical := 6
  targetLogical := 4
  sourceIndex := s1Reg
  targetIndex := p1Reg
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

private def paramOccurrence : ParamPushShape where
  push := initialPush
  copy := parameterCopy
  restore := parameterRestore
  copy_source := rfl
  copy_first := rfl
  copy_second := rfl
  restore_source := rfl
  restore_target := rfl
  push_exit := rfl
  copy_exit := rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h

/-- Every coordinate except TW and WS is retained by the complete file effect. -/
theorem paramPushFile_other (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (paramPushFile file) i = regValue file i := by
  rw [paramPushFile, read_put_other _ _ twReg i ht.symm,
    read_put_other _ _ wsReg i hs.symm]

/-- The copy/restore tail permits arbitrary TW and needs only S1=0. -/
theorem copy_tail_run (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file p1Reg + 2) (liveValue (number copyEntry : V) file) =
      liveValue (number exit : V) (put twReg (regValue file twReg + regValue file p1Reg) file) := by
  simpa only [show paramOccurrence.copy.test = copyEntry from rfl,
    show paramOccurrence.restore.exit = exit from rfl] using param_copy_run paramOccurrence file h1

/-- Actual275→301, with positive internal time and exact complete-file output. -/
theorem ax_param_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number exit : V) (paramPushFile file) := by
  simpa only [show paramOccurrence.push.first.test = entry from rfl,
    show paramOccurrence.restore.exit = exit from rfl] using param_push_run paramOccurrence file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextParamPush254

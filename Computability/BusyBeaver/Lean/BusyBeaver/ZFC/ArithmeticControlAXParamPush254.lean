import BusyBeaver.ZFC.ArithmeticControlParamPush254

set_option autoImplicit false
noncomputable section

/-!
Actual AX parameter1 push at controls222..247, exiting at248. The checked
internal ParamPushShape contract supplies all unbounded execution. The old TW
is pushed onto WS and parameter1 is copied into TW while being restored.
Both scratch registers initially vanish. The following constructor is separate.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamPush254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlUnpair254 (wsReg)
open FiniteControlTable254 RegisterPath

def entry : Control := ⟨222, by decide⟩
def copyEntry : Control := ⟨241, by decide⟩
def exit : Control := ⟨248, by decide⟩
private def c223 : Control := ⟨223, by decide⟩
private def c224 : Control := ⟨224, by decide⟩
private def c225 : Control := ⟨225, by decide⟩
private def c226 : Control := ⟨226, by decide⟩
private def c227 : Control := ⟨227, by decide⟩
private def c228 : Control := ⟨228, by decide⟩
private def c229 : Control := ⟨229, by decide⟩
private def c230 : Control := ⟨230, by decide⟩
private def c231 : Control := ⟨231, by decide⟩
private def c232 : Control := ⟨232, by decide⟩
private def c233 : Control := ⟨233, by decide⟩
private def c234 : Control := ⟨234, by decide⟩
private def c235 : Control := ⟨235, by decide⟩
private def c236 : Control := ⟨236, by decide⟩
private def c237 : Control := ⟨237, by decide⟩
private def c238 : Control := ⟨238, by decide⟩
private def c239 : Control := ⟨239, by decide⟩
private def c240 : Control := ⟨240, by decide⟩
private def c242 : Control := ⟨242, by decide⟩
private def c243 : Control := ⟨243, by decide⟩
private def c244 : Control := ⟨244, by decide⟩
private def c245 : Control := ⟨245, by decide⟩
private def c246 : Control := ⟨246, by decide⟩
private def c247 : Control := ⟨247, by decide⟩

theorem entry_source : (source entry).2 = .decnz 1 := by rfl
theorem copyEntry_source : (source copyEntry).2 = .decnz 4 := by rfl
theorem exit_source : (source exit).2 = .decnz 2 := by rfl

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
  increment := c223
  again := c224
  exit := c225
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
  test := c225
  increment := c226
  again := c227
  exit := c228
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
  test := c228
  firstInc := c229
  secondInc := c230
  again := c231
  exit := c232
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
  test := c234
  increment := c235
  again := c236
  exit := c237
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
  testS1 := c232
  incS2 := c233
  move := pairMove
  again := c237
  exit := c238
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
  test := c238
  increment := c239
  again := c240
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
  firstInc := c242
  secondInc := c243
  again := c244
  exit := c245
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
  test := c245
  increment := c246
  again := c247
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

/-- Actual222→248, with positive internal time and exact complete-file output. -/
theorem ax_param_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number exit : V) (paramPushFile file) := by
  simpa only [show paramOccurrence.push.first.test = entry from rfl,
    show paramOccurrence.restore.exit = exit from rfl] using param_push_run paramOccurrence file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXParamPush254

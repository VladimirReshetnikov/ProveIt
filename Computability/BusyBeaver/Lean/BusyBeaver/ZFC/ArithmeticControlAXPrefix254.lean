import BusyBeaver.ZFC.ArithmeticControlParamPush254

set_option autoImplicit false
noncomputable section

/-!
The first actual AX parameter push: literal controls 41..66 reach control 67.
The checked generic Move/Copy/Pair contracts supply all unbounded runtime
reasoning. No new induction, AX bundle evaluation, or binary PA endpoint
is asserted. The source program is shared by the exact 246-state target.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry dispatchEntry)
open FiniteControlTable254 RegisterPath

private def c42 : Control := ⟨42, by decide⟩
private def c43 : Control := ⟨43, by decide⟩
private def c44 : Control := ⟨44, by decide⟩
private def c45 : Control := ⟨45, by decide⟩
private def c46 : Control := ⟨46, by decide⟩
private def c47 : Control := ⟨47, by decide⟩
private def c48 : Control := ⟨48, by decide⟩
private def c49 : Control := ⟨49, by decide⟩
private def c50 : Control := ⟨50, by decide⟩
private def c51 : Control := ⟨51, by decide⟩
private def c52 : Control := ⟨52, by decide⟩
private def c53 : Control := ⟨53, by decide⟩
private def c54 : Control := ⟨54, by decide⟩
private def c55 : Control := ⟨55, by decide⟩
private def c56 : Control := ⟨56, by decide⟩
private def c57 : Control := ⟨57, by decide⟩
private def c58 : Control := ⟨58, by decide⟩
private def c59 : Control := ⟨59, by decide⟩
private def c60 : Control := ⟨60, by decide⟩
private def c61 : Control := ⟨61, by decide⟩
private def c62 : Control := ⟨62, by decide⟩
private def c63 : Control := ⟨63, by decide⟩
private def c64 : Control := ⟨64, by decide⟩
private def c65 : Control := ⟨65, by decide⟩
private def c66 : Control := ⟨66, by decide⟩

/-- The second AX push starts here, after parameter1 has been restored. -/
def nextPush : Control := ⟨67, by decide⟩
/-- Parameter1 is copied only after the old top has been pushed. -/
def parameterCopy : Control := c60

theorem entry_source : source axEntry =
    ([true,true,true,false,true,false,false,true,false,false,true,false,false,false,false,false,false,false], .decnz 1) :=
  ArithmeticControlDispatch254.axEntry_source

theorem nextPush_source : source nextPush =
    ([true,true,true,false,true,false,false,true,false,false,true,false,false,false,true,false,false,false], .decnz 1) := by rfl

theorem parameterCopy_source : (source parameterCopy).2 = .decnz 4 := by rfl

private def topToScratch : MoveShape where
  test := axEntry
  increment := c42
  again := c43
  exit := c44
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
  positive_target := by rfl
  increment_target := by rfl
  repeat_target := by rfl
  zero_target := by rfl

private def stackToTop : MoveShape where
  test := c44
  increment := c45
  again := c46
  exit := c47
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
  positive_target := by rfl
  increment_target := by rfl
  repeat_target := by rfl
  zero_target := by rfl

private def pairCopy : CopyShape where
  test := c47
  firstInc := c48
  secondInc := c49
  again := c50
  exit := c51
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
  positive_target := by rfl
  first_target := by rfl
  second_target := by rfl
  repeat_target := by rfl
  zero_target := by rfl

private def pairMove : MoveShape where
  test := c53
  increment := c54
  again := c55
  exit := c56
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
  positive_target := by rfl
  increment_target := by rfl
  repeat_target := by rfl
  zero_target := by rfl

private def pairing : PairShape where
  copy := pairCopy
  testS1 := c51
  incS2 := c52
  move := pairMove
  again := c56
  exit := c57
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
  positive_target := by rfl
  zero_target := by rfl
  increment_target := by rfl
  repeat_target := by rfl

private def pairOutput : MoveShape where
  test := c57
  increment := c58
  again := c59
  exit := c60
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
  positive_target := by rfl
  increment_target := by rfl
  repeat_target := by rfl
  zero_target := by rfl

private def parameterCopyShape : CopyShape where
  test := c60
  firstInc := c61
  secondInc := c62
  again := c63
  exit := c64
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
  positive_target := by rfl
  first_target := by rfl
  second_target := by rfl
  repeat_target := by rfl
  zero_target := by rfl

private def parameterRestore : MoveShape where
  test := c64
  increment := c65
  again := c66
  exit := nextPush
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
  positive_target := by rfl
  increment_target := by rfl
  repeat_target := by rfl
  zero_target := by rfl

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

private def axPrefix : ParamPushShape where
  push := initialPush
  copy := parameterCopyShape
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

/-- First push: only TW and WS change; all other fields are retained. -/
theorem ax_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number parameterCopy : V) (pushFile file) := by
  exact push_run initialPush file h1 h2

/-- The copy/restore tail has exactly 7*param1+2 logical instructions. -/
theorem ax_parameter_copy_run (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file p1Reg + 2)
      (liveValue (number parameterCopy : V) file) =
      liveValue (number nextPush : V)
        (put twReg (regValue file twReg + regValue file p1Reg) file) := by
  exact param_copy_run axPrefix file h1

/-- Actual AX prefix: TW:=param1 and WS:=cantor(oldTW,oldWS), preserving
parameter1, cache, both scratch fields, AC, PL and the enumeration counter. -/
theorem ax_prefix_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number nextPush : V) (paramPushFile file) := by
  exact param_push_run axPrefix file h1 h2

/-- Include the exact AC=c+3 classifier, retaining c in the whole file. -/
theorem dispatch_ax_prefix_run (file c : V) (ha : regValue file acReg = c + 3)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number dispatchEntry : V) file) =
      liveValue (number nextPush : V) (paramPushFile (put acReg c file)) := by
  have h1' : regValue (put acReg c file) s1Reg = 0 := by
    rw [put, ArithmeticControlStep254.write_other file c acReg s1Reg (by decide)]
    exact h1
  have h2' : regValue (put acReg c file) s2Reg = 0 := by
    rw [put, ArithmeticControlStep254.write_other file c acReg s2Reg (by decide)]
    exact h2
  obtain ⟨time, ht, hr⟩ := ax_prefix_run (put acReg c file) h1' h2'
  refine ⟨3 + time, le_trans ht (le_add_of_nonneg_left (Arithmetic.zero_le 3)), ?_⟩
  rw [controlRun_add, ArithmeticControlDispatch254.dispatch_ax file c ha, hr]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXPrefix254

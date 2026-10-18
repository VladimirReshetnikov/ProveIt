import BusyBeaver.ZFC.ArithmeticControlCopyBack254

set_option autoImplicit false
noncomputable section

/-! Actual AX argument push136→162, followed by a plain push162→181.
Generic internal contracts supply all unbounded execution. The finite shapes
bind actual control edges and successors. Later reads/constructors remain separate. -/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlCopyBack254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlUnpair254 (wsReg)
open FiniteControlTable254 RegisterPath

def entry : Control := ⟨136, by decide⟩
def argumentExit : Control := ⟨162, by decide⟩
def exit : Control := ⟨181, by decide⟩
private def c137 : Control := ⟨137, by decide⟩
private def c138 : Control := ⟨138, by decide⟩
private def c139 : Control := ⟨139, by decide⟩
private def c140 : Control := ⟨140, by decide⟩
private def c141 : Control := ⟨141, by decide⟩
private def c142 : Control := ⟨142, by decide⟩
private def c143 : Control := ⟨143, by decide⟩
private def c144 : Control := ⟨144, by decide⟩
private def c145 : Control := ⟨145, by decide⟩
private def c146 : Control := ⟨146, by decide⟩
private def c147 : Control := ⟨147, by decide⟩
private def c148 : Control := ⟨148, by decide⟩
private def c149 : Control := ⟨149, by decide⟩
private def c150 : Control := ⟨150, by decide⟩
private def c151 : Control := ⟨151, by decide⟩
private def c152 : Control := ⟨152, by decide⟩
private def c153 : Control := ⟨153, by decide⟩
private def c154 : Control := ⟨154, by decide⟩
private def c155 : Control := ⟨155, by decide⟩
private def c156 : Control := ⟨156, by decide⟩
private def c157 : Control := ⟨157, by decide⟩
private def c158 : Control := ⟨158, by decide⟩
private def c159 : Control := ⟨159, by decide⟩
private def c160 : Control := ⟨160, by decide⟩
private def c161 : Control := ⟨161, by decide⟩
private def c162 : Control := ⟨162, by decide⟩
private def c163 : Control := ⟨163, by decide⟩
private def c164 : Control := ⟨164, by decide⟩
private def c165 : Control := ⟨165, by decide⟩
private def c166 : Control := ⟨166, by decide⟩
private def c167 : Control := ⟨167, by decide⟩
private def c168 : Control := ⟨168, by decide⟩
private def c169 : Control := ⟨169, by decide⟩
private def c170 : Control := ⟨170, by decide⟩
private def c171 : Control := ⟨171, by decide⟩
private def c172 : Control := ⟨172, by decide⟩
private def c173 : Control := ⟨173, by decide⟩
private def c174 : Control := ⟨174, by decide⟩
private def c175 : Control := ⟨175, by decide⟩
private def c176 : Control := ⟨176, by decide⟩
private def c177 : Control := ⟨177, by decide⟩
private def c178 : Control := ⟨178, by decide⟩
private def c179 : Control := ⟨179, by decide⟩
private def c180 : Control := ⟨180, by decide⟩

theorem entry_source : (source entry).2 = .decnz 1 := by rfl
theorem argumentExit_source : (source argumentExit).2 = .decnz 1 := by rfl
theorem exit_source : (source exit).2 = .decnz 8 := by rfl

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
  increment := c137
  again := c138
  exit := c139
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
  test := c139
  increment := c140
  again := c141
  exit := c142
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
  test := c142
  firstInc := c143
  secondInc := c144
  again := c145
  exit := c146
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
  test := c148
  increment := c149
  again := c150
  exit := c151
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
  testS1 := c146
  incS2 := c147
  move := pairMove
  again := c151
  exit := c152
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
  test := c152
  increment := c153
  again := c154
  exit := c155
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

private def argumentCopy : CopyShape where
  test := c155
  firstInc := c156
  secondInc := c157
  again := c158
  exit := c159
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

private def argumentRestore : MoveShape where
  test := c159
  increment := c160
  again := c161
  exit := argumentExit
  sourceLogical := 6
  targetLogical := 3
  sourceIndex := s1Reg
  targetIndex := acReg
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

private def argumentCopyBack : CopyBackShape where
  copy := argumentCopy
  restore := argumentRestore
  first_target := rfl
  second_target := rfl
  restore_source := rfl
  restore_target := rfl
  join := rfl

private def plainTopToScratch : MoveShape where
  test := argumentExit
  increment := c163
  again := c164
  exit := c165
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

private def plainStackToTop : MoveShape where
  test := c165
  increment := c166
  again := c167
  exit := c168
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

private def plainPairCopy : CopyShape where
  test := c168
  firstInc := c169
  secondInc := c170
  again := c171
  exit := c172
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

private def plainPairMove : MoveShape where
  test := c174
  increment := c175
  again := c176
  exit := c177
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

private def plainPairing : PairShape where
  copy := plainPairCopy
  testS1 := c172
  incS2 := c173
  move := plainPairMove
  again := c177
  exit := c178
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

private def plainPairOutput : MoveShape where
  test := c178
  increment := c179
  again := c180
  exit := exit
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

private def plainInitialPush : PushShape where
  first := plainTopToScratch
  second := plainStackToTop
  pairing := plainPairing
  output := plainPairOutput
  first_source := rfl
  first_target := rfl
  second_source := rfl
  second_target := rfl
  output_source := rfl
  output_target := rfl
  first_exit := rfl
  second_exit := rfl
  pair_exit := rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Push the old TW, then copy AC into TW, preserving all other fields. -/
theorem argument_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number argumentExit : V) (argumentPushFile acReg file) := by
  exact argument_push_run initialPush argumentCopyBack rfl (by decide) file h1 h2

/-- The immediately following plain push leaves TW zero. -/
theorem plain_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number argumentExit : V) file) =
      liveValue (number exit : V) (pushFile file) := by
  exact push_run plainInitialPush file h1 h2

/-- The complete two-push segment, retaining the literal nested file update. -/
theorem two_pushes_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number exit : V) (pushFile (argumentPushFile acReg file)) := by
  have hg1 : regValue (argumentPushFile acReg file) s1Reg = 0 :=
    (argumentPushFile_other acReg s1Reg file (by decide) (by decide)).trans h1
  have hg2 : regValue (argumentPushFile acReg file) s2Reg = 0 :=
    (argumentPushFile_other acReg s2Reg file (by decide) (by decide)).trans h2
  obtain ⟨t1, ht1, hr1⟩ := argument_run file h1 h2
  obtain ⟨t2, _, hr2⟩ := plain_push_run (argumentPushFile acReg file) hg1 hg2
  refine ⟨t1 + t2, le_trans ht1 (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hr1, hr2]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXArgumentPush254

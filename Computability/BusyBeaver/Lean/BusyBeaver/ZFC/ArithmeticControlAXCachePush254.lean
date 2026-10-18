import BusyBeaver.ZFC.ArithmeticControlAXPrefix254

set_option autoImplicit false
noncomputable section

/-!
The actual AX cache/P2 push, controls 67..92 reaching control 93. Generic
Move/Copy/Pair contracts supply all unbounded runtime reasoning. The exact
cache-copy tail and composition with the checked first AX push preserve the
whole nine-register file. No GEN constructor or later AX suffix is included.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlClear254
open ArithmeticControlPair254 ArithmeticControlParamPush254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlAXPrefix254 (nextPush ax_prefix_run)
open FiniteControlTable254 RegisterPath

private def c68 : Control := ⟨68, by decide⟩
private def c69 : Control := ⟨69, by decide⟩
private def c70 : Control := ⟨70, by decide⟩
private def c71 : Control := ⟨71, by decide⟩
private def c72 : Control := ⟨72, by decide⟩
private def c73 : Control := ⟨73, by decide⟩
private def c74 : Control := ⟨74, by decide⟩
private def c75 : Control := ⟨75, by decide⟩
private def c76 : Control := ⟨76, by decide⟩
private def c77 : Control := ⟨77, by decide⟩
private def c78 : Control := ⟨78, by decide⟩
private def c79 : Control := ⟨79, by decide⟩
private def c80 : Control := ⟨80, by decide⟩
private def c81 : Control := ⟨81, by decide⟩
private def c82 : Control := ⟨82, by decide⟩
private def c83 : Control := ⟨83, by decide⟩
private def c84 : Control := ⟨84, by decide⟩
private def c85 : Control := ⟨85, by decide⟩
private def c86 : Control := ⟨86, by decide⟩
private def c87 : Control := ⟨87, by decide⟩
private def c88 : Control := ⟨88, by decide⟩
private def c89 : Control := ⟨89, by decide⟩
private def c90 : Control := ⟨90, by decide⟩
private def c91 : Control := ⟨91, by decide⟩
private def c92 : Control := ⟨92, by decide⟩

/-- The cache is copied after the old top has been pushed. -/
def cacheCopy : Control := c86
/-- The following constructor begins by popping the stack here. -/
def cachePop : Control := ⟨93, by decide⟩

theorem entry_source : source nextPush =
    ([true,true,true,false,true,false,false,true,false,false,true,false,false,false,true,false,false,false], .decnz 1) :=
  ArithmeticControlAXPrefix254.nextPush_source

theorem cacheCopy_source : (source cacheCopy).2 = .decnz 5 := by rfl

theorem cachePop_source : source cachePop =
    ([true,true,true,false,true,false,false,true,false,false,true,false,false,true,false,false,false,false], .decnz 2) := by rfl

private def topToScratch : MoveShape where
  test := nextPush
  increment := c68
  again := c69
  exit := c70
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
  test := c70
  increment := c71
  again := c72
  exit := c73
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
  test := c73
  firstInc := c74
  secondInc := c75
  again := c76
  exit := c77
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
  test := c79
  increment := c80
  again := c81
  exit := c82
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
  testS1 := c77
  incS2 := c78
  move := pairMove
  again := c82
  exit := c83
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
  test := c83
  increment := c84
  again := c85
  exit := c86
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

private def cacheCopyShape : CopyShape where
  test := c86
  firstInc := c87
  secondInc := c88
  again := c89
  exit := c90
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
  test_edge := by rfl
  first_edge := by rfl
  second_edge := by rfl
  again_edge := by rfl
  positive_target := by rfl
  first_target := by rfl
  second_target := by rfl
  repeat_target := by rfl
  zero_target := by rfl

private def cacheRestore : MoveShape where
  test := c90
  increment := c91
  again := c92
  exit := cachePop
  sourceLogical := 6
  targetLogical := 5
  sourceIndex := s1Reg
  targetIndex := cacheReg
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

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) :
    regValue (put p x file) p = x := write_at file x p
private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h
private theorem file_ext (x y : V) (h : ∀ i, regValue x i = regValue y i) : x = y := by
  rw [←file_reg x, ←file_reg y]
  exact congrArg fileValue (funext h)
private theorem read_put (p q : Fin 9) (x file : V) :
    regValue (put p x file) q = if p = q then x else regValue file q := by
  by_cases h : p = q
  · subst q
    rw [if_pos rfl]
    exact read_put_self file x p
  · simpa only [if_neg h] using read_put_other file x p q h

/-- This occurrence pushes TW before copying the cache. -/
theorem ax_stack_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number nextPush : V) file) =
      liveValue (number cacheCopy : V) (pushFile file) := by
  exact push_run initialPush file h1 h2

/-- Exactly 7*cache+2 instructions; only scratch1 must initially be zero. -/
theorem ax_cache_copy_run (file : V) (h1 : regValue file s1Reg = 0) :
    controlRun (7 * regValue file cacheReg + 2)
      (liveValue (number cacheCopy : V) file) =
      liveValue (number cachePop : V)
        (put twReg (regValue file twReg + regValue file cacheReg) file) := by
  let h := regValue file cacheReg
  let g := put s1Reg h (put twReg (regValue file twReg + h) (put cacheReg 0 file))
  have hcopy : controlRun (4 * h + 1) (liveValue (number cacheCopy : V) file) =
      liveValue (number cacheRestore.test : V) g := by
    simpa only [show cacheCopyShape.test = cacheCopy from rfl,
      show cacheCopyShape.exit = cacheRestore.test from rfl,
      show cacheCopyShape.sourceIndex = cacheReg from rfl,
      show cacheCopyShape.firstIndex = twReg from rfl,
      show cacheCopyShape.secondIndex = s1Reg from rfl, h1, zero_add, h, g]
      using copy_run cacheCopyShape file
  have hgs1 : regValue g s1Reg = h := by
    dsimp only [g]
    rw [read_put_self]
  have hgp : regValue g cacheReg = 0 := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg cacheReg (by decide),
      read_put_other _ _ twReg cacheReg (by decide), read_put_self]
  have hf : put cacheReg h (put s1Reg 0 g) =
      put twReg (regValue file twReg + regValue file cacheReg) file := by
    apply file_ext
    intro i
    have h1' : regValue file (8 : Fin 9) = 0 := h1
    by_cases hi2 : i = (2 : Fin 9)
    · subst i
      simp [read_put, g, h, twReg, cacheReg, s1Reg]
    by_cases hi7 : i = (7 : Fin 9)
    · subst i
      simp [read_put, g, h, twReg, cacheReg, s1Reg]
    by_cases hi8 : i = (8 : Fin 9)
    · subst i
      simp [read_put, g, h, twReg, cacheReg, s1Reg, h1']
    simp [read_put, g, h, twReg, cacheReg, s1Reg,
      Ne.symm hi2, Ne.symm hi7, Ne.symm hi8]
  have hrestore : controlRun (3 * h + 1)
      (liveValue (number cacheRestore.test : V) g) =
      liveValue (number cachePop : V)
        (put twReg (regValue file twReg + regValue file cacheReg) file) := by
    simpa only [show cacheRestore.exit = cachePop from rfl,
      show cacheRestore.sourceIndex = s1Reg from rfl,
      show cacheRestore.targetIndex = cacheReg from rfl, hgs1, hgp, zero_add, hf]
      using move_run cacheRestore g
  rw [show 7 * regValue file cacheReg + 2 = (4 * h + 1) + (3 * h + 1) by
      dsimp only [h]; ring, controlRun_add, hcopy, hrestore]

/-- The second AX push changes exactly the two working formula fields. -/
def cachePushFile (file : V) : V :=
  put twReg (regValue file cacheReg)
    (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)

theorem cachePushFile_other (file : V) (p : Fin 9)
    (ht : p ≠ twReg) (hs : p ≠ wsReg) :
    regValue (cachePushFile file) p = regValue file p := by
  rw [cachePushFile, read_put_other _ _ twReg p ht.symm,
    read_put_other _ _ wsReg p hs.symm]

/-- Actual cache/P2 push for arbitrary internal input values and runtime. -/
theorem ax_cache_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number nextPush : V) file) =
      liveValue (number cachePop : V) (cachePushFile file) := by
  let g := pushFile file
  have hg1 : regValue g s1Reg = 0 := by
    dsimp only [g, pushFile]
    rw [read_put_other _ _ wsReg s1Reg (by decide),
      read_put_other _ _ twReg s1Reg (by decide)]
    exact h1
  have hgtw : regValue g twReg = 0 := by
    dsimp only [g, pushFile]
    rw [read_put_other _ _ wsReg twReg (by decide), read_put_self]
  have hgc : regValue g cacheReg = regValue file cacheReg := by
    dsimp only [g, pushFile]
    rw [read_put_other _ _ wsReg cacheReg (by decide),
      read_put_other _ _ twReg cacheReg (by decide)]
  have hf : put twReg (regValue g twReg + regValue g cacheReg) g = cachePushFile file := by
    rw [hgtw, hgc, zero_add]
    apply file_ext
    intro i
    by_cases hi2 : i = (2 : Fin 9)
    · subst i
      simp [read_put, g, pushFile, cachePushFile, twReg, wsReg]
    by_cases hi0 : i = (0 : Fin 9)
    · subst i
      simp [read_put, g, pushFile, cachePushFile, twReg, wsReg]
    simp [read_put, g, pushFile, cachePushFile, twReg, wsReg, Ne.symm hi2, Ne.symm hi0]
  obtain ⟨tp, htp, hp⟩ := ax_stack_push_run file h1 h2
  have ht := ax_cache_copy_run g hg1
  rw [hf, hgc] at ht
  refine ⟨tp + (7 * regValue file cacheReg + 2),
    le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hp]
  exact ht

/-- The two parameter pushes save the old top followed by parameter1. -/
def twoParametersFile (file : V) : V :=
  put twReg (regValue file cacheReg)
    (put wsReg (cantor (regValue file p1Reg)
      (cantor (regValue file twReg) (regValue file wsReg))) file)

private theorem cachePushFile_paramPushFile (file : V) :
    cachePushFile (paramPushFile file) = twoParametersFile file := by
  apply file_ext
  intro i
  by_cases hi2 : i = (2 : Fin 9)
  · subst i
    simp [read_put, cachePushFile, paramPushFile, twoParametersFile, twReg, wsReg, cacheReg]
  by_cases hi0 : i = (0 : Fin 9)
  · subst i
    simp [read_put, cachePushFile, paramPushFile, twoParametersFile, twReg, wsReg, cacheReg]
  simp [read_put, cachePushFile, paramPushFile, twoParametersFile, twReg, wsReg, cacheReg,
    Ne.symm hi2, Ne.symm hi0]

/-- Composition with the checked first AX push, still before the GEN constructor. -/
theorem ax_two_parameters_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number cachePop : V) (twoParametersFile file) := by
  have h1' : regValue (paramPushFile file) s1Reg = 0 := by
    rw [paramPushFile, read_put_other _ _ twReg s1Reg (by decide),
      read_put_other _ _ wsReg s1Reg (by decide)]
    exact h1
  have h2' : regValue (paramPushFile file) s2Reg = 0 := by
    rw [paramPushFile, read_put_other _ _ twReg s2Reg (by decide),
      read_put_other _ _ wsReg s2Reg (by decide)]
    exact h2
  obtain ⟨t1, ht1, hr1⟩ := ax_prefix_run file h1 h2
  obtain ⟨t2, _, hr2⟩ := ax_cache_push_run (paramPushFile file) h1' h2'
  refine ⟨t1 + t2, le_trans ht1 (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hr1, hr2, cachePushFile_paramPushFile]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXCachePush254

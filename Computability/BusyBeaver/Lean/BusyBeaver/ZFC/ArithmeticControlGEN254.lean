import BusyBeaver.ZFC.ArithmeticControlAXCachePush254
import BusyBeaver.ZFC.ArithmeticControlMP254

set_option autoImplicit false
noncomputable section

/-!
The actual first AX universal-formula constructor, controls93..121 reaching122.
The finite occurrences reuse checked internal UnpairCore, Pair and Scale4
contracts. No new induction, standard-Nat restriction, fixed fuel or assumption
of formula wellformedness is used. The result is the whole nine-register file.
The later parameter read and remaining AX branch are separate obligations.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254
open ArithmeticControlSimulation254 ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticControlClear254 ArithmeticControlPair254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (axEntry cacheReg)
open ArithmeticControlAXPrefix254 (nextPush)
open ArithmeticControlAXCachePush254 (cachePop cachePushFile twoParametersFile)
open ArithmeticControlUnpairCore254 (UnpairCoreShape core_run)
open ArithmeticControlMP254 (Scale4Shape scale_run)
open FiniteControlTable254 RegisterPath

private def c94 : Control := ⟨94, by decide⟩
private def c95 : Control := ⟨95, by decide⟩
private def c96 : Control := ⟨96, by decide⟩
private def c97 : Control := ⟨97, by decide⟩
private def c98 : Control := ⟨98, by decide⟩
private def c99 : Control := ⟨99, by decide⟩
private def c100 : Control := ⟨100, by decide⟩
private def c101 : Control := ⟨101, by decide⟩
private def c102 : Control := ⟨102, by decide⟩
private def c103 : Control := ⟨103, by decide⟩
private def c104 : Control := ⟨104, by decide⟩
private def c105 : Control := ⟨105, by decide⟩
private def c106 : Control := ⟨106, by decide⟩
private def c107 : Control := ⟨107, by decide⟩
private def c108 : Control := ⟨108, by decide⟩
private def c109 : Control := ⟨109, by decide⟩
private def c110 : Control := ⟨110, by decide⟩
private def c111 : Control := ⟨111, by decide⟩
private def c112 : Control := ⟨112, by decide⟩
private def c113 : Control := ⟨113, by decide⟩
private def c114 : Control := ⟨114, by decide⟩
private def c115 : Control := ⟨115, by decide⟩
private def c116 : Control := ⟨116, by decide⟩
private def c117 : Control := ⟨117, by decide⟩
private def c118 : Control := ⟨118, by decide⟩
private def c119 : Control := ⟨119, by decide⟩
private def c120 : Control := ⟨120, by decide⟩
private def c121 : Control := ⟨121, by decide⟩

/-- Pairing starts after the stack pop. -/
def pairEntry : Control := c104
/-- The two tag increments follow the scaled transfer. -/
def tagEntry : Control := c120
/-- The next parameter read is outside this constructor contract. -/
def nextRead : Control := ⟨122, by decide⟩

theorem entry_source : (source cachePop).2 = .decnz 2 :=
  congrArg Prod.snd ArithmeticControlAXCachePush254.cachePop_source

theorem pairEntry_source : (source pairEntry).2 = .decnz 1 := by rfl

theorem nextRead_source : (source nextRead).2 = .decnz 8 := by rfl

private def stackPop : UnpairCoreShape where
  readEntry := cachePop
  bodyIncS2 := c94
  bodyTestS1 := c95
  bodyBreak := c96
  bodyMoveTest := c97
  bodyMoveInc := c98
  bodyMoveContinue := c99
  bodyContinue := c100
  restoreMainTest := c101
  restoreMainInc := c102
  restoreMainContinue := c103
  exit := pairEntry
  mainLogical := 2
  mainIndex := wsReg
  main_physical := rfl
  main_ne_s1 := by decide
  main_ne_s2 := by decide
  read_edge := by rfl
  body_inc_edge := by rfl
  body_test_edge := by rfl
  body_break_edge := by rfl
  body_move_test_edge := by rfl
  body_move_inc_edge := by rfl
  body_move_continue_edge := by rfl
  body_continue_edge := by rfl
  restore_test_edge := by rfl
  restore_inc_edge := by rfl
  restore_continue_edge := by rfl
  next_read_positive := by rfl
  next_read_zero := by rfl
  next_body_inc := by rfl
  next_body_test_positive := by rfl
  next_body_test_zero := by rfl
  next_body_break := by rfl
  next_body_move_positive := by rfl
  next_body_move_inc := by rfl
  next_body_move_continue := by rfl
  next_body_move_zero := by rfl
  next_body_continue := by rfl
  next_restore_main_positive := by rfl
  next_restore_main_inc := by rfl
  next_restore_main_continue := by rfl
  next_restore_main_zero := by rfl

private def genCopy : CopyShape where
  test := pairEntry
  firstInc := c105
  secondInc := c106
  again := c107
  exit := c108
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

private def genMove : MoveShape where
  test := c110
  increment := c111
  again := c112
  exit := c113
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

private def genPair : PairShape where
  copy := genCopy
  testS1 := c108
  incS2 := c109
  move := genMove
  again := c113
  exit := c114
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

private def genScale : Scale4Shape where
  test := c114
  inc1 := c115
  inc2 := c116
  inc3 := c117
  inc4 := c118
  again := c119
  exit := tagEntry
  test_edge := by rfl
  inc1_edge := by rfl
  inc2_edge := by rfl
  inc3_edge := by rfl
  inc4_edge := by rfl
  again_edge := by rfl
  positive_target := by rfl
  zero_target := by rfl
  next_inc1 := by rfl
  next_inc2 := by rfl
  next_inc3 := by rfl
  next_inc4 := by rfl
  repeat_target := by rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) :
    regValue (put p x file) p = x := write_at file x p
private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h
private theorem put_twice (p : Fin 9) (x y file : V) :
    put p y (put p x file) = put p y file := write_overwrite file x y p
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

private theorem read_tw (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 1) 0 = regValue file twReg :=
  physicalValues_getD file twReg

private theorem increment (p q : Control) (edge : (source p).2 = .inc 1)
    (next : resolveControl (incPath (source p).1) = q) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number p : V) file) =
      liveValue (number q : V) (put twReg (regValue file twReg + 1) file) := by
  rw [step_inc p 1 edge, next, read_tw]
  rfl

/-- The universal tag is two literal increments, with all other fields fixed. -/
theorem gen_tag_run (file : V) :
    controlRun 2 (liveValue (number tagEntry : V) file) =
      liveValue (number nextRead : V) (put twReg (regValue file twReg + 2) file) := by
  have hrun : controlRun ((0 + 1) + 1 : V) (liveValue (number tagEntry : V) file) =
      liveValue (number nextRead : V) (put twReg ((regValue file twReg + 1) + 1) file) := by
    rw [controlRun_succ, controlRun_succ, controlRun_zero,
      increment tagEntry c121 (by rfl) (by rfl),
      increment c121 nextRead (by rfl) (by rfl), read_put_self, put_twice]
  simpa only [show ((0 + 1) + 1 : V) = 2 by ring,
    show (regValue file twReg + 1) + 1 = regValue file twReg + 2 by ring] using hrun

/-- The middle consumes scratch1 as its left input; scratch2 must be zero. -/
def pairScaleFile (file : V) : V :=
  put twReg (wal (regValue file s1Reg) (regValue file twReg)) (put s1Reg 0 file)

theorem gen_pair_scale_run (file : V) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number pairEntry : V) file) =
      liveValue (number nextRead : V) (pairScaleFile file) := by
  let p := cantor (regValue file s1Reg) (regValue file twReg)
  let g := pairFile file 0 0 p
  have hp : ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number pairEntry : V) file) =
        liveValue (number genScale.test : V)
          (pairFile file 0 0 (regValue file s2Reg + p)) := by
    simpa only [show genPair.copy.test = pairEntry from rfl,
      show genPair.exit = genScale.test from rfl, p] using pair_run genPair file
  obtain ⟨tp, htp, hpair⟩ := hp
  rw [h2, zero_add] at hpair
  have hgs2 : regValue g s2Reg = p := by
    dsimp only [g, pairFile]
    rw [read_put_other _ _ s1Reg s2Reg (by decide), read_put_self]
  have hgtw : regValue g twReg = 0 := by
    dsimp only [g, pairFile]
    rw [read_put_other _ _ s1Reg twReg (by decide),
      read_put_other _ _ s2Reg twReg (by decide), read_put_self]
  let scaled := put twReg (4 * p) (put s2Reg 0 g)
  have hscale := scale_run genScale g
  rw [hgs2, hgtw, zero_add] at hscale
  have htag := gen_tag_run scaled
  have hf : put twReg (regValue scaled twReg + 2) scaled = pairScaleFile file := by
    apply file_ext
    intro i
    have hz : regValue file (5 : Fin 9) = 0 := h2
    by_cases hi2 : i = (2 : Fin 9)
    · subst i
      simp [read_put, scaled, g, pairFile, pairScaleFile, p, wal, tagged, twReg, s1Reg, s2Reg]
    by_cases hi8 : i = (8 : Fin 9)
    · subst i
      simp [read_put, scaled, g, pairFile, pairScaleFile, twReg, s1Reg, s2Reg]
    by_cases hi5 : i = (5 : Fin 9)
    · subst i
      simp [read_put, scaled, g, pairFile, pairScaleFile, twReg, s1Reg, s2Reg, hz]
    simp [read_put, scaled, g, pairFile, pairScaleFile, twReg, s1Reg, s2Reg,
      Ne.symm hi2, Ne.symm hi8, Ne.symm hi5]
  rw [hf] at htag
  refine ⟨(tp + (6 * p + 1)) + 2,
    le_trans htp (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le _))
      (le_add_of_nonneg_right (Arithmetic.zero_le _))), ?_⟩
  rw [controlRun_add (tp + (6 * p + 1)) 2,
    controlRun_add tp (6 * p + 1), hpair, hscale]
  exact htag

/-- Pop one internal stack cell and form the universal code. -/
def genFile (file : V) : V :=
  put twReg (wal (first (regValue file wsReg)) (regValue file twReg))
    (put wsReg (second (regValue file wsReg)) file)

theorem genFile_other (file : V) (i : Fin 9) (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (genFile file) i = regValue file i := by
  rw [genFile, read_put_other _ _ twReg i ht.symm,
    read_put_other _ _ wsReg i hs.symm]

/-- Actual93→122 constructor, for arbitrary internal register files and clocks. -/
theorem gen_constructor_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number cachePop : V) file) =
      liveValue (number nextRead : V) (genFile file) := by
  let g := put s1Reg (first (regValue file wsReg))
    (put wsReg (second (regValue file wsReg)) file)
  have hp : ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number cachePop : V) file) =
      liveValue (number pairEntry : V) g := by
    simpa only [show stackPop.readEntry = cachePop from rfl,
      show stackPop.exit = pairEntry from rfl,
      show stackPop.mainIndex = wsReg from rfl, g] using core_run stackPop file h1 h2
  obtain ⟨tp, htp, hpop⟩ := hp
  have hg2 : regValue g s2Reg = 0 := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg s2Reg (by decide),
      read_put_other _ _ wsReg s2Reg (by decide)]
    exact h2
  have hf : pairScaleFile g = genFile file := by
    apply file_ext
    intro i
    have hz : regValue file (8 : Fin 9) = 0 := h1
    by_cases hi2 : i = (2 : Fin 9)
    · subst i
      simp [read_put, pairScaleFile, g, genFile, twReg, wsReg, s1Reg]
    by_cases hi0 : i = (0 : Fin 9)
    · subst i
      simp [read_put, pairScaleFile, g, genFile, twReg, wsReg, s1Reg]
    by_cases hi8 : i = (8 : Fin 9)
    · subst i
      simp [read_put, pairScaleFile, g, genFile, twReg, wsReg, s1Reg, hz]
    simp [read_put, pairScaleFile, g, genFile, twReg, wsReg, s1Reg,
      Ne.symm hi2, Ne.symm hi0, Ne.symm hi8]
  obtain ⟨tm, _, hmiddle⟩ := gen_pair_scale_run g hg2
  refine ⟨tp + tm, le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hpop, hmiddle, hf]

/-- Cache push plus GEN restores the original stack and changes only TW. -/
def cacheGenFile (file : V) : V :=
  put twReg (wal (regValue file twReg) (regValue file cacheReg)) file

private theorem genFile_cachePush (file : V) : genFile (cachePushFile file) = cacheGenFile file := by
  apply file_ext
  intro i
  by_cases hi2 : i = (2 : Fin 9)
  · subst i
    simp [read_put, genFile, cachePushFile, cacheGenFile, twReg, wsReg]
  by_cases hi0 : i = (0 : Fin 9)
  · subst i
    simp [read_put, genFile, cachePushFile, cacheGenFile, twReg, wsReg]
  simp [read_put, genFile, cachePushFile, cacheGenFile, twReg, wsReg, Ne.symm hi2, Ne.symm hi0]

theorem gen_cache_push_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number nextPush : V) file) =
      liveValue (number nextRead : V) (cacheGenFile file) := by
  have h1' : regValue (cachePushFile file) s1Reg = 0 := by
    rw [ArithmeticControlAXCachePush254.cachePushFile_other file s1Reg (by decide) (by decide)]
    exact h1
  have h2' : regValue (cachePushFile file) s2Reg = 0 := by
    rw [ArithmeticControlAXCachePush254.cachePushFile_other file s2Reg (by decide) (by decide)]
    exact h2
  obtain ⟨tp, htp, hp⟩ := ArithmeticControlAXCachePush254.ax_cache_push_run file h1 h2
  obtain ⟨tg, _, hg⟩ := gen_constructor_run (cachePushFile file) h1' h2'
  refine ⟨tp + tg, le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hp, hg, genFile_cachePush]

/-- The first AX formula is formed before the subsequent cache/P2 read. -/
def axGenFile (file : V) : V :=
  put twReg (wal (regValue file p1Reg) (regValue file cacheReg))
    (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)

private theorem genFile_twoParameters (file : V) :
    genFile (twoParametersFile file) = axGenFile file := by
  apply file_ext
  intro i
  by_cases hi2 : i = (2 : Fin 9)
  · subst i
    simp [read_put, genFile, twoParametersFile, axGenFile, twReg, wsReg]
  by_cases hi0 : i = (0 : Fin 9)
  · subst i
    simp [read_put, genFile, twoParametersFile, axGenFile, twReg, wsReg]
  simp [read_put, genFile, twoParametersFile, axGenFile, twReg, wsReg, Ne.symm hi2, Ne.symm hi0]

theorem ax_gen_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number axEntry : V) file) =
      liveValue (number nextRead : V) (axGenFile file) := by
  have h1' : regValue (twoParametersFile file) s1Reg = 0 := by
    rw [twoParametersFile, read_put_other _ _ twReg s1Reg (by decide),
      read_put_other _ _ wsReg s1Reg (by decide)]
    exact h1
  have h2' : regValue (twoParametersFile file) s2Reg = 0 := by
    rw [twoParametersFile, read_put_other _ _ twReg s2Reg (by decide),
      read_put_other _ _ wsReg s2Reg (by decide)]
    exact h2
  obtain ⟨tp, htp, hp⟩ := ArithmeticControlAXCachePush254.ax_two_parameters_run file h1 h2
  obtain ⟨tg, _, hg⟩ := gen_constructor_run (twoParametersFile file) h1' h2'
  refine ⟨tp + tg, le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hp, hg, genFile_twoParameters]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlGEN254

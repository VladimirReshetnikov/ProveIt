import BusyBeaver.ZFC.ArithmeticControlMP254

set_option autoImplicit false
noncomputable section

/-!
A literal constructor template for tags0..3: pop WS, pair its first coordinate
with TW, scale by4, then execute the tag's finite TW-increment chain. The shapes
contain only actual instruction and control-target facts. Unbounded loops reuse
checked internal IΣ1 contracts. Files and existential total clocks remain
arbitrary internal values. The actual zero-tag occurrence is controls195→222.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlConstructor254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254
open ArithmeticControlSimulation254 ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticControlClear254 ArithmeticControlPair254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlUnpairCore254 (UnpairCoreShape core_run)
open ArithmeticControlMP254 (Scale4Shape scale_run)
open FiniteControlTable254 RegisterPath

/-- A finite sequence of actual TW increments, with no semantic run premise. -/
inductive TagChain : Nat → Control → Control → Prop
  | nil (p : Control) : TagChain 0 p p
  | snoc {n : Nat} {p q r : Control} (prior : TagChain n p q)
      (edge : (source q).2 = .inc 1)
      (next : resolveControl (incPath (source q).1) = r) : TagChain (n + 1) p r

/-- Interfaces between checked loops and a bounded literal tag chain. -/
structure ConstructorShape where
  pop : UnpairCoreShape
  pair : PairShape
  scale : Scale4Shape
  tag : Fin 4
  exit : Control
  pop_main : pop.mainIndex = wsReg
  pop_to_pair : pop.exit = pair.copy.test
  pair_to_scale : pair.exit = scale.test
  tag_steps : TagChain tag.val scale.exit exit

/-- The next actual AX implication constructor starts at control195. -/
def impEntry : Control := ⟨195, by decide⟩
/-- Its zero-tag exit is immediately the next push, at control222. -/
def impExit : Control := ⟨222, by decide⟩

private def c196 : Control := ⟨196, by decide⟩
private def c197 : Control := ⟨197, by decide⟩
private def c198 : Control := ⟨198, by decide⟩
private def c199 : Control := ⟨199, by decide⟩
private def c200 : Control := ⟨200, by decide⟩
private def c201 : Control := ⟨201, by decide⟩
private def c202 : Control := ⟨202, by decide⟩
private def c203 : Control := ⟨203, by decide⟩
private def c204 : Control := ⟨204, by decide⟩
private def c205 : Control := ⟨205, by decide⟩
private def c206 : Control := ⟨206, by decide⟩
private def c207 : Control := ⟨207, by decide⟩
private def c208 : Control := ⟨208, by decide⟩
private def c209 : Control := ⟨209, by decide⟩
private def c210 : Control := ⟨210, by decide⟩
private def c211 : Control := ⟨211, by decide⟩
private def c212 : Control := ⟨212, by decide⟩
private def c213 : Control := ⟨213, by decide⟩
private def c214 : Control := ⟨214, by decide⟩
private def c215 : Control := ⟨215, by decide⟩
private def c216 : Control := ⟨216, by decide⟩
private def c217 : Control := ⟨217, by decide⟩
private def c218 : Control := ⟨218, by decide⟩
private def c219 : Control := ⟨219, by decide⟩
private def c220 : Control := ⟨220, by decide⟩
private def c221 : Control := ⟨221, by decide⟩

theorem impEntry_source : (source impEntry).2 = .decnz 2 := by rfl
theorem impExit_source : (source impExit).2 = .decnz 1 := by rfl

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

private def impPop : UnpairCoreShape where
  readEntry := impEntry
  bodyIncS2 := c196
  bodyTestS1 := c197
  bodyBreak := c198
  bodyMoveTest := c199
  bodyMoveInc := c200
  bodyMoveContinue := c201
  bodyContinue := c202
  restoreMainTest := c203
  restoreMainInc := c204
  restoreMainContinue := c205
  exit := c206
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
  next_read_positive := by
    apply literal_target <;> rfl
  next_read_zero := by
    apply literal_target <;> rfl
  next_body_inc := by
    apply literal_target <;> rfl
  next_body_test_positive := by
    apply literal_target <;> rfl
  next_body_test_zero := by
    apply literal_target <;> rfl
  next_body_break := by
    apply literal_target <;> rfl
  next_body_move_positive := by
    apply literal_target <;> rfl
  next_body_move_inc := by
    apply literal_target <;> rfl
  next_body_move_continue := by
    apply literal_target <;> rfl
  next_body_move_zero := by
    apply literal_target <;> rfl
  next_body_continue := by
    apply literal_target <;> rfl
  next_restore_main_positive := by
    apply literal_target <;> rfl
  next_restore_main_inc := by
    apply literal_target <;> rfl
  next_restore_main_continue := by
    apply literal_target <;> rfl
  next_restore_main_zero := by
    apply literal_target <;> rfl

private def impCopy : CopyShape where
  test := c206
  firstInc := c207
  secondInc := c208
  again := c209
  exit := c210
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

private def impMove : MoveShape where
  test := c212
  increment := c213
  again := c214
  exit := c215
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

private def impPair : PairShape where
  copy := impCopy
  testS1 := c210
  incS2 := c211
  move := impMove
  again := c215
  exit := c216
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

private def impScale : Scale4Shape where
  test := c216
  inc1 := c217
  inc2 := c218
  inc3 := c219
  inc4 := c220
  again := c221
  exit := impExit
  test_edge := by rfl
  inc1_edge := by rfl
  inc2_edge := by rfl
  inc3_edge := by rfl
  inc4_edge := by rfl
  again_edge := by rfl
  positive_target := by
    apply literal_target <;> rfl
  zero_target := by
    apply literal_target <;> rfl
  next_inc1 := by
    apply literal_target <;> rfl
  next_inc2 := by
    apply literal_target <;> rfl
  next_inc3 := by
    apply literal_target <;> rfl
  next_inc4 := by
    apply literal_target <;> rfl
  repeat_target := by
    apply literal_target <;> rfl

/-- Every field is a literal edge/target equality or interface equality. -/
def impConstructor : ConstructorShape where
  pop := impPop
  pair := impPair
  scale := impScale
  tag := 0
  exit := impExit
  pop_main := rfl
  pop_to_pair := rfl
  pair_to_scale := rfl
  tag_steps := TagChain.nil impExit

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) :
    regValue (put p x file) p = x := write_at file x p
private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h
private theorem put_same (p : Fin 9) (file : V) : put p (regValue file p) file = file :=
  write_same file p
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

/-- This finite induction concerns only a literal control chain; the file is internal. -/
theorem tagChain_run {n : Nat} {p q : Control} (chain : TagChain n p q) (file : V) :
    controlRun (n : V) (liveValue (number p : V) file) =
      liveValue (number q : V) (put twReg (regValue file twReg + (n : V)) file) := by
  induction chain generalizing file with
  | nil p => simp only [Nat.cast_zero, controlRun_zero, add_zero, put_same]
  | @snoc n p q r prior edge next ih =>
    rw [Nat.cast_add, Nat.cast_one, controlRun_succ, ih,
      increment q r edge next, read_put_self, put_twice]
    simp only [add_assoc]

/-- The middle consumes arbitrary S1 and requires only S2=0. -/
def middleFile (tag : Fin 4) (file : V) : V :=
  put twReg (tagged (tag.val : V) (regValue file s1Reg) (regValue file twReg))
    (put s1Reg 0 file)

theorem constructor_middle_run (c : ConstructorShape) (file : V)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number c.pair.copy.test : V) file) =
      liveValue (number c.exit : V) (middleFile c.tag file) := by
  let p := cantor (regValue file s1Reg) (regValue file twReg)
  let g := pairFile file 0 0 p
  have hp : ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number c.pair.copy.test : V) file) =
        liveValue (number c.scale.test : V)
          (pairFile file 0 0 (regValue file s2Reg + p)) := by
    simpa only [c.pair_to_scale, p] using pair_run c.pair file
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
  have hscale := scale_run c.scale g
  rw [hgs2, hgtw, zero_add] at hscale
  have htag := tagChain_run c.tag_steps scaled
  have hf : put twReg (regValue scaled twReg + (c.tag.val : V)) scaled = middleFile c.tag file := by
    apply file_ext
    intro i
    have hz : regValue file (5 : Fin 9) = 0 := h2
    by_cases hi2 : i = (2 : Fin 9)
    · subst i
      simp [read_put, scaled, g, pairFile, middleFile, p, tagged, twReg, s1Reg, s2Reg]
    by_cases hi8 : i = (8 : Fin 9)
    · subst i
      simp [read_put, scaled, g, pairFile, middleFile, twReg, s1Reg, s2Reg]
    by_cases hi5 : i = (5 : Fin 9)
    · subst i
      simp [read_put, scaled, g, pairFile, middleFile, twReg, s1Reg, s2Reg, hz]
    simp [read_put, scaled, g, pairFile, middleFile, twReg, s1Reg, s2Reg,
      Ne.symm hi2, Ne.symm hi8, Ne.symm hi5]
  rw [hf] at htag
  refine ⟨(tp + (6 * p + 1)) + (c.tag.val : V),
    le_trans htp (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le _))
      (le_add_of_nonneg_right (Arithmetic.zero_le _))), ?_⟩
  rw [controlRun_add (tp + (6 * p + 1)) (c.tag.val : V),
    controlRun_add tp (6 * p + 1), hpair, hscale]
  exact htag

/-- The complete file effect preserves all coordinates except TW and WS. -/
def constructorFile (tag : Fin 4) (file : V) : V :=
  put twReg (tagged (tag.val : V) (first (regValue file wsReg)) (regValue file twReg))
    (put wsReg (second (regValue file wsReg)) file)

theorem constructorFile_other (tag : Fin 4) (file : V) (i : Fin 9)
    (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (constructorFile tag file) i = regValue file i := by
  rw [constructorFile, read_put_other _ _ twReg i ht.symm,
    read_put_other _ _ wsReg i hs.symm]

/-- All unbounded clocks and data range over the arbitrary internal model. -/
theorem constructor_run (c : ConstructorShape) (file : V)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number c.pop.readEntry : V) file) =
      liveValue (number c.exit : V) (constructorFile c.tag file) := by
  let g := put s1Reg (first (regValue file wsReg))
    (put wsReg (second (regValue file wsReg)) file)
  have hp : ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number c.pop.readEntry : V) file) =
      liveValue (number c.pair.copy.test : V) g := by
    simpa only [c.pop_main, c.pop_to_pair, g] using core_run c.pop file h1 h2
  obtain ⟨tp, htp, hpop⟩ := hp
  have hg2 : regValue g s2Reg = 0 := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg s2Reg (by decide),
      read_put_other _ _ wsReg s2Reg (by decide)]
    exact h2
  have hf : middleFile c.tag g = constructorFile c.tag file := by
    apply file_ext
    intro i
    have hz : regValue file (8 : Fin 9) = 0 := h1
    by_cases hi2 : i = (2 : Fin 9)
    · subst i
      simp [read_put, middleFile, g, constructorFile, twReg, wsReg, s1Reg]
    by_cases hi0 : i = (0 : Fin 9)
    · subst i
      simp [read_put, middleFile, g, constructorFile, twReg, wsReg, s1Reg]
    by_cases hi8 : i = (8 : Fin 9)
    · subst i
      simp [read_put, middleFile, g, constructorFile, twReg, wsReg, s1Reg, hz]
    simp [read_put, middleFile, g, constructorFile, twReg, wsReg, s1Reg,
      Ne.symm hi2, Ne.symm hi0, Ne.symm hi8]
  obtain ⟨tm, _, hmiddle⟩ := constructor_middle_run c g hg2
  refine ⟨tp + tm, le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)), ?_⟩
  rw [controlRun_add, hpop, hmiddle, hf]

/-- The actual195→222 implication constructor, with every other field preserved. -/
theorem imp_constructor_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number impEntry : V) file) =
      liveValue (number impExit : V)
        (put twReg (wim (first (regValue file wsReg)) (regValue file twReg))
          (put wsReg (second (regValue file wsReg)) file)) := by
  simpa only [show impConstructor.pop.readEntry = impEntry from rfl,
    show impConstructor.exit = impExit from rfl,
    show impConstructor.tag = (0 : Fin 4) from rfl,
    constructorFile, Fin.val_zero, Nat.cast_zero, wim] using constructor_run impConstructor file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlConstructor254

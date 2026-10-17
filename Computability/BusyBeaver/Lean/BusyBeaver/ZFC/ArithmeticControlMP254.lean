import BusyBeaver.ZFC.ArithmeticControlUnpairCore254

set_option autoImplicit false
noncomputable section

/-!
The actual MP constructor middle block and full clean-scratch branch. All
control occurrences are bound separately; only internal IΣ1 arithmetic is used.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlClear254
open ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticControlFetch254 (put s1Reg fetchTest)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlDispatch254 (cacheReg mpEntry dispatchEntry dispatch_mp)
open ArithmeticControlCompare254 (compareEntry compareEntry_source compareFile)
open ArithmeticControlParamPush254 (paramPushFile mp_compare_tail_run)
open ArithmeticControlUnpairCore254 (mpConstructorEntry mpConstructorEntry_source mpInitialFile mp_initial_pop_run)
open FiniteControlTable254 RegisterPath

/-- The actual six-instruction scratch2-to-TW transfer with four increments. -/
structure Scale4Shape where
  test : Control
  inc1 : Control
  inc2 : Control
  inc3 : Control
  inc4 : Control
  again : Control
  exit : Control
  test_edge : (source test).2=.decnz 7
  inc1_edge : (source inc1).2=.inc 1
  inc2_edge : (source inc2).2=.inc 1
  inc3_edge : (source inc3).2=.inc 1
  inc4_edge : (source inc4).2=.inc 1
  again_edge : (source again).2=.cont 2
  positive_target : resolveControl (incPath (source test).1)=inc1
  zero_target : resolveControl (breakPath 1 (source test).1)=exit
  next_inc1 : resolveControl (incPath (source inc1).1)=inc2
  next_inc2 : resolveControl (incPath (source inc2).1)=inc3
  next_inc3 : resolveControl (incPath (source inc3).1)=inc4
  next_inc4 : resolveControl (incPath (source inc4).1)=again
  repeat_target : resolveControl (continuePath 2 (source again).1)=test

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem read_put_self (file x : V) (p : Fin 9) : regValue (put p x file) p=x :=
  write_at file x p
private theorem read_put_other (file x : V) (p q : Fin 9) (h : p≠q) :
    regValue (put p x file) q=regValue file q := write_other file x p q h
private theorem put_same (p : Fin 9) (file : V) : put p (regValue file p) file=file :=
  write_same file p
private theorem put_twice (p : Fin 9) (x y file : V) : put p y (put p x file)=put p y file :=
  write_overwrite file x y p
private theorem file_ext (x y : V) (h : ∀ i, regValue x i=regValue y i) : x=y := by
  rw [←file_reg x,←file_reg y]
  exact congrArg fileValue (funext h)
private theorem read_put (p q : Fin 9) (x file : V) :
    regValue (put p x file) q=if p=q then x else regValue file q := by
  by_cases h : p=q
  · subst q
    rw [if_pos rfl]
    exact read_put_self file x p
  · simpa only [if_neg h] using read_put_other file x p q h
private theorem put_commute (p q : Fin 9) (h : p≠q) (x y file : V) :
    put p x (put q y file)=put q y (put p x file) := by
  have hcast : (p.val : V)≠(q.val : V) := by
    intro he
    exact h (Fin.ext (by simpa only [Nat.cast_inj] using he))
  apply file_ext
  intro i
  simp only [put,reg_write]
  by_cases hp : (p.val : V)=(i.val : V)
  · by_cases hq : (q.val : V)=(i.val : V)
    · exact False.elim (hcast (hp.trans hq.symm))
    · simp only [hp,hq,if_true,if_false]
  · by_cases hq : (q.val : V)=(i.val : V) <;> simp only [hp,hq,if_true,if_false]

local instance write_definable : 𝚺₁-Function₃[V] writeValue := write_defined.to_definable
local instance live_definable : 𝚺₁-Function₂[V] liveValue := live_defined.to_definable
local instance reg_definable (p : Fin 9) : 𝚺₁-Function₁[V] (fun file => regValue file p) :=
  (projection_defined 8 p).to_definable

private theorem read_s2 (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 7) 0=regValue file s2Reg :=
  physicalValues_getD file s2Reg
private theorem read_tw (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 1) 0=regValue file twReg :=
  physicalValues_getD file twReg
private theorem run_one (state : V) : controlRun 1 state=ArithmeticControlStep254.stepValue state := by
  rw [show (1 : V)=0+1 by ring,controlRun_succ,controlRun_zero]
private theorem scale_positive (c : Scale4Shape) (file : V) (h : regValue file s2Reg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.inc1 : V) (put s2Reg (regValue file s2Reg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 7) 0≠0 := by rwa [read_s2]
  rw [step_decnz_positive c.test 7 c.test_edge file hn,c.positive_target,read_s2]
  rfl
private theorem scale_zero (c : Scale4Shape) (file : V) (h : regValue file s2Reg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 7) 0=0 := by rwa [read_s2]
  rw [step_decnz_zero c.test 7 c.test_edge file hz,c.zero_target]
private theorem increment (p q : Control) (edge : (source p).2=.inc 1)
    (next : resolveControl (incPath (source p).1)=q) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number p : V) file)=
      liveValue (number q : V) (put twReg (regValue file twReg+1) file) := by
  rw [step_inc p 1 edge,next,read_tw]
  rfl
private theorem scale_again (c : Scale4Shape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.again : V) file)=
      liveValue (number c.test : V) file := by
  rw [step_continue c.again 2 c.again_edge,c.repeat_target]
private theorem increment_four (c : Scale4Shape) (file : V) :
    controlRun 4 (liveValue (number c.inc1 : V) file)=
      liveValue (number c.again : V) (put twReg (regValue file twReg+4) file) := by
  rw [show (4 : V)=(((0+1)+1)+1)+1 by ring,
    controlRun_succ,controlRun_succ,controlRun_succ,controlRun_succ,controlRun_zero,
    increment c.inc1 c.inc2 c.inc1_edge c.next_inc1,
    increment c.inc2 c.inc3 c.inc2_edge c.next_inc2,
    increment c.inc3 c.inc4 c.inc3_edge c.next_inc3,
    increment c.inc4 c.again c.inc4_edge c.next_inc4]
  simp only [read_put_self,put_twice]
  rw [show (((regValue file twReg+1)+1)+1)+1=regValue file twReg+4 by ring]
  rw [show (0+1+1+1+1 : V)=4 by ring]

private def scaleCycle (file : V) : V :=
  put twReg (regValue file twReg+4) (put s2Reg (regValue file s2Reg-1) file)
private def scaleFile (file t : V) : V :=
  put twReg (regValue file twReg+4*t) (put s2Reg (regValue file s2Reg-t) file)
private theorem scaleFile_source (file t : V) :
    regValue (scaleFile file t) s2Reg=regValue file s2Reg-t := by
  rw [scaleFile,read_put_other _ _ twReg s2Reg (by decide),read_put_self]
private theorem scaleFile_target (file t : V) :
    regValue (scaleFile file t) twReg=regValue file twReg+4*t := by
  rw [scaleFile,read_put_self]
private theorem scaleFile_zero (file : V) : scaleFile file 0=file := by
  simp only [scaleFile,mul_zero,add_zero,tsub_zero,put_same]
private theorem scaleFile_succ (file t : V) :
    scaleCycle (scaleFile file t)=scaleFile file (t+1) := by
  rw [scaleCycle,scaleFile_source,scaleFile_target,
    show (regValue file twReg+4*t)+4=regValue file twReg+4*(t+1) by ring]
  simp only [scaleFile,put_commute s2Reg twReg (by decide),put_twice,←tsub_add_eq_tsub_tsub]

/-- One literal six-step iteration of the scaled transfer. -/
theorem scale_cycle (c : Scale4Shape) (file : V) (h : regValue file s2Reg≠0) :
    controlRun 6 (liveValue (number c.test : V) file)=
      liveValue (number c.test : V) (scaleCycle file) := by
  rw [show (6 : V)=(1+4)+1 by ring,controlRun_succ,controlRun_add,run_one,
    scale_positive c file h,increment_four,scale_again]
  simp only [scaleCycle,read_put_other _ _ s2Reg twReg (by decide)]

/-- Exact scaled transfer for arbitrary internal counters and target values. -/
theorem scale_run (c : Scale4Shape) (file : V) :
    controlRun (6*regValue file s2Reg+1) (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V)
        (put twReg (regValue file twReg+4*regValue file s2Reg) (put s2Reg 0 file)) := by
  let n := regValue file s2Reg
  have reach (t : V) : t≤n →
      controlRun (6*t) (liveValue (number c.test : V) file)=
        liveValue (number c.test : V) (scaleFile file t) := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold scaleFile put
      definability
    case zero => intro _; rw [mul_zero,controlRun_zero,scaleFile_zero]
    case succ t ih =>
      intro ht
      have hp := ih (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) ht)
      have hn : regValue (scaleFile file t) s2Reg≠0 := by
        rw [scaleFile_source]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) ht))
      rw [show 6*(t+1)=6*t+6 by ring,controlRun_add,hp,scale_cycle _ _ hn,scaleFile_succ]
  have hend := reach n le_rfl
  rw [controlRun_succ,hend,scale_zero c _ (by rw [scaleFile_source,tsub_self])]
  simp only [scaleFile,n,tsub_self]

end Model

private theorem literal_source (P Q : List Bool) (e : Edge)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0=some (e,Q.length))
    (hc : consume P Q.length=Q) : source (resolveControl P)=(Q,e) := by
  rw [resolve_source P e Q.length hw,hc]

def mpConstructorCopyS2 : Control := resolveControl (incPath (source mpConstructorEntry).1)
def mpConstructorCopyS1 : Control := resolveControl (incPath (source mpConstructorCopyS2).1)
def mpConstructorCopyAgain : Control := resolveControl (incPath (source mpConstructorCopyS1).1)
def mpConstructorTestS1 : Control := resolveControl (breakPath 1 (source mpConstructorEntry).1)
def mpConstructorIncS2 : Control := resolveControl (incPath (source mpConstructorTestS1).1)
def mpConstructorMoveTest : Control := resolveControl (incPath (source mpConstructorIncS2).1)
def mpConstructorMoveInc : Control := resolveControl (incPath (source mpConstructorMoveTest).1)
def mpConstructorMoveAgain : Control := resolveControl (incPath (source mpConstructorMoveInc).1)
def mpConstructorAgain : Control := resolveControl (breakPath 1 (source mpConstructorMoveTest).1)
def mpScaleTest : Control := resolveControl (breakPath 1 (source mpConstructorTestS1).1)
def mpScaleInc1 : Control := resolveControl (incPath (source mpScaleTest).1)
def mpScaleInc2 : Control := resolveControl (incPath (source mpScaleInc1).1)
def mpScaleInc3 : Control := resolveControl (incPath (source mpScaleInc2).1)
def mpScaleInc4 : Control := resolveControl (incPath (source mpScaleInc3).1)
def mpScaleAgain : Control := resolveControl (incPath (source mpScaleInc4).1)
def mpCompareMoveTest : Control := resolveControl (breakPath 1 (source mpScaleTest).1)
def mpCompareMoveInc : Control := resolveControl (incPath (source mpCompareMoveTest).1)
def mpCompareMoveAgain : Control := resolveControl (incPath (source mpCompareMoveInc).1)

theorem mpConstructorCopyS2_source : source mpConstructorCopyS2=([true,true,true,true,false,false,true,true,false,false,true,false],.inc 7) := by
  rw [mpConstructorCopyS2,mpConstructorEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpConstructorCopyS1_source : source mpConstructorCopyS1=([true,true,true,true,false,false,true,true,false,false,true,true,false],.inc 6) := by
  rw [mpConstructorCopyS1,mpConstructorCopyS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpConstructorCopyAgain_source : source mpConstructorCopyAgain=([true,true,true,true,false,false,true,true,false,false,true,true,true],.cont 3) := by
  rw [mpConstructorCopyAgain,mpConstructorCopyS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpConstructorTestS1_source : source mpConstructorTestS1=([true,true,true,true,false,false,true,true,false,true,false],.decnz 6) := by
  rw [mpConstructorTestS1,mpConstructorEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpConstructorIncS2_source : source mpConstructorIncS2=([true,true,true,true,false,false,true,true,false,true,true,false,false],.inc 7) := by
  rw [mpConstructorIncS2,mpConstructorTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpConstructorMoveTest_source : source mpConstructorMoveTest=([true,true,true,true,false,false,true,true,false,true,true,false,true,false],.decnz 6) := by
  rw [mpConstructorMoveTest,mpConstructorIncS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpConstructorMoveInc_source : source mpConstructorMoveInc=([true,true,true,true,false,false,true,true,false,true,true,false,true,true,false],.inc 1) := by
  rw [mpConstructorMoveInc,mpConstructorMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpConstructorMoveAgain_source : source mpConstructorMoveAgain=([true,true,true,true,false,false,true,true,false,true,true,false,true,true,true],.cont 2) := by
  rw [mpConstructorMoveAgain,mpConstructorMoveInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpConstructorAgain_source : source mpConstructorAgain=([true,true,true,true,false,false,true,true,false,true,true,true],.cont 3) := by
  rw [mpConstructorAgain,mpConstructorMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpScaleTest_source : source mpScaleTest=([true,true,true,true,false,false,true,true,true,false],.decnz 7) := by
  rw [mpScaleTest,mpConstructorTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpScaleInc1_source : source mpScaleInc1=([true,true,true,true,false,false,true,true,true,true,false,false,false],.inc 1) := by
  rw [mpScaleInc1,mpScaleTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpScaleInc2_source : source mpScaleInc2=([true,true,true,true,false,false,true,true,true,true,false,false,true],.inc 1) := by
  rw [mpScaleInc2,mpScaleInc1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpScaleInc3_source : source mpScaleInc3=([true,true,true,true,false,false,true,true,true,true,false,true,false],.inc 1) := by
  rw [mpScaleInc3,mpScaleInc2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpScaleInc4_source : source mpScaleInc4=([true,true,true,true,false,false,true,true,true,true,false,true,true],.inc 1) := by
  rw [mpScaleInc4,mpScaleInc3_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpScaleAgain_source : source mpScaleAgain=([true,true,true,true,false,false,true,true,true,true,true],.cont 2) := by
  rw [mpScaleAgain,mpScaleInc4_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCompareMoveTest_source : source mpCompareMoveTest=([true,true,true,true,false,true,false],.decnz 1) := by
  rw [mpCompareMoveTest,mpScaleTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCompareMoveInc_source : source mpCompareMoveInc=([true,true,true,true,false,true,true,false],.inc 6) := by
  rw [mpCompareMoveInc,mpCompareMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCompareMoveAgain_source : source mpCompareMoveAgain=([true,true,true,true,false,true,true,true],.cont 2) := by
  rw [mpCompareMoveAgain,mpCompareMoveInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

def mpConstructorCopy : CopyShape where
  test := mpConstructorEntry
  firstInc := mpConstructorCopyS2
  secondInc := mpConstructorCopyS1
  again := mpConstructorCopyAgain
  exit := mpConstructorTestS1
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
  test_edge := congrArg Prod.snd mpConstructorEntry_source
  first_edge := congrArg Prod.snd mpConstructorCopyS2_source
  second_edge := congrArg Prod.snd mpConstructorCopyS1_source
  again_edge := congrArg Prod.snd mpConstructorCopyAgain_source
  positive_target := by
    apply source_injective
    rw [mpConstructorEntry_source,mpConstructorCopyS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  first_target := by
    apply source_injective
    rw [mpConstructorCopyS2_source,mpConstructorCopyS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  second_target := by
    apply source_injective
    rw [mpConstructorCopyS1_source,mpConstructorCopyAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpConstructorCopyAgain_source,mpConstructorEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpConstructorEntry_source,mpConstructorTestS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpConstructorMove : MoveShape where
  test := mpConstructorMoveTest
  increment := mpConstructorMoveInc
  again := mpConstructorMoveAgain
  exit := mpConstructorAgain
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd mpConstructorMoveTest_source
  increment_edge := congrArg Prod.snd mpConstructorMoveInc_source
  again_edge := congrArg Prod.snd mpConstructorMoveAgain_source
  positive_target := by
    apply source_injective
    rw [mpConstructorMoveTest_source,mpConstructorMoveInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [mpConstructorMoveInc_source,mpConstructorMoveAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpConstructorMoveAgain_source,mpConstructorMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpConstructorMoveTest_source,mpConstructorAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpConstructorPair : PairShape where
  copy := mpConstructorCopy
  testS1 := mpConstructorTestS1
  incS2 := mpConstructorIncS2
  move := mpConstructorMove
  again := mpConstructorAgain
  exit := mpScaleTest
  copy_source := rfl
  copy_first := rfl
  copy_second := rfl
  copy_exit := by simp only [mpConstructorCopy]
  move_source := rfl
  move_target := rfl
  move_exit := by simp only [mpConstructorMove]
  test_edge := congrArg Prod.snd mpConstructorTestS1_source
  increment_edge := congrArg Prod.snd mpConstructorIncS2_source
  again_edge := congrArg Prod.snd mpConstructorAgain_source
  positive_target := by
    apply source_injective
    rw [mpConstructorTestS1_source,mpConstructorIncS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpConstructorTestS1_source,mpScaleTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    dsimp only [mpConstructorMove]
    apply source_injective
    rw [mpConstructorIncS2_source,mpConstructorMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    dsimp only [mpConstructorCopy]
    apply source_injective
    rw [mpConstructorAgain_source,mpConstructorEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpScale : Scale4Shape where
  test := mpScaleTest
  inc1 := mpScaleInc1
  inc2 := mpScaleInc2
  inc3 := mpScaleInc3
  inc4 := mpScaleInc4
  again := mpScaleAgain
  exit := mpCompareMoveTest
  test_edge := congrArg Prod.snd mpScaleTest_source
  inc1_edge := congrArg Prod.snd mpScaleInc1_source
  inc2_edge := congrArg Prod.snd mpScaleInc2_source
  inc3_edge := congrArg Prod.snd mpScaleInc3_source
  inc4_edge := congrArg Prod.snd mpScaleInc4_source
  again_edge := congrArg Prod.snd mpScaleAgain_source
  positive_target := by
    apply source_injective
    rw [mpScaleTest_source,mpScaleInc1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpScaleTest_source,mpCompareMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_inc1 := by
    apply source_injective
    rw [mpScaleInc1_source,mpScaleInc2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_inc2 := by
    apply source_injective
    rw [mpScaleInc2_source,mpScaleInc3_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_inc3 := by
    apply source_injective
    rw [mpScaleInc3_source,mpScaleInc4_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_inc4 := by
    apply source_injective
    rw [mpScaleInc4_source,mpScaleAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpScaleAgain_source,mpScaleTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpCompareMove : MoveShape where
  test := mpCompareMoveTest
  increment := mpCompareMoveInc
  again := mpCompareMoveAgain
  exit := compareEntry
  sourceLogical := 1
  targetLogical := 6
  sourceIndex := twReg
  targetIndex := s1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd mpCompareMoveTest_source
  increment_edge := congrArg Prod.snd mpCompareMoveInc_source
  again_edge := congrArg Prod.snd mpCompareMoveAgain_source
  positive_target := by
    apply source_injective
    rw [mpCompareMoveTest_source,mpCompareMoveInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [mpCompareMoveInc_source,mpCompareMoveAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpCompareMoveAgain_source,mpCompareMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpCompareMoveTest_source,compareEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local instance : DecidableEq V := Classical.decEq V

/-- Constructor and transfer output immediately before the comparison. -/
def mpMiddleFile (file : V) : V :=
  put s1Reg (wim (regValue file s1Reg) (regValue file twReg)) (put twReg 0 file)

/-- Actual constructor pairing, scaled transfer and final TW-to-scratch1 move.
Only scratch2 is required to be zero at this entry. -/
theorem mp_middle_run (file : V) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpConstructorEntry : V) file)=
      liveValue (number compareEntry : V) (mpMiddleFile file) := by
  let p := cantor (regValue file s1Reg) (regValue file twReg)
  let g := pairFile file 0 0 p
  have hp : ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number mpConstructorEntry : V) file)=
        liveValue (number mpScaleTest : V) (pairFile file 0 0 (regValue file s2Reg+p)) := by
    simpa only [mpConstructorPair,mpConstructorCopy,p] using pair_run mpConstructorPair file
  obtain ⟨tp,_,hpair⟩ := hp
  rw [h2,zero_add] at hpair
  have hgs2 : regValue g s2Reg=p := by
    dsimp only [g,pairFile]
    rw [read_put_other _ _ s1Reg s2Reg (by decide),read_put_self]
  have hgtw : regValue g twReg=0 := by
    dsimp only [g,pairFile]
    rw [read_put_other _ _ s1Reg twReg (by decide),
      read_put_other _ _ s2Reg twReg (by decide),read_put_self]
  let scaled := put twReg (4*p) (put s2Reg 0 g)
  have hscale := scale_run mpScale g
  simp only [mpScale] at hscale
  rw [hgs2,hgtw,zero_add] at hscale
  have hscaledtw : regValue scaled twReg=4*p := read_put_self _ _ _
  have hscaleds1 : regValue scaled s1Reg=0 := by
    dsimp only [scaled,g,pairFile]
    rw [read_put_other _ _ twReg s1Reg (by decide),
      read_put_other _ _ s2Reg s1Reg (by decide),read_put_self]
  have hmove := move_run mpCompareMove scaled
  simp only [mpCompareMove] at hmove
  rw [hscaledtw,hscaleds1,zero_add] at hmove
  have hf : put s1Reg (4*p) (put twReg 0 scaled)=mpMiddleFile file := by
    apply file_ext
    intro i
    by_cases hi8 : i=(8 : Fin 9)
    · subst i
      simp [read_put,scaled,g,pairFile,mpMiddleFile,p,wim,tagged,twReg,s1Reg,s2Reg]
    by_cases hi2 : i=(2 : Fin 9)
    · subst i
      simp [read_put,scaled,g,pairFile,mpMiddleFile,twReg,s1Reg,s2Reg]
    by_cases hi5 : i=(5 : Fin 9)
    · subst i
      have hz : regValue file (5 : Fin 9)=0 := h2
      simp [read_put,scaled,g,pairFile,mpMiddleFile,twReg,s1Reg,s2Reg,hz]
    simp [read_put,scaled,g,pairFile,mpMiddleFile,twReg,s1Reg,s2Reg,
      Ne.symm hi8,Ne.symm hi2,Ne.symm hi5]
  refine ⟨(tp+(6*p+1))+(3*(4*p)+1),?_,?_⟩
  · rw [show (tp+(6*p+1))+(3*(4*p)+1)=((tp+(6*p+1))+3*(4*p))+1 by ring]
    exact le_add_of_nonneg_left (Arithmetic.zero_le _)
  · rw [controlRun_add (tp+(6*p+1)) (3*(4*p)+1),
      controlRun_add tp (6*p+1),hpair,hscale,hmove,hf]

/-- Complete file effect of the actual MP branch after parameter decoding. -/
def mpFile (file : V) : V :=
  if wim (regValue file twReg) (regValue file p1Reg)=regValue file cacheReg then
    put twReg (regValue file p1Reg)
      (put wsReg (cantor 0 (regValue file wsReg)) (put cacheReg 0 file))
  else put twReg 0 (put cacheReg 0 file)

private theorem cleared_file (file : V) (h1 : regValue file s1Reg=0) :
    compareFile (mpMiddleFile (mpInitialFile file)) 0 0=put twReg 0 (put cacheReg 0 file) := by
  apply file_ext
  intro i
  by_cases hi8 : i=(8 : Fin 9)
  · subst i
    have hz : regValue file (8 : Fin 9)=0 := h1
    simp [read_put,compareFile,mpMiddleFile,mpInitialFile,twReg,s1Reg,cacheReg,hz]
  by_cases hi2 : i=(2 : Fin 9)
  · subst i
    simp [read_put,compareFile,mpMiddleFile,mpInitialFile,twReg,s1Reg,cacheReg]
  by_cases hi7 : i=(7 : Fin 9)
  · subst i
    simp [read_put,compareFile,mpMiddleFile,mpInitialFile,twReg,s1Reg,cacheReg]
  simp [read_put,compareFile,mpMiddleFile,mpInitialFile,twReg,s1Reg,cacheReg,
    Ne.symm hi8,Ne.symm hi2,Ne.symm hi7]
private theorem success_file (file : V) :
    paramPushFile (put twReg 0 (put cacheReg 0 file))=
      put twReg (regValue file p1Reg)
        (put wsReg (cantor 0 (regValue file wsReg)) (put cacheReg 0 file)) := by
  simp only [paramPushFile,read_put_other _ _ twReg p1Reg (by decide),
    read_put_other _ _ cacheReg p1Reg (by decide),read_put_self,
    read_put_other _ _ twReg wsReg (by decide),read_put_other _ _ cacheReg wsReg (by decide),
    put_commute wsReg twReg (by decide),put_twice]

/-- Actual MP: constructor equality selects the genuine zero-filler success
push; failure clears TW. Cache and both scratch fields are zero at return. -/
theorem mp_run (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpEntry : V) file)=
      liveValue (number fetchTest : V) (mpFile file) := by
  obtain ⟨ta,_,hstart⟩ := mp_initial_pop_run file h1 h2
  have hn2 : regValue (mpInitialFile file) s2Reg=0 := by
    rw [mpInitialFile,read_put_other _ _ s1Reg s2Reg (by decide),
      read_put_other _ _ twReg s2Reg (by decide)]
    exact h2
  obtain ⟨tb,_,hmid⟩ := mp_middle_run (mpInitialFile file) hn2
  let m := mpMiddleFile (mpInitialFile file)
  have hm1 : regValue m s1Reg=wim (regValue file twReg) (regValue file p1Reg) := by
    dsimp only [m,mpMiddleFile]
    rw [read_put_self,mpInitialFile,read_put_self,
      read_put_other _ _ s1Reg twReg (by decide),read_put_self]
  have hmc : regValue m cacheReg=regValue file cacheReg := by
    dsimp only [m,mpMiddleFile,mpInitialFile]
    rw [read_put_other _ _ s1Reg cacheReg (by decide),
      read_put_other _ _ twReg cacheReg (by decide),
      read_put_other _ _ s1Reg cacheReg (by decide),
      read_put_other _ _ twReg cacheReg (by decide)]
  have hm2 : regValue m s2Reg=0 := by
    dsimp only [m,mpMiddleFile]
    rw [read_put_other _ _ s1Reg s2Reg (by decide),
      read_put_other _ _ twReg s2Reg (by decide)]
    exact hn2
  obtain ⟨tc,htc,htail⟩ := mp_compare_tail_run m hm2
  rw [hm1,hmc,cleared_file file h1,success_file] at htail
  have hend : controlRun tc (liveValue (number compareEntry : V) m)=
      liveValue (number fetchTest : V) (mpFile file) := by
    by_cases he : wim (regValue file twReg) (regValue file p1Reg)=regValue file cacheReg
    · simpa only [mpFile,if_pos he] using htail
    · simpa only [mpFile,if_neg he] using htail
  refine ⟨(ta+tb)+tc,le_trans htc (le_add_of_nonneg_left (Arithmetic.zero_le (ta+tb))),?_⟩
  rw [controlRun_add (ta+tb) tc,controlRun_add ta tb,hstart,hmid,hend]

/-- AC=0 classification followed by the complete actual MP branch. -/
theorem dispatch_mp_run (file : V) (ha : regValue file acReg=0)
    (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number dispatchEntry : V) file)=
      liveValue (number fetchTest : V) (mpFile file) := by
  obtain ⟨time,_,h⟩ := mp_run file h1 h2
  refine ⟨1+time,le_add_of_nonneg_right (Arithmetic.zero_le time),?_⟩
  rw [controlRun_add,dispatch_mp file ha,h]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlMP254

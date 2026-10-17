import BusyBeaver.ZFC.ArithmeticControlNip254

set_option autoImplicit false
noncomputable section

/-!
A source-parameterized finite unpair shape in the actual numbered interpreter.
Its runtime is proved from literal edges/resolved continuations, with explicit
main/target physical bindings and scratch disjointness. All values may be
internal to an IΣ1 model; no complete L2/Enum equivalence is established here.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 FiniteControlTable254 RegisterPath
open ArithmeticControlRead254 (s2Reg)

/-- External finite controls from the actual catalogue, never an execution
oracle. Every step in the template is specified by an actual source equality
and its actual resolved continuation. -/
structure UnpairShape where
  readEntry : Control
  bodyIncS2 : Control
  bodyTestS1 : Control
  bodyBreak : Control
  bodyMoveTest : Control
  bodyMoveInc : Control
  bodyMoveContinue : Control
  bodyContinue : Control
  restoreMainTest : Control
  restoreMainInc : Control
  restoreMainContinue : Control
  outputTest : Control
  outputInc : Control
  outputContinue : Control
  nextRead : Control
  mainLogical : Nat
  mainIndex : Fin 9
  main_physical : Permutation252Frame.physOf mainLogical=mainIndex.val
  main_ne_s1 : mainIndex≠s1Reg
  main_ne_s2 : mainIndex≠s2Reg
  targetLogical : Nat
  targetIndex : Fin 9
  target_physical : Permutation252Frame.physOf targetLogical=targetIndex.val
  target_ne_s1 : targetIndex≠s1Reg
  target_ne_s2 : targetIndex≠s2Reg
  target_ne_main : targetIndex≠mainIndex
  read_edge : (source readEntry).2=.decnz mainLogical
  body_inc_edge : (source bodyIncS2).2=.inc 7
  body_test_edge : (source bodyTestS1).2=.decnz 6
  body_break_edge : (source bodyBreak).2=.brk 1
  body_move_test_edge : (source bodyMoveTest).2=.decnz 7
  body_move_inc_edge : (source bodyMoveInc).2=.inc 6
  body_move_continue_edge : (source bodyMoveContinue).2=.cont 2
  body_continue_edge : (source bodyContinue).2=.cont 3
  restore_test_edge : (source restoreMainTest).2=.decnz 7
  restore_inc_edge : (source restoreMainInc).2=.inc mainLogical
  restore_continue_edge : (source restoreMainContinue).2=.cont 2
  output_test_edge : (source outputTest).2=.decnz 6
  output_inc_edge : (source outputInc).2=.inc targetLogical
  output_continue_edge : (source outputContinue).2=.cont 2
  next_read_positive : resolveControl (incPath (source readEntry).1)=bodyIncS2
  next_read_zero : resolveControl (breakPath 1 (source readEntry).1)=restoreMainTest
  next_body_inc : resolveControl (incPath (source bodyIncS2).1)=bodyTestS1
  next_body_test_positive : resolveControl (incPath (source bodyTestS1).1)=bodyBreak
  next_body_test_zero : resolveControl (breakPath 1 (source bodyTestS1).1)=bodyMoveTest
  next_body_break : resolveControl (breakPath 1 (source bodyBreak).1)=bodyContinue
  next_body_move_positive : resolveControl (incPath (source bodyMoveTest).1)=bodyMoveInc
  next_body_move_inc : resolveControl (incPath (source bodyMoveInc).1)=bodyMoveContinue
  next_body_move_continue : resolveControl (continuePath 2 (source bodyMoveContinue).1)=bodyMoveTest
  next_body_move_zero : resolveControl (breakPath 1 (source bodyMoveTest).1)=bodyContinue
  next_body_continue : resolveControl (continuePath 3 (source bodyContinue).1)=readEntry
  next_restore_main_positive : resolveControl (incPath (source restoreMainTest).1)=restoreMainInc
  next_restore_main_inc : resolveControl (incPath (source restoreMainInc).1)=restoreMainContinue
  next_restore_main_continue : resolveControl (continuePath 2 (source restoreMainContinue).1)=restoreMainTest
  next_restore_main_zero : resolveControl (breakPath 1 (source restoreMainTest).1)=outputTest
  next_output_positive : resolveControl (incPath (source outputTest).1)=outputInc
  next_output_inc : resolveControl (incPath (source outputInc).1)=outputContinue
  next_output_continue : resolveControl (continuePath 2 (source outputContinue).1)=outputTest
  next_output_zero : resolveControl (breakPath 1 (source outputTest).1)=nextRead

/-- Private proof substrate, instantiated below at three literal transfer
loops. Every control/edge/target premise is a fact about the actual catalogue. -/
private structure TransferShape where
  test : Control
  increment : Control
  again : Control
  exit : Control
  sourceLogical : Nat
  targetLogical : Nat
  sourceIndex : Fin 9
  targetIndex : Fin 9
  source_physical : Permutation252Frame.physOf sourceLogical=sourceIndex.val
  target_physical : Permutation252Frame.physOf targetLogical=targetIndex.val
  distinct : sourceIndex≠targetIndex
  test_edge : (source test).2=.decnz sourceLogical
  increment_edge : (source increment).2=.inc targetLogical
  again_edge : (source again).2=.cont 2
  positive_target : resolveControl (incPath (source test).1)=increment
  increment_target : resolveControl (incPath (source increment).1)=again
  repeat_target : resolveControl (continuePath 2 (source again).1)=test
  zero_target : resolveControl (breakPath 1 (source test).1)=exit

private def bodyTransfer (c : UnpairShape) : TransferShape where
  test := c.bodyMoveTest
  increment := c.bodyMoveInc
  again := c.bodyMoveContinue
  exit := c.bodyContinue
  sourceLogical := 7
  targetLogical := 6
  sourceIndex := s2Reg
  targetIndex := s1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := c.body_move_test_edge
  increment_edge := c.body_move_inc_edge
  again_edge := c.body_move_continue_edge
  positive_target := c.next_body_move_positive
  increment_target := c.next_body_move_inc
  repeat_target := c.next_body_move_continue
  zero_target := c.next_body_move_zero

private def restoreMainTransfer (c : UnpairShape) : TransferShape where
  test := c.restoreMainTest
  increment := c.restoreMainInc
  again := c.restoreMainContinue
  exit := c.outputTest
  sourceLogical := 7
  targetLogical := c.mainLogical
  sourceIndex := s2Reg
  targetIndex := c.mainIndex
  source_physical := rfl
  target_physical := c.main_physical
  distinct := c.main_ne_s2.symm
  test_edge := c.restore_test_edge
  increment_edge := c.restore_inc_edge
  again_edge := c.restore_continue_edge
  positive_target := c.next_restore_main_positive
  increment_target := c.next_restore_main_inc
  repeat_target := c.next_restore_main_continue
  zero_target := c.next_restore_main_zero

private def outputTransfer (c : UnpairShape) : TransferShape where
  test := c.outputTest
  increment := c.outputInc
  again := c.outputContinue
  exit := c.nextRead
  sourceLogical := 6
  targetLogical := c.targetLogical
  sourceIndex := s1Reg
  targetIndex := c.targetIndex
  source_physical := rfl
  target_physical := c.target_physical
  distinct := c.target_ne_s1.symm
  test_edge := c.output_test_edge
  increment_edge := c.output_inc_edge
  again_edge := c.output_continue_edge
  positive_target := c.next_output_positive
  increment_target := c.next_output_inc
  repeat_target := c.next_output_continue
  zero_target := c.next_output_zero

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (c : UnpairShape)
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
local instance first_definable : 𝚺₀-Function₁[V] first := first_defined.to_definable
local instance second_definable : 𝚺₀-Function₁[V] second := second_defined.to_definable
local instance reg_definable (p : Fin 9) : 𝚺₁-Function₁[V] (fun file => regValue file p) :=
  (projection_defined 8 p).to_definable

private theorem transfer_read_source (c : TransferShape) (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf c.sourceLogical) 0=
      regValue file c.sourceIndex := by
  rw [c.source_physical]
  exact physicalValues_getD file c.sourceIndex
private theorem transfer_read_target (c : TransferShape) (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf c.targetLogical) 0=
      regValue file c.targetIndex := by
  rw [c.target_physical]
  exact physicalValues_getD file c.targetIndex
private theorem transfer_step_positive (c : TransferShape) (file : V)
    (h : regValue file c.sourceIndex≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.increment : V)
        (put c.sourceIndex (regValue file c.sourceIndex-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf c.sourceLogical) 0≠0 := by
    rwa [transfer_read_source]
  rw [step_decnz_positive c.test c.sourceLogical c.test_edge file hn,
    c.positive_target,transfer_read_source]
  simp only [put,c.source_physical]
private theorem transfer_step_zero (c : TransferShape) (file : V)
    (h : regValue file c.sourceIndex=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf c.sourceLogical) 0=0 := by
    rwa [transfer_read_source]
  rw [step_decnz_zero c.test c.sourceLogical c.test_edge file hz,c.zero_target]
private theorem transfer_step_increment (c : TransferShape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.increment : V) file)=
      liveValue (number c.again : V)
        (put c.targetIndex (regValue file c.targetIndex+1) file) := by
  rw [step_inc c.increment c.targetLogical c.increment_edge,c.increment_target,transfer_read_target]
  simp only [put,c.target_physical]
private theorem transfer_step_again (c : TransferShape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.again : V) file)=
      liveValue (number c.test : V) file := by
  rw [step_continue c.again 2 c.again_edge,c.repeat_target]

private def transferFile (c : TransferShape) (file t : V) : V :=
  put c.targetIndex (regValue file c.targetIndex+t)
    (put c.sourceIndex (regValue file c.sourceIndex-t) file)
private def transferCycle (c : TransferShape) (file : V) : V :=
  put c.targetIndex (regValue file c.targetIndex+1)
    (put c.sourceIndex (regValue file c.sourceIndex-1) file)
private theorem transferFile_source (c : TransferShape) (file t : V) :
    regValue (transferFile c file t) c.sourceIndex=regValue file c.sourceIndex-t := by
  rw [transferFile,read_put_other _ _ c.targetIndex c.sourceIndex c.distinct.symm,read_put_self]
private theorem transferFile_target (c : TransferShape) (file t : V) :
    regValue (transferFile c file t) c.targetIndex=regValue file c.targetIndex+t := by
  rw [transferFile,read_put_self]
private theorem transferFile_zero (c : TransferShape) (file : V) : transferFile c file 0=file := by
  simp only [transferFile,add_zero,tsub_zero,put_same]
private theorem transferFile_succ (c : TransferShape) (file t : V) :
    transferCycle c (transferFile c file t)=transferFile c file (t+1) := by
  rw [transferCycle,transferFile_source,transferFile_target]
  simp only [transferFile,put_commute c.sourceIndex c.targetIndex c.distinct,
    put_twice,←tsub_add_eq_tsub_tsub,add_assoc]
private theorem transfer_cycle (c : TransferShape) (file : V)
    (h : regValue file c.sourceIndex≠0) :
    controlRun 3 (liveValue (number c.test : V) file)=
      liveValue (number c.test : V) (transferCycle c file) := by
  rw [show (3 : V)=((0+1)+1)+1 by ring,
    controlRun_succ,controlRun_succ,controlRun_succ,controlRun_zero,
    transfer_step_positive c file h,transfer_step_increment,transfer_step_again]
  simp only [transferCycle,read_put_other _ _ c.sourceIndex c.targetIndex c.distinct]
private theorem transfer_run (c : TransferShape) (file : V) :
    controlRun (3*regValue file c.sourceIndex+1) (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V) (transferFile c file (regValue file c.sourceIndex)) := by
  let n := regValue file c.sourceIndex
  have reach (t : V) : t≤n →
      controlRun (3*t) (liveValue (number c.test : V) file)=
        liveValue (number c.test : V) (transferFile c file t) := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold transferFile put
      definability
    case zero => intro _; rw [mul_zero,controlRun_zero,transferFile_zero]
    case succ t ih =>
      intro ht
      have hp := ih (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) ht)
      have hn : regValue (transferFile c file t) c.sourceIndex≠0 := by
        rw [transferFile_source]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) ht))
      rw [show 3*(t+1)=3*t+3 by ring,controlRun_add,hp,transfer_cycle _ _ hn,transferFile_succ]
  have hend := reach n le_rfl
  rw [controlRun_succ,hend,transfer_step_zero c _ (by rw [transferFile_source,tsub_self])]

/-- Actual nested body transfer, including its zero exit at the body continue. -/
theorem move_s2_s1 (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.bodyMoveTest : V) file)=
      liveValue (number c.bodyContinue : V)
        (put s1Reg (regValue file s1Reg+regValue file s2Reg) (put s2Reg 0 file)) := by
  simpa only [transferFile,bodyTransfer,tsub_self] using transfer_run (bodyTransfer c) file
/-- Actual restoration of the second Cantor component into the main field. -/
theorem move_s2_main (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.restoreMainTest : V) file)=
      liveValue (number c.outputTest : V)
        (put c.mainIndex (regValue file c.mainIndex+regValue file s2Reg) (put s2Reg 0 file)) := by
  simpa only [transferFile,restoreMainTransfer,tsub_self] using transfer_run (restoreMainTransfer c) file
/-- Actual transfer of the first Cantor component into the shape target. -/
theorem move_s1_target (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number c.outputTest : V) file)=
      liveValue (number c.nextRead : V)
        (put c.targetIndex (regValue file c.targetIndex+regValue file s1Reg) (put s1Reg 0 file)) := by
  simpa only [transferFile,outputTransfer,tsub_self] using transfer_run (outputTransfer c) file

private theorem read_main (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf c.mainLogical) 0=regValue file c.mainIndex := by
  rw [c.main_physical]
  exact physicalValues_getD file c.mainIndex
private theorem read_s1 (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 6) 0=regValue file s1Reg :=
  physicalValues_getD file s1Reg
private theorem read_s2 (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 7) 0=regValue file s2Reg :=
  physicalValues_getD file s2Reg
private theorem run_one (state : V) : controlRun 1 state=ArithmeticControlStep254.stepValue state := by
  rw [show (1 : V)=0+1 by ring,controlRun_succ,controlRun_zero]
private theorem step_read_positive (file : V) (h : regValue file c.mainIndex≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.readEntry : V) file)=
      liveValue (number c.bodyIncS2 : V) (put c.mainIndex (regValue file c.mainIndex-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf c.mainLogical) 0≠0 := by rwa [read_main]
  rw [step_decnz_positive c.readEntry c.mainLogical (c.read_edge) file hn,
    c.next_read_positive,read_main]
  simp only [put,c.main_physical]
private theorem step_read_zero (file : V) (h : regValue file c.mainIndex=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.readEntry : V) file)=
      liveValue (number c.restoreMainTest : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf c.mainLogical) 0=0 := by rwa [read_main]
  rw [step_decnz_zero c.readEntry c.mainLogical (c.read_edge) file hz,c.next_read_zero]
private theorem step_body_inc (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.bodyIncS2 : V) file)=
      liveValue (number c.bodyTestS1 : V) (put s2Reg (regValue file s2Reg+1) file) := by
  rw [step_inc c.bodyIncS2 7 (c.body_inc_edge),c.next_body_inc,read_s2]
  rfl
private theorem step_body_test_positive (file : V) (h : regValue file s1Reg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.bodyTestS1 : V) file)=
      liveValue (number c.bodyBreak : V) (put s1Reg (regValue file s1Reg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 6) 0≠0 := by rwa [read_s1]
  rw [step_decnz_positive c.bodyTestS1 6 (c.body_test_edge) file hn,
    c.next_body_test_positive,read_s1]
  rfl
private theorem step_body_test_zero (file : V) (h : regValue file s1Reg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.bodyTestS1 : V) file)=
      liveValue (number c.bodyMoveTest : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 6) 0=0 := by rwa [read_s1]
  rw [step_decnz_zero c.bodyTestS1 6 (c.body_test_edge) file hz,c.next_body_test_zero]
private theorem step_body_break (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.bodyBreak : V) file)=
      liveValue (number c.bodyContinue : V) file := by
  rw [step_break c.bodyBreak 1 (c.body_break_edge),c.next_body_break]
private theorem step_body_continue (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.bodyContinue : V) file)=
      liveValue (number c.readEntry : V) file := by
  rw [step_continue c.bodyContinue 3 (c.body_continue_edge),c.next_body_continue]

local instance : DecidableEq V := Classical.decEq V

/-- Exact scratch-coordinate change of one actual unpair-walk body. -/
def bodyFile (file : V) : V :=
  put s1Reg (if regValue file s1Reg=0 then regValue file s2Reg+1 else regValue file s1Reg-1)
    (put s2Reg (if regValue file s1Reg=0 then 0 else regValue file s2Reg+1) file)
def bodyClock (file : V) : V :=
  if regValue file s1Reg=0 then 3*(regValue file s2Reg+1)+4 else 4

/-- This local body starts after the outer main decrement and returns to that
same actual read test. Its nested variable transfer is fully discharged. -/
theorem body_run (file : V) :
    controlRun (bodyClock file) (liveValue (number c.bodyIncS2 : V) file)=
      liveValue (number c.readEntry : V) (bodyFile file) := by
  let g := put s2Reg (regValue file s2Reg+1) file
  by_cases hs : regValue file s1Reg=0
  · have hg : regValue g s1Reg=0 := by
      dsimp only [g]
      rw [read_put_other _ _ s2Reg s1Reg (by decide)]
      exact hs
    have hfirst : controlRun 2 (liveValue (number c.bodyIncS2 : V) file)=
        liveValue (number c.bodyMoveTest : V) g := by
      rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,step_body_inc c,step_body_test_zero c g hg]
    have hm := move_s2_s1 c g
    rw [show regValue g s2Reg=regValue file s2Reg+1 by exact read_put_self _ _ s2Reg,hg,zero_add] at hm
    have hf : put s1Reg (regValue file s2Reg+1) (put s2Reg 0 g)=bodyFile file := by
      simp only [bodyFile,hs,if_true,g,put_twice]
    rw [bodyClock,if_pos hs,
      show 3*(regValue file s2Reg+1)+4=(2+(3*(regValue file s2Reg+1)+1))+1 by ring,
      controlRun_add (2+(3*(regValue file s2Reg+1)+1)) 1 (liveValue (number c.bodyIncS2 : V) file),
      controlRun_add 2 (3*(regValue file s2Reg+1)+1) (liveValue (number c.bodyIncS2 : V) file),
      hfirst,hm,run_one,step_body_continue c,hf]
  · have hg : regValue g s1Reg≠0 := by
      dsimp only [g]
      rw [read_put_other _ _ s2Reg s1Reg (by decide)]
      exact hs
    rw [bodyClock,if_neg hs,show (4 : V)=(((0+1)+1)+1)+1 by ring,
      controlRun_succ,controlRun_succ,controlRun_succ,controlRun_succ,controlRun_zero,
      step_body_inc c,step_body_test_positive c g hg,step_body_break c,step_body_continue c]
    simp only [bodyFile,if_neg hs,g,read_put_other _ _ s2Reg s1Reg (by decide)]

private theorem first_zero : first (0 : V)=0 :=
  le_antisymm (projections_spec (0 : V)).1 (Arithmetic.zero_le _)
private theorem second_zero : second (0 : V)=0 :=
  le_antisymm (projections_spec (0 : V)).2.1 (Arithmetic.zero_le _)

/-- Pointwise state after t outer iterations, with original main input/file fixed. -/
def walkFile (file t : V) : V :=
  put s1Reg (first t) (put s2Reg (second t) (put c.mainIndex (regValue file c.mainIndex-t) file))
private theorem walkFile_main (file t : V) : regValue (walkFile c file t) c.mainIndex=regValue file c.mainIndex-t := by
  rw [walkFile,read_put_other _ _ s1Reg c.mainIndex c.main_ne_s1.symm,
    read_put_other _ _ s2Reg c.mainIndex c.main_ne_s2.symm,read_put_self]
private theorem walkFile_s1 (file t : V) : regValue (walkFile c file t) s1Reg=first t := by
  rw [walkFile,read_put_self]
private theorem walkFile_s2 (file t : V) : regValue (walkFile c file t) s2Reg=second t := by
  rw [walkFile,read_put_other _ _ s1Reg s2Reg (by decide),read_put_self]
private theorem walkFile_target (file t : V) : regValue (walkFile c file t) c.targetIndex=regValue file c.targetIndex := by
  rw [walkFile,read_put_other _ _ s1Reg c.targetIndex c.target_ne_s1.symm,
    read_put_other _ _ s2Reg c.targetIndex c.target_ne_s2.symm,read_put_other _ _ c.mainIndex c.targetIndex c.target_ne_main.symm]
private theorem walkFile_zero (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    walkFile c file 0=file := by
  have hp1 : put s1Reg 0 file=file := by rw [←h1]; exact put_same _ _
  have hp2 : put s2Reg 0 file=file := by rw [←h2]; exact put_same _ _
  simp only [walkFile,first_zero,second_zero,tsub_zero,put_same,hp1,hp2]
private theorem walkFile_step (file t : V) :
    bodyFile (put c.mainIndex (regValue (walkFile c file t) c.mainIndex-1) (walkFile c file t))=
      walkFile c file (t+1) := by
  rw [bodyFile]
  simp only [read_put_other _ _ c.mainIndex s1Reg c.main_ne_s1,
    read_put_other _ _ c.mainIndex s2Reg c.main_ne_s2,walkFile_s1,walkFile_s2]
  rw [←ArithmeticControlRead254.CantorWalk.first_succ,←ArithmeticControlRead254.CantorWalk.second_succ,walkFile_main]
  simp only [walkFile,put_commute c.mainIndex s1Reg c.main_ne_s1,
    put_commute c.mainIndex s2Reg c.main_ne_s2,put_commute s2Reg s1Reg (by decide),
    put_twice,←tsub_add_eq_tsub_tsub]

/-- The unbounded logical clock is an existential inside a Σ1 predicate with
fixed original file and input. No forall-files/exists-time induction is used. -/
theorem walk_reach (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (t : V) (ht : t≤regValue file c.mainIndex) :
    ∃ time : V, controlRun time (liveValue (number c.readEntry : V) file)=
      liveValue (number c.readEntry : V) (walkFile c file t) := by
  have reach (t : V) : t≤regValue file c.mainIndex →
      ∃ time : V, controlRun time (liveValue (number c.readEntry : V) file)=
        liveValue (number c.readEntry : V) (walkFile c file t) := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold walkFile put
      definability
    case zero =>
      intro _
      refine ⟨0,?_⟩
      rw [controlRun_zero,walkFile_zero c file h1 h2]
    case succ t ih =>
      intro hbound
      obtain ⟨time,hreach⟩ := ih
        (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) hbound)
      have hn : regValue (walkFile c file t) c.mainIndex≠0 := by
        rw [walkFile_main]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) hbound))
      let g := put c.mainIndex (regValue (walkFile c file t) c.mainIndex-1) (walkFile c file t)
      refine ⟨(time+1)+bodyClock g,?_⟩
      rw [controlRun_add (time+1) (bodyClock g) (liveValue (number c.readEntry : V) file),
        controlRun_succ time _,hreach,step_read_positive c _ hn,body_run c,walkFile_step]
  exact reach t ht

/-- The finite read shape consumes the main field into its Cantor components, adding the
first to its target and restoring the second to the main field. The whole nine-register file is
preserved except for those two fields; both scratch fields return to zero. -/
theorem read_shape (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number c.readEntry : V) file)=
        liveValue (number c.nextRead : V)
          (put c.targetIndex (regValue file c.targetIndex+first (regValue file c.mainIndex))
            (put c.mainIndex (second (regValue file c.mainIndex)) file)) := by
  let n := regValue file c.mainIndex
  obtain ⟨time,hreach⟩ := walk_reach c file h1 h2 n le_rfl
  let g := walkFile c file n
  have hg0 : regValue g c.mainIndex=0 := by
    dsimp only [g]
    rw [walkFile_main,tsub_self]
  have hfirst : controlRun 1 (liveValue (number c.readEntry : V) g)=
      liveValue (number c.restoreMainTest : V) g := by rw [run_one,step_read_zero c g hg0]
  have hp := move_s2_main c g
  rw [show regValue g s2Reg=second n by exact walkFile_s2 c _ _,hg0,zero_add] at hp
  let restored := put c.mainIndex (second n) (put s2Reg 0 g)
  have hr1 : regValue restored s1Reg=first n := by
    dsimp only [restored,g]
    rw [read_put_other _ _ c.mainIndex s1Reg c.main_ne_s1,
      read_put_other _ _ s2Reg s1Reg (by decide),walkFile_s1]
  have hra : regValue restored c.targetIndex=regValue file c.targetIndex := by
    dsimp only [restored,g]
    rw [read_put_other _ _ c.mainIndex c.targetIndex c.target_ne_main.symm,
      read_put_other _ _ s2Reg c.targetIndex c.target_ne_s2.symm,walkFile_target c]
  have ha := move_s1_target c restored
  rw [hr1,hra] at ha
  have hput1 : put s1Reg 0 file=file := by rw [←h1]; exact put_same _ _
  have hput2 : put s2Reg 0 file=file := by rw [←h2]; exact put_same _ _
  have hf : put c.targetIndex (regValue file c.targetIndex+first n) (put s1Reg 0 restored)=
      put c.targetIndex (regValue file c.targetIndex+first n) (put c.mainIndex (second n) file) := by
    simp only [restored,g,walkFile,show regValue file c.mainIndex=n from rfl,tsub_self,
      put_commute s1Reg c.mainIndex c.main_ne_s1.symm,put_commute s2Reg c.mainIndex c.main_ne_s2.symm,
      put_commute s2Reg s1Reg (by decide),put_twice,hput1,hput2]
  refine ⟨((time+1)+(3*second n+1))+(3*first n+1),?_,?_⟩
  · rw [show ((time+1)+(3*second n+1))+(3*first n+1)=
        (((time+1)+(3*second n+1))+3*first n)+1 by ring]
    exact le_add_of_nonneg_left (Arithmetic.zero_le _)
  · rw [controlRun_add ((time+1)+(3*second n+1)) (3*first n+1)
        (liveValue (number c.readEntry : V) file),
      controlRun_add (time+1) (3*second n+1) (liveValue (number c.readEntry : V) file),
      controlRun_succ time _,hreach]
    rw [←run_one (liveValue (number c.readEntry : V) g),hfirst,hp,ha,hf]

end Model


open ArithmeticControlNip254 ArithmeticControlDispatch254
open ArithmeticControlRead254 (acReg)

private theorem literal_source (P Q : List Bool) (e : Edge)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0=some (e,Q.length))
    (hc : consume P Q.length=Q) : source (resolveControl P)=(Q,e) := by
  rw [resolve_source P e Q.length hw,hc]

/-- WS is logical2, stored in physical0. -/
def wsReg : Fin 9 := 0

def wsBodyIncS2 : Control := resolveControl (incPath (source stackPopEntry).1)
def wsBodyTestS1 : Control := resolveControl (incPath (source wsBodyIncS2).1)
def wsBodyBreak : Control := resolveControl (incPath (source wsBodyTestS1).1)
def wsBodyMoveTest : Control := resolveControl (breakPath 1 (source wsBodyTestS1).1)
def wsBodyMoveInc : Control := resolveControl (incPath (source wsBodyMoveTest).1)
def wsBodyMoveContinue : Control := resolveControl (incPath (source wsBodyMoveInc).1)
def wsBodyContinue : Control := resolveControl (breakPath 1 (source wsBodyBreak).1)
def wsRestoreMainTest : Control := resolveControl (breakPath 1 (source stackPopEntry).1)
def wsRestoreMainInc : Control := resolveControl (incPath (source wsRestoreMainTest).1)
def wsRestoreMainContinue : Control := resolveControl (incPath (source wsRestoreMainInc).1)
def wsOutputTest : Control := resolveControl (breakPath 1 (source wsRestoreMainTest).1)
def wsOutputInc : Control := resolveControl (incPath (source wsOutputTest).1)
def wsOutputContinue : Control := resolveControl (incPath (source wsOutputInc).1)
def wsExit : Control := resolveControl (breakPath 1 (source wsOutputTest).1)
def nipJoin : Control := resolveControl (breakPath 1 (source wsExit).1)

theorem wsBodyIncS2_source : source wsBodyIncS2=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,false],.inc 7) := by
  rw [wsBodyIncS2,stackPopEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsBodyTestS1_source : source wsBodyTestS1=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,true,false,false,false],.decnz 6) := by
  rw [wsBodyTestS1,wsBodyIncS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsBodyBreak_source : source wsBodyBreak=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,true,false,false,true],.brk 1) := by
  rw [wsBodyBreak,wsBodyTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsBodyMoveTest_source : source wsBodyMoveTest=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,true,false,true,false],.decnz 7) := by
  rw [wsBodyMoveTest,wsBodyTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsBodyMoveInc_source : source wsBodyMoveInc=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,true,false,true,true,false],.inc 6) := by
  rw [wsBodyMoveInc,wsBodyMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsBodyMoveContinue_source : source wsBodyMoveContinue=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,true,false,true,true,true],.cont 2) := by
  rw [wsBodyMoveContinue,wsBodyMoveInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsBodyContinue_source : source wsBodyContinue=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,true,true,true],.cont 3) := by
  rw [wsBodyContinue,wsBodyBreak_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsRestoreMainTest_source : source wsRestoreMainTest=([true,true,true,false,true,false,false,true,false,true,true,true,false,true,false],.decnz 7) := by
  rw [wsRestoreMainTest,stackPopEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsRestoreMainInc_source : source wsRestoreMainInc=([true,true,true,false,true,false,false,true,false,true,true,true,false,true,true,false],.inc 2) := by
  rw [wsRestoreMainInc,wsRestoreMainTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsRestoreMainContinue_source : source wsRestoreMainContinue=([true,true,true,false,true,false,false,true,false,true,true,true,false,true,true,true],.cont 2) := by
  rw [wsRestoreMainContinue,wsRestoreMainInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsOutputTest_source : source wsOutputTest=([true,true,true,false,true,false,false,true,false,true,true,true,true,false],.decnz 6) := by
  rw [wsOutputTest,wsRestoreMainTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsOutputInc_source : source wsOutputInc=([true,true,true,false,true,false,false,true,false,true,true,true,true,true,false],.inc 5) := by
  rw [wsOutputInc,wsOutputTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsOutputContinue_source : source wsOutputContinue=([true,true,true,false,true,false,false,true,false,true,true,true,true,true,true],.cont 2) := by
  rw [wsOutputContinue,wsOutputInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem wsExit_source : source wsExit=([true,true,true,false,true,false,false,true,true],.brk 1) := by
  rw [wsExit,wsOutputTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem nipJoin_source : source nipJoin=([true,true,true,false,true,true],.brk 1) := by
  rw [nipJoin,wsExit_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_nip_join : resolveControl (breakPath 1 (source nipJoin).1)=fetchTest := by
  apply source_injective
  rw [nipJoin_source,fetchTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

/-- The actual WS→cache unpair, with every edge/continuation bound to the
literal current program. -/
def wsRead : UnpairShape where
  readEntry := stackPopEntry
  bodyIncS2 := wsBodyIncS2
  bodyTestS1 := wsBodyTestS1
  bodyBreak := wsBodyBreak
  bodyMoveTest := wsBodyMoveTest
  bodyMoveInc := wsBodyMoveInc
  bodyMoveContinue := wsBodyMoveContinue
  bodyContinue := wsBodyContinue
  restoreMainTest := wsRestoreMainTest
  restoreMainInc := wsRestoreMainInc
  restoreMainContinue := wsRestoreMainContinue
  outputTest := wsOutputTest
  outputInc := wsOutputInc
  outputContinue := wsOutputContinue
  nextRead := wsExit
  mainLogical := 2
  mainIndex := wsReg
  main_physical := rfl
  main_ne_s1 := by decide
  main_ne_s2 := by decide
  targetLogical := 5
  targetIndex := cacheReg
  target_physical := rfl
  target_ne_s1 := by decide
  target_ne_s2 := by decide
  target_ne_main := by decide
  read_edge := congrArg Prod.snd stackPopEntry_source
  body_inc_edge := congrArg Prod.snd wsBodyIncS2_source
  body_test_edge := congrArg Prod.snd wsBodyTestS1_source
  body_break_edge := congrArg Prod.snd wsBodyBreak_source
  body_move_test_edge := congrArg Prod.snd wsBodyMoveTest_source
  body_move_inc_edge := congrArg Prod.snd wsBodyMoveInc_source
  body_move_continue_edge := congrArg Prod.snd wsBodyMoveContinue_source
  body_continue_edge := congrArg Prod.snd wsBodyContinue_source
  restore_test_edge := congrArg Prod.snd wsRestoreMainTest_source
  restore_inc_edge := congrArg Prod.snd wsRestoreMainInc_source
  restore_continue_edge := congrArg Prod.snd wsRestoreMainContinue_source
  output_test_edge := congrArg Prod.snd wsOutputTest_source
  output_inc_edge := congrArg Prod.snd wsOutputInc_source
  output_continue_edge := congrArg Prod.snd wsOutputContinue_source
  next_read_positive := by
    apply source_injective
    rw [stackPopEntry_source,wsBodyIncS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_read_zero := by
    apply source_injective
    rw [stackPopEntry_source,wsRestoreMainTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_inc := by
    apply source_injective
    rw [wsBodyIncS2_source,wsBodyTestS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_test_positive := by
    apply source_injective
    rw [wsBodyTestS1_source,wsBodyBreak_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_test_zero := by
    apply source_injective
    rw [wsBodyTestS1_source,wsBodyMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_break := by
    apply source_injective
    rw [wsBodyBreak_source,wsBodyContinue_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_move_positive := by
    apply source_injective
    rw [wsBodyMoveTest_source,wsBodyMoveInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_move_inc := by
    apply source_injective
    rw [wsBodyMoveInc_source,wsBodyMoveContinue_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_move_continue := by
    apply source_injective
    rw [wsBodyMoveContinue_source,wsBodyMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_move_zero := by
    apply source_injective
    rw [wsBodyMoveTest_source,wsBodyContinue_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_continue := by
    apply source_injective
    rw [wsBodyContinue_source,stackPopEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_restore_main_positive := by
    apply source_injective
    rw [wsRestoreMainTest_source,wsRestoreMainInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_restore_main_inc := by
    apply source_injective
    rw [wsRestoreMainInc_source,wsRestoreMainContinue_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_restore_main_continue := by
    apply source_injective
    rw [wsRestoreMainContinue_source,wsRestoreMainTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_restore_main_zero := by
    apply source_injective
    rw [wsRestoreMainTest_source,wsOutputTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_output_positive := by
    apply source_injective
    rw [wsOutputTest_source,wsOutputInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_output_inc := by
    apply source_injective
    rw [wsOutputInc_source,wsOutputContinue_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_output_continue := by
    apply source_injective
    rw [wsOutputContinue_source,wsOutputTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_output_zero := by
    apply source_injective
    rw [wsOutputTest_source,wsExit_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

section ActualModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual WS unpair permits an arbitrary initial cache, adding the first
projection to it. Only WS and cache change; both scratch fields return to0. -/
theorem ws_unpair (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number stackPopEntry : V) file)=
        liveValue (number wsExit : V)
          (put cacheReg (regValue file cacheReg+first (regValue file wsReg))
            (put wsReg (second (regValue file wsReg)) file)) := by
  simpa only [wsRead] using read_shape wsRead file h1 h2

/-- Literal NIP stack-pop result, without modifying any other file field. -/
def popFile (file : V) : V :=
  put cacheReg (first (regValue file wsReg))
    (put wsReg (second (regValue file wsReg)) file)

theorem ws_pop (file : V) (h1 : regValue file s1Reg=0)
    (h2 : regValue file s2Reg=0) (hh : regValue file cacheReg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number stackPopEntry : V) file)=
        liveValue (number wsExit : V) (popFile file) := by
  simpa only [hh,zero_add,popFile] using ws_unpair file h1 h2

/-- Both remaining literal breaks return to the actual fetch test. -/
theorem nip_return (file : V) :
    controlRun 2 (liveValue (number wsExit : V) file)=
      liveValue (number fetchTest : V) file := by
  rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,
    step_break wsExit 1 (congrArg Prod.snd wsExit_source),
    show resolveControl (breakPath 1 (source wsExit).1)=nipJoin from rfl,
    step_break nipJoin 1 (congrArg Prod.snd nipJoin_source),next_nip_join]

/-- The full actual nonfalsity NIP branch: comparison, cache clear, WS unpair,
and both literal breaks. The complete original file remains visible. -/
theorem nip_nonfalsity_run (file : V) (h1 : regValue file s1Reg=0)
    (h2 : regValue file s2Reg=0) (hh : regValue file cacheReg≠1) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number nipEntry : V) file)=
        liveValue (number fetchTest : V) (popFile file) := by
  let g := put cacheReg 0 file
  have hg1 : regValue g s1Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ cacheReg s1Reg (by decide)]
    exact h1
  have hg2 : regValue g s2Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ cacheReg s2Reg (by decide)]
    exact h2
  have hgh : regValue g cacheReg=0 := read_put_self _ _ _
  obtain ⟨t1,ht1,hcompare⟩ := ArithmeticControlNip254.nip_nonfalsity file h1 hh
  obtain ⟨t2,ht2,hpop⟩ := ws_pop g hg1 hg2 hgh
  have hf : popFile g=popFile file := by
    simp only [popFile,g,read_put_other _ _ cacheReg wsReg (by decide),
      put_commute wsReg cacheReg (by decide),put_twice]
  refine ⟨t1+(t2+2),le_trans ht1 (le_add_of_nonneg_right (Arithmetic.zero_le _)),?_⟩
  rw [controlRun_add t1 (t2+2) (liveValue (number nipEntry : V) file),hcompare,
    controlRun_add t2 2 (liveValue (number stackPopEntry : V) g),hpop,nip_return,hf]

/-- Complete literal NIP behavior for every internal cache: cached falsity
halts, and every other value pops WS into the cache and returns to fetch. -/
theorem nip_run (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number nipEntry : V) file)=
        if regValue file cacheReg=1 then 0 else
          liveValue (number fetchTest : V) (popFile file) := by
  by_cases hh : regValue file cacheReg=1
  · refine ⟨7,?_,?_⟩
    · rw [show (7 : V)=6+1 by ring]
      exact le_add_of_nonneg_left (Arithmetic.zero_le _)
    · rw [if_pos hh]
      exact nip_falsity file h1 hh
  · simpa only [if_neg hh] using nip_nonfalsity_run file h1 h2 hh

/-- The actual dispatcher followed by complete NIP. Classification clears AC;
all other changes are precisely the WS/cache pop, or an actual halt. -/
theorem dispatch_nip_run (file : V) (ha : regValue file acReg=2)
    (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number dispatchEntry : V) file)=
        if regValue file cacheReg=1 then 0 else
          liveValue (number fetchTest : V) (popFile (put acReg 0 file)) := by
  let g := put acReg 0 file
  have hg1 : regValue g s1Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ acReg s1Reg (by decide)]
    exact h1
  have hg2 : regValue g s2Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ acReg s2Reg (by decide)]
    exact h2
  have hgh : regValue g cacheReg=regValue file cacheReg := by
    dsimp only [g]
    exact read_put_other _ _ acReg cacheReg (by decide)
  obtain ⟨time,ht,hr⟩ := nip_run g hg1 hg2
  rw [hgh] at hr
  refine ⟨3+time,le_trans ht (le_add_of_nonneg_left (Arithmetic.zero_le (3 : V))),?_⟩
  rw [controlRun_add,dispatch_nip file ha,hr]

end ActualModel

end SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpair254

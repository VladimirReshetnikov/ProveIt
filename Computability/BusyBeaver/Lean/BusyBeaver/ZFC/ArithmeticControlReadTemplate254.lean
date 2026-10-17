import BusyBeaver.ZFC.ArithmeticControlRead254

set_option autoImplicit false
noncomputable section

/-!
A finite read shape in the actual numbered interpreter, with its all-internal
runtime proved from literal edge and continuation equalities. The actual
second read binds controls24–37 to dispatch entry38. This module does not
establish the complete internal L2/Enum equivalence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 FiniteControlTable254 RegisterPath
open ArithmeticControlRead254 (s2Reg)

/-- External finite controls from the actual catalogue, never an execution
oracle. Every step in the template is specified by an actual source equality
and its actual resolved continuation. -/
structure ReadShape where
  readEntry : Control
  bodyIncS2 : Control
  bodyTestS1 : Control
  bodyBreak : Control
  bodyMoveTest : Control
  bodyMoveInc : Control
  bodyMoveContinue : Control
  bodyContinue : Control
  restorePLTest : Control
  restorePLInc : Control
  restorePLContinue : Control
  outputTest : Control
  outputInc : Control
  outputContinue : Control
  nextRead : Control
  targetLogical : Nat
  targetIndex : Fin 9
  target_physical : Permutation252Frame.physOf targetLogical=targetIndex.val
  target_ne_s1 : targetIndex≠s1Reg
  target_ne_s2 : targetIndex≠s2Reg
  target_ne_pl : targetIndex≠plReg
  read_edge : (source readEntry).2=.decnz 8
  body_inc_edge : (source bodyIncS2).2=.inc 7
  body_test_edge : (source bodyTestS1).2=.decnz 6
  body_break_edge : (source bodyBreak).2=.brk 1
  body_move_test_edge : (source bodyMoveTest).2=.decnz 7
  body_move_inc_edge : (source bodyMoveInc).2=.inc 6
  body_move_continue_edge : (source bodyMoveContinue).2=.cont 2
  body_continue_edge : (source bodyContinue).2=.cont 3
  restore_test_edge : (source restorePLTest).2=.decnz 7
  restore_inc_edge : (source restorePLInc).2=.inc 8
  restore_continue_edge : (source restorePLContinue).2=.cont 2
  output_test_edge : (source outputTest).2=.decnz 6
  output_inc_edge : (source outputInc).2=.inc targetLogical
  output_continue_edge : (source outputContinue).2=.cont 2
  next_read_positive : resolveControl (incPath (source readEntry).1)=bodyIncS2
  next_read_zero : resolveControl (breakPath 1 (source readEntry).1)=restorePLTest
  next_body_inc : resolveControl (incPath (source bodyIncS2).1)=bodyTestS1
  next_body_test_positive : resolveControl (incPath (source bodyTestS1).1)=bodyBreak
  next_body_test_zero : resolveControl (breakPath 1 (source bodyTestS1).1)=bodyMoveTest
  next_body_break : resolveControl (breakPath 1 (source bodyBreak).1)=bodyContinue
  next_body_move_positive : resolveControl (incPath (source bodyMoveTest).1)=bodyMoveInc
  next_body_move_inc : resolveControl (incPath (source bodyMoveInc).1)=bodyMoveContinue
  next_body_move_continue : resolveControl (continuePath 2 (source bodyMoveContinue).1)=bodyMoveTest
  next_body_move_zero : resolveControl (breakPath 1 (source bodyMoveTest).1)=bodyContinue
  next_body_continue : resolveControl (continuePath 3 (source bodyContinue).1)=readEntry
  next_restore_pl_positive : resolveControl (incPath (source restorePLTest).1)=restorePLInc
  next_restore_pl_inc : resolveControl (incPath (source restorePLInc).1)=restorePLContinue
  next_restore_pl_continue : resolveControl (continuePath 2 (source restorePLContinue).1)=restorePLTest
  next_restore_pl_zero : resolveControl (breakPath 1 (source restorePLTest).1)=outputTest
  next_output_positive : resolveControl (incPath (source outputTest).1)=outputInc
  next_output_inc : resolveControl (incPath (source outputInc).1)=outputContinue
  next_output_continue : resolveControl (continuePath 2 (source outputContinue).1)=outputTest
  next_output_zero : resolveControl (breakPath 1 (source outputTest).1)=nextRead

/-- Parameter1/D occupies physical field3. -/
def p1Reg : Fin 9 := 3

/-- The actual second read, including every resolved continuation. -/
def p1Read : ReadShape where
  readEntry := ⟨24,by decide⟩
  bodyIncS2 := ⟨25,by decide⟩
  bodyTestS1 := ⟨26,by decide⟩
  bodyBreak := ⟨27,by decide⟩
  bodyMoveTest := ⟨28,by decide⟩
  bodyMoveInc := ⟨29,by decide⟩
  bodyMoveContinue := ⟨30,by decide⟩
  bodyContinue := ⟨31,by decide⟩
  restorePLTest := ⟨32,by decide⟩
  restorePLInc := ⟨33,by decide⟩
  restorePLContinue := ⟨34,by decide⟩
  outputTest := ⟨35,by decide⟩
  outputInc := ⟨36,by decide⟩
  outputContinue := ⟨37,by decide⟩
  nextRead := ⟨38,by decide⟩
  targetLogical := 4
  targetIndex := p1Reg
  target_physical := rfl
  target_ne_s1 := by decide
  target_ne_s2 := by decide
  target_ne_pl := by decide
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
  output_test_edge := by rfl
  output_inc_edge := by rfl
  output_continue_edge := by rfl
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
  next_restore_pl_positive := by rfl
  next_restore_pl_inc := by rfl
  next_restore_pl_continue := by rfl
  next_restore_pl_zero := by rfl
  next_output_positive := by rfl
  next_output_inc := by rfl
  next_output_continue := by rfl
  next_output_zero := by rfl

theorem p1Read_entry : p1Read.readEntry=ArithmeticControlRead254.nextRead := by rfl
theorem p1Read_exit_source : source p1Read.nextRead=([true,true,true,false,false],.decnz 3) := by rfl
theorem p1Read_target : p1Read.targetIndex=p1Reg := by rfl

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

private def bodyTransfer (c : ReadShape) : TransferShape where
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

private def restorePLTransfer (c : ReadShape) : TransferShape where
  test := c.restorePLTest
  increment := c.restorePLInc
  again := c.restorePLContinue
  exit := c.outputTest
  sourceLogical := 7
  targetLogical := 8
  sourceIndex := s2Reg
  targetIndex := plReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := c.restore_test_edge
  increment_edge := c.restore_inc_edge
  again_edge := c.restore_continue_edge
  positive_target := c.next_restore_pl_positive
  increment_target := c.next_restore_pl_inc
  repeat_target := c.next_restore_pl_continue
  zero_target := c.next_restore_pl_zero

private def outputTransfer (c : ReadShape) : TransferShape where
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
variable (c : ReadShape)
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
/-- Actual restoration of the second Cantor component into PL. -/
theorem move_s2_pl (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.restorePLTest : V) file)=
      liveValue (number c.outputTest : V)
        (put plReg (regValue file plReg+regValue file s2Reg) (put s2Reg 0 file)) := by
  simpa only [transferFile,restorePLTransfer,tsub_self] using transfer_run (restorePLTransfer c) file
/-- Actual transfer of the first Cantor component into the shape target. -/
theorem move_s1_target (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number c.outputTest : V) file)=
      liveValue (number c.nextRead : V)
        (put c.targetIndex (regValue file c.targetIndex+regValue file s1Reg) (put s1Reg 0 file)) := by
  simpa only [transferFile,outputTransfer,tsub_self] using transfer_run (outputTransfer c) file

private theorem read_pl (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 8) 0=regValue file plReg :=
  physicalValues_getD file plReg
private theorem read_s1 (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 6) 0=regValue file s1Reg :=
  physicalValues_getD file s1Reg
private theorem read_s2 (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 7) 0=regValue file s2Reg :=
  physicalValues_getD file s2Reg
private theorem run_one (state : V) : controlRun 1 state=ArithmeticControlStep254.stepValue state := by
  rw [show (1 : V)=0+1 by ring,controlRun_succ,controlRun_zero]
private theorem step_read_positive (file : V) (h : regValue file plReg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.readEntry : V) file)=
      liveValue (number c.bodyIncS2 : V) (put plReg (regValue file plReg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 8) 0≠0 := by rwa [read_pl]
  rw [step_decnz_positive c.readEntry 8 (c.read_edge) file hn,
    c.next_read_positive,read_pl]
  rfl
private theorem step_read_zero (file : V) (h : regValue file plReg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.readEntry : V) file)=
      liveValue (number c.restorePLTest : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 8) 0=0 := by rwa [read_pl]
  rw [step_decnz_zero c.readEntry 8 (c.read_edge) file hz,c.next_read_zero]
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

/-- This local body starts after the outer PL decrement and returns to that
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

/-- Pointwise state after t outer iterations, with original input/file fixed. -/
def walkFile (file t : V) : V :=
  put s1Reg (first t) (put s2Reg (second t) (put plReg (regValue file plReg-t) file))
private theorem walkFile_pl (file t : V) : regValue (walkFile file t) plReg=regValue file plReg-t := by
  rw [walkFile,read_put_other _ _ s1Reg plReg (by decide),
    read_put_other _ _ s2Reg plReg (by decide),read_put_self]
private theorem walkFile_s1 (file t : V) : regValue (walkFile file t) s1Reg=first t := by
  rw [walkFile,read_put_self]
private theorem walkFile_s2 (file t : V) : regValue (walkFile file t) s2Reg=second t := by
  rw [walkFile,read_put_other _ _ s1Reg s2Reg (by decide),read_put_self]
private theorem walkFile_target (file t : V) : regValue (walkFile file t) c.targetIndex=regValue file c.targetIndex := by
  rw [walkFile,read_put_other _ _ s1Reg c.targetIndex c.target_ne_s1.symm,
    read_put_other _ _ s2Reg c.targetIndex c.target_ne_s2.symm,read_put_other _ _ plReg c.targetIndex c.target_ne_pl.symm]
private theorem walkFile_zero (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    walkFile file 0=file := by
  have hp1 : put s1Reg 0 file=file := by rw [←h1]; exact put_same _ _
  have hp2 : put s2Reg 0 file=file := by rw [←h2]; exact put_same _ _
  simp only [walkFile,first_zero,second_zero,tsub_zero,put_same,hp1,hp2]
private theorem walkFile_step (file t : V) :
    bodyFile (put plReg (regValue (walkFile file t) plReg-1) (walkFile file t))=
      walkFile file (t+1) := by
  rw [bodyFile]
  simp only [read_put_other _ _ plReg s1Reg (by decide),
    read_put_other _ _ plReg s2Reg (by decide),walkFile_s1,walkFile_s2]
  rw [←ArithmeticControlRead254.CantorWalk.first_succ,←ArithmeticControlRead254.CantorWalk.second_succ,walkFile_pl]
  simp only [walkFile,put_commute plReg s1Reg (by decide),
    put_commute plReg s2Reg (by decide),put_commute s2Reg s1Reg (by decide),
    put_twice,←tsub_add_eq_tsub_tsub]

/-- The unbounded logical clock is an existential inside a Σ1 predicate with
fixed original file and input. No forall-files/exists-time induction is used. -/
theorem walk_reach (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (t : V) (ht : t≤regValue file plReg) :
    ∃ time : V, controlRun time (liveValue (number c.readEntry : V) file)=
      liveValue (number c.readEntry : V) (walkFile file t) := by
  have reach (t : V) : t≤regValue file plReg →
      ∃ time : V, controlRun time (liveValue (number c.readEntry : V) file)=
        liveValue (number c.readEntry : V) (walkFile file t) := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold walkFile put
      definability
    case zero =>
      intro _
      refine ⟨0,?_⟩
      rw [controlRun_zero,walkFile_zero file h1 h2]
    case succ t ih =>
      intro hbound
      obtain ⟨time,hreach⟩ := ih
        (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) hbound)
      have hn : regValue (walkFile file t) plReg≠0 := by
        rw [walkFile_pl]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) hbound))
      let g := put plReg (regValue (walkFile file t) plReg-1) (walkFile file t)
      refine ⟨(time+1)+bodyClock g,?_⟩
      rw [controlRun_add (time+1) (bodyClock g) (liveValue (number c.readEntry : V) file),
        controlRun_succ time _,hreach,step_read_positive c _ hn,body_run c,walkFile_step]
  exact reach t ht

/-- The finite read shape consumes PL into its Cantor components, adding the
first to its target and restoring the second to PL. The whole nine-register file is
preserved except for those two fields; both scratch fields return to zero. -/
theorem read_shape (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number c.readEntry : V) file)=
        liveValue (number c.nextRead : V)
          (put c.targetIndex (regValue file c.targetIndex+first (regValue file plReg))
            (put plReg (second (regValue file plReg)) file)) := by
  let n := regValue file plReg
  obtain ⟨time,hreach⟩ := walk_reach c file h1 h2 n le_rfl
  let g := walkFile file n
  have hg0 : regValue g plReg=0 := by
    dsimp only [g]
    rw [walkFile_pl,tsub_self]
  have hfirst : controlRun 1 (liveValue (number c.readEntry : V) g)=
      liveValue (number c.restorePLTest : V) g := by rw [run_one,step_read_zero c g hg0]
  have hp := move_s2_pl c g
  rw [show regValue g s2Reg=second n by exact walkFile_s2 _ _,hg0,zero_add] at hp
  let restored := put plReg (second n) (put s2Reg 0 g)
  have hr1 : regValue restored s1Reg=first n := by
    dsimp only [restored,g]
    rw [read_put_other _ _ plReg s1Reg (by decide),
      read_put_other _ _ s2Reg s1Reg (by decide),walkFile_s1]
  have hra : regValue restored c.targetIndex=regValue file c.targetIndex := by
    dsimp only [restored,g]
    rw [read_put_other _ _ plReg c.targetIndex c.target_ne_pl.symm,
      read_put_other _ _ s2Reg c.targetIndex c.target_ne_s2.symm,walkFile_target c]
  have ha := move_s1_target c restored
  rw [hr1,hra] at ha
  have hput1 : put s1Reg 0 file=file := by rw [←h1]; exact put_same _ _
  have hput2 : put s2Reg 0 file=file := by rw [←h2]; exact put_same _ _
  have hf : put c.targetIndex (regValue file c.targetIndex+first n) (put s1Reg 0 restored)=
      put c.targetIndex (regValue file c.targetIndex+first n) (put plReg (second n) file) := by
    simp only [restored,g,walkFile,show regValue file plReg=n from rfl,tsub_self,
      put_commute s1Reg plReg (by decide),put_commute s2Reg plReg (by decide),
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

/-- Actual second read: PL is consumed into its two Cantor projections, the
first is added to parameter1/D, and every other whole-file field is retained. -/
theorem read_p1 {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number ArithmeticControlRead254.nextRead : V) file)=
        liveValue (number p1Read.nextRead : V)
          (put p1Reg (regValue file p1Reg+first (regValue file plReg))
            (put plReg (second (regValue file plReg)) file)) := by
  simpa only [p1Read_entry,p1Read_target] using read_shape p1Read file h1 h2

/-- The two actual reads preceding dispatch, composed at their literal common
control. Scratch zero is preserved, and the complete original file remains
visible in the endpoint. -/
theorem reads_run {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number ArithmeticControlFetch254.readEntry : V) file)=
        liveValue (number p1Read.nextRead : V)
          (put p1Reg (regValue file p1Reg+first (second (regValue file plReg)))
            (put ArithmeticControlRead254.acReg
              (regValue file ArithmeticControlRead254.acReg+first (regValue file plReg))
              (put plReg (second (second (regValue file plReg))) file))) := by
  let g := put ArithmeticControlRead254.acReg
    (regValue file ArithmeticControlRead254.acReg+first (regValue file plReg))
    (put plReg (second (regValue file plReg)) file)
  obtain ⟨t1,ht1,hfirst⟩ := ArithmeticControlRead254.read_ac file h1 h2
  have hg1 : regValue g s1Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ ArithmeticControlRead254.acReg s1Reg (by decide),
      read_put_other _ _ plReg s1Reg (by decide)]
    exact h1
  have hg2 : regValue g s2Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ ArithmeticControlRead254.acReg s2Reg (by decide),
      read_put_other _ _ plReg s2Reg (by decide)]
    exact h2
  have hgp : regValue g plReg=second (regValue file plReg) := by
    dsimp only [g]
    rw [read_put_other _ _ ArithmeticControlRead254.acReg plReg (by decide),read_put_self]
  have hgd : regValue g p1Reg=regValue file p1Reg := by
    dsimp only [g]
    rw [read_put_other _ _ ArithmeticControlRead254.acReg p1Reg (by decide),
      read_put_other _ _ plReg p1Reg (by decide)]
  obtain ⟨t2,ht2,hsecond⟩ := read_p1 g hg1 hg2
  rw [hgp,hgd] at hsecond
  refine ⟨t1+t2,le_trans ht1 (le_add_of_nonneg_right (Arithmetic.zero_le t2)),?_⟩
  rw [controlRun_add,hfirst,hsecond]
  simp only [g,put_commute plReg ArithmeticControlRead254.acReg (by decide),put_twice]

end SetTheory.BusyBeaver.ZFC.ArithmeticControlReadTemplate254

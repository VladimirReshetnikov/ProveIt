import BusyBeaver.ZFC.ArithmeticControlFetch254

set_option autoImplicit false
noncomputable section

/-!
Actual first read/unpair macro. All counters and file values may be internal
to an IΣ1 model. This module does not establish complete internal L2/Enum
equivalence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 FiniteControlTable254 RegisterPath

def bodyIncS2 : Control := ⟨11,by decide⟩
def bodyTestS1 : Control := ⟨12,by decide⟩
def bodyBreak : Control := ⟨13,by decide⟩
def bodyMoveTest : Control := ⟨14,by decide⟩
def bodyMoveInc : Control := ⟨15,by decide⟩
def bodyMoveContinue : Control := ⟨16,by decide⟩
def bodyContinue : Control := ⟨17,by decide⟩
def restorePLTest : Control := ⟨18,by decide⟩
def restorePLInc : Control := ⟨19,by decide⟩
def restorePLContinue : Control := ⟨20,by decide⟩
def outputTest : Control := ⟨21,by decide⟩
def outputInc : Control := ⟨22,by decide⟩
def outputContinue : Control := ⟨23,by decide⟩
def nextRead : Control := ⟨24,by decide⟩

theorem bodyIncS2_source : source bodyIncS2=([true,false,false,false,true,false],.inc 7) := by rfl
theorem bodyTestS1_source : source bodyTestS1=([true,false,false,false,true,true,false,false,false],.decnz 6) := by rfl
theorem bodyBreak_source : source bodyBreak=([true,false,false,false,true,true,false,false,true],.brk 1) := by rfl
theorem bodyMoveTest_source : source bodyMoveTest=([true,false,false,false,true,true,false,true,false],.decnz 7) := by rfl
theorem bodyMoveInc_source : source bodyMoveInc=([true,false,false,false,true,true,false,true,true,false],.inc 6) := by rfl
theorem bodyMoveContinue_source : source bodyMoveContinue=([true,false,false,false,true,true,false,true,true,true],.cont 2) := by rfl
theorem bodyContinue_source : source bodyContinue=([true,false,false,false,true,true,true],.cont 3) := by rfl
theorem restorePLTest_source : source restorePLTest=([true,false,false,true,false],.decnz 7) := by rfl
theorem restorePLInc_source : source restorePLInc=([true,false,false,true,true,false],.inc 8) := by rfl
theorem restorePLContinue_source : source restorePLContinue=([true,false,false,true,true,true],.cont 2) := by rfl
theorem outputTest_source : source outputTest=([true,false,true,false],.decnz 6) := by rfl
theorem outputInc_source : source outputInc=([true,false,true,true,false],.inc 3) := by rfl
theorem outputContinue_source : source outputContinue=([true,false,true,true,true],.cont 2) := by rfl
theorem nextRead_source : source nextRead=([true,true,false,false,false,false],.decnz 8) := by rfl

theorem next_read_positive : resolveControl (incPath (source readEntry).1)=bodyIncS2 := by rfl
theorem next_read_zero : resolveControl (breakPath 1 (source readEntry).1)=restorePLTest := by rfl
theorem next_body_inc : resolveControl (incPath (source bodyIncS2).1)=bodyTestS1 := by rfl
theorem next_body_test_positive : resolveControl (incPath (source bodyTestS1).1)=bodyBreak := by rfl
theorem next_body_test_zero : resolveControl (breakPath 1 (source bodyTestS1).1)=bodyMoveTest := by rfl
theorem next_body_break : resolveControl (breakPath 1 (source bodyBreak).1)=bodyContinue := by rfl
theorem next_body_move_positive : resolveControl (incPath (source bodyMoveTest).1)=bodyMoveInc := by rfl
theorem next_body_move_inc : resolveControl (incPath (source bodyMoveInc).1)=bodyMoveContinue := by rfl
theorem next_body_move_continue : resolveControl (continuePath 2 (source bodyMoveContinue).1)=bodyMoveTest := by rfl
theorem next_body_move_zero : resolveControl (breakPath 1 (source bodyMoveTest).1)=bodyContinue := by rfl
theorem next_body_continue : resolveControl (continuePath 3 (source bodyContinue).1)=readEntry := by rfl
theorem next_restore_pl_positive : resolveControl (incPath (source restorePLTest).1)=restorePLInc := by rfl
theorem next_restore_pl_inc : resolveControl (incPath (source restorePLInc).1)=restorePLContinue := by rfl
theorem next_restore_pl_continue : resolveControl (continuePath 2 (source restorePLContinue).1)=restorePLTest := by rfl
theorem next_restore_pl_zero : resolveControl (breakPath 1 (source restorePLTest).1)=outputTest := by rfl
theorem next_output_positive : resolveControl (incPath (source outputTest).1)=outputInc := by rfl
theorem next_output_inc : resolveControl (incPath (source outputInc).1)=outputContinue := by rfl
theorem next_output_continue : resolveControl (continuePath 2 (source outputContinue).1)=outputTest := by rfl
theorem next_output_zero : resolveControl (breakPath 1 (source outputTest).1)=nextRead := by rfl

def s2Reg : Fin 9 := 5
def acReg : Fin 9 := 4


namespace CantorWalk
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
local instance : DecidableEq V := Classical.decEq V

/-- Wrap to the first point on the next anti-diagonal. -/
lemma cantor_zero_succ (b : V) : cantor 0 b + 1 = cantor (b+1) 0 := by
  simp only [cantor,zero_add,add_zero,triangle_succ]

private lemma pred_add_one (a : V) (ha : a ≠ 0) : a-1+1 = a := by
  have hpos : 0 < a := lt_of_le_of_ne (Arithmetic.zero_le a) (Ne.symm ha)
  exact tsub_add_cancel_of_le (by simpa using lt_iff_succ_le.mp hpos)

/-- Inside an anti-diagonal, move one unit from the first coordinate to the
second. The nonzero premise justifies the truncated predecessor. -/
lemma cantor_pred_succ (a b : V) (ha : a ≠ 0) :
    cantor (a-1) (b+1) = cantor a b + 1 := by
  have hs : (a-1)+(b+1) = a+b := by
    calc
      (a-1)+(b+1) = (a-1+1)+b := by ring
      _ = a+b := by rw [pred_add_one a ha]
  simp only [cantor,hs]
  ring

lemma cantor_succ (a b : V) :
    cantor a b + 1 =
      if a=0 then cantor (b+1) 0 else cantor (a-1) (b+1) := by
  by_cases ha : a=0
  · subst a
    rw [if_pos rfl]
    exact cantor_zero_succ b
  · rw [if_neg ha]
    exact (cantor_pred_succ a b ha).symm

lemma successor_reconstruct (n : V) :
    n+1 = if first n=0 then cantor (second n+1) 0
      else cantor (first n-1) (second n+1) := by
  calc
    n+1 = cantor (first n) (second n)+1 := by rw [cantor_projections]
    _ = _ := cantor_succ (first n) (second n)

lemma projections_succ_zero (n : V) (h : first n=0) :
    first (n+1)=second n+1 ∧ second (n+1)=0 := by
  have he := successor_reconstruct n
  rw [if_pos h] at he
  rw [he,first_cantor,second_cantor]
  exact ⟨rfl,rfl⟩

lemma projections_succ_nonzero (n : V) (h : first n≠0) :
    first (n+1)=first n-1 ∧ second (n+1)=second n+1 := by
  have he := successor_reconstruct n
  rw [if_neg h] at he
  rw [he,first_cantor,second_cantor]
  exact ⟨rfl,rfl⟩

/-- Exact inverse-successor walk, with no standard-code premise. -/
theorem projections_succ (n : V) :
    (first (n+1),second (n+1)) =
      if first n=0 then (second n+1,0) else (first n-1,second n+1) := by
  by_cases h : first n=0
  · rw [if_pos h]
    exact Prod.ext (projections_succ_zero n h).1 (projections_succ_zero n h).2
  · rw [if_neg h]
    exact Prod.ext (projections_succ_nonzero n h).1 (projections_succ_nonzero n h).2

/-- Scalar first-coordinate form for a register-loop invariant. -/
theorem first_succ (n : V) :
    first (n+1) = if first n=0 then second n+1 else first n-1 := by
  by_cases h : first n=0
  · rw [if_pos h]
    exact (projections_succ_zero n h).1
  · rw [if_neg h]
    exact (projections_succ_nonzero n h).1

/-- Scalar second-coordinate form, including the anti-diagonal reset to zero. -/
theorem second_succ (n : V) :
    second (n+1) = if first n=0 then 0 else second n+1 := by
  by_cases h : first n=0
  · rw [if_pos h]
    exact (projections_succ_zero n h).2
  · rw [if_neg h]
    exact (projections_succ_nonzero n h).2

end CantorWalk

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

private def bodyTransfer : TransferShape where
  test := bodyMoveTest
  increment := bodyMoveInc
  again := bodyMoveContinue
  exit := bodyContinue
  sourceLogical := 7
  targetLogical := 6
  sourceIndex := s2Reg
  targetIndex := s1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd bodyMoveTest_source
  increment_edge := congrArg Prod.snd bodyMoveInc_source
  again_edge := congrArg Prod.snd bodyMoveContinue_source
  positive_target := next_body_move_positive
  increment_target := next_body_move_inc
  repeat_target := next_body_move_continue
  zero_target := next_body_move_zero

private def restorePLTransfer : TransferShape where
  test := restorePLTest
  increment := restorePLInc
  again := restorePLContinue
  exit := outputTest
  sourceLogical := 7
  targetLogical := 8
  sourceIndex := s2Reg
  targetIndex := plReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd restorePLTest_source
  increment_edge := congrArg Prod.snd restorePLInc_source
  again_edge := congrArg Prod.snd restorePLContinue_source
  positive_target := next_restore_pl_positive
  increment_target := next_restore_pl_inc
  repeat_target := next_restore_pl_continue
  zero_target := next_restore_pl_zero

private def outputTransfer : TransferShape where
  test := outputTest
  increment := outputInc
  again := outputContinue
  exit := nextRead
  sourceLogical := 6
  targetLogical := 3
  sourceIndex := s1Reg
  targetIndex := acReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd outputTest_source
  increment_edge := congrArg Prod.snd outputInc_source
  again_edge := congrArg Prod.snd outputContinue_source
  positive_target := next_output_positive
  increment_target := next_output_inc
  repeat_target := next_output_continue
  zero_target := next_output_zero

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
    controlRun (3*regValue file s2Reg+1) (liveValue (number bodyMoveTest : V) file)=
      liveValue (number bodyContinue : V)
        (put s1Reg (regValue file s1Reg+regValue file s2Reg) (put s2Reg 0 file)) := by
  simpa only [transferFile,bodyTransfer,tsub_self] using transfer_run bodyTransfer file
/-- Actual restoration of the second Cantor component into PL. -/
theorem move_s2_pl (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number restorePLTest : V) file)=
      liveValue (number outputTest : V)
        (put plReg (regValue file plReg+regValue file s2Reg) (put s2Reg 0 file)) := by
  simpa only [transferFile,restorePLTransfer,tsub_self] using transfer_run restorePLTransfer file
/-- Actual transfer of the first Cantor component into the AC accumulator. -/
theorem move_s1_ac (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number outputTest : V) file)=
      liveValue (number nextRead : V)
        (put acReg (regValue file acReg+regValue file s1Reg) (put s1Reg 0 file)) := by
  simpa only [transferFile,outputTransfer,tsub_self] using transfer_run outputTransfer file

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
    ArithmeticControlStep254.stepValue (liveValue (number readEntry : V) file)=
      liveValue (number bodyIncS2 : V) (put plReg (regValue file plReg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 8) 0≠0 := by rwa [read_pl]
  rw [step_decnz_positive readEntry 8 (congrArg Prod.snd readEntry_source) file hn,
    next_read_positive,read_pl]
  rfl
private theorem step_read_zero (file : V) (h : regValue file plReg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number readEntry : V) file)=
      liveValue (number restorePLTest : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 8) 0=0 := by rwa [read_pl]
  rw [step_decnz_zero readEntry 8 (congrArg Prod.snd readEntry_source) file hz,next_read_zero]
private theorem step_body_inc (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number bodyIncS2 : V) file)=
      liveValue (number bodyTestS1 : V) (put s2Reg (regValue file s2Reg+1) file) := by
  rw [step_inc bodyIncS2 7 (congrArg Prod.snd bodyIncS2_source),next_body_inc,read_s2]
  rfl
private theorem step_body_test_positive (file : V) (h : regValue file s1Reg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number bodyTestS1 : V) file)=
      liveValue (number bodyBreak : V) (put s1Reg (regValue file s1Reg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 6) 0≠0 := by rwa [read_s1]
  rw [step_decnz_positive bodyTestS1 6 (congrArg Prod.snd bodyTestS1_source) file hn,
    next_body_test_positive,read_s1]
  rfl
private theorem step_body_test_zero (file : V) (h : regValue file s1Reg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number bodyTestS1 : V) file)=
      liveValue (number bodyMoveTest : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 6) 0=0 := by rwa [read_s1]
  rw [step_decnz_zero bodyTestS1 6 (congrArg Prod.snd bodyTestS1_source) file hz,next_body_test_zero]
private theorem step_body_break (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number bodyBreak : V) file)=
      liveValue (number bodyContinue : V) file := by
  rw [step_break bodyBreak 1 (congrArg Prod.snd bodyBreak_source),next_body_break]
private theorem step_body_continue (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number bodyContinue : V) file)=
      liveValue (number readEntry : V) file := by
  rw [step_continue bodyContinue 3 (congrArg Prod.snd bodyContinue_source),next_body_continue]

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
    controlRun (bodyClock file) (liveValue (number bodyIncS2 : V) file)=
      liveValue (number readEntry : V) (bodyFile file) := by
  let g := put s2Reg (regValue file s2Reg+1) file
  by_cases hs : regValue file s1Reg=0
  · have hg : regValue g s1Reg=0 := by
      dsimp only [g]
      rw [read_put_other _ _ s2Reg s1Reg (by decide)]
      exact hs
    have hfirst : controlRun 2 (liveValue (number bodyIncS2 : V) file)=
        liveValue (number bodyMoveTest : V) g := by
      rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,step_body_inc,step_body_test_zero g hg]
    have hm := move_s2_s1 g
    rw [show regValue g s2Reg=regValue file s2Reg+1 by exact read_put_self _ _ s2Reg,hg,zero_add] at hm
    have hf : put s1Reg (regValue file s2Reg+1) (put s2Reg 0 g)=bodyFile file := by
      simp only [bodyFile,hs,if_true,g,put_twice]
    rw [bodyClock,if_pos hs,
      show 3*(regValue file s2Reg+1)+4=(2+(3*(regValue file s2Reg+1)+1))+1 by ring,
      controlRun_add (2+(3*(regValue file s2Reg+1)+1)) 1 (liveValue (number bodyIncS2 : V) file),
      controlRun_add 2 (3*(regValue file s2Reg+1)+1) (liveValue (number bodyIncS2 : V) file),
      hfirst,hm,run_one,step_body_continue,hf]
  · have hg : regValue g s1Reg≠0 := by
      dsimp only [g]
      rw [read_put_other _ _ s2Reg s1Reg (by decide)]
      exact hs
    rw [bodyClock,if_neg hs,show (4 : V)=(((0+1)+1)+1)+1 by ring,
      controlRun_succ,controlRun_succ,controlRun_succ,controlRun_succ,controlRun_zero,
      step_body_inc,step_body_test_positive g hg,step_body_break,step_body_continue]
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
private theorem walkFile_ac (file t : V) : regValue (walkFile file t) acReg=regValue file acReg := by
  rw [walkFile,read_put_other _ _ s1Reg acReg (by decide),
    read_put_other _ _ s2Reg acReg (by decide),read_put_other _ _ plReg acReg (by decide)]
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
  rw [←CantorWalk.first_succ,←CantorWalk.second_succ,walkFile_pl]
  simp only [walkFile,put_commute plReg s1Reg (by decide),
    put_commute plReg s2Reg (by decide),put_commute s2Reg s1Reg (by decide),
    put_twice,←tsub_add_eq_tsub_tsub]

/-- The unbounded logical clock is an existential inside a Σ1 predicate with
fixed original file and input. No forall-files/exists-time induction is used. -/
theorem walk_reach (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0)
    (t : V) (ht : t≤regValue file plReg) :
    ∃ time : V, controlRun time (liveValue (number readEntry : V) file)=
      liveValue (number readEntry : V) (walkFile file t) := by
  have reach (t : V) : t≤regValue file plReg →
      ∃ time : V, controlRun time (liveValue (number readEntry : V) file)=
        liveValue (number readEntry : V) (walkFile file t) := by
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
      rw [controlRun_add (time+1) (bodyClock g) (liveValue (number readEntry : V) file),
        controlRun_succ time _,hreach,step_read_positive _ hn,body_run,walkFile_step]
  exact reach t ht

/-- The actual first read consumes PL into its Cantor components, adding the
first to AC and restoring the second to PL. The whole nine-register file is
preserved except for those two fields; both scratch fields return to zero. -/
theorem read_ac (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number readEntry : V) file)=
        liveValue (number nextRead : V)
          (put acReg (regValue file acReg+first (regValue file plReg))
            (put plReg (second (regValue file plReg)) file)) := by
  let n := regValue file plReg
  obtain ⟨time,hreach⟩ := walk_reach file h1 h2 n le_rfl
  let g := walkFile file n
  have hg0 : regValue g plReg=0 := by
    dsimp only [g]
    rw [walkFile_pl,tsub_self]
  have hfirst : controlRun 1 (liveValue (number readEntry : V) g)=
      liveValue (number restorePLTest : V) g := by rw [run_one,step_read_zero g hg0]
  have hp := move_s2_pl g
  rw [show regValue g s2Reg=second n by exact walkFile_s2 _ _,hg0,zero_add] at hp
  let restored := put plReg (second n) (put s2Reg 0 g)
  have hr1 : regValue restored s1Reg=first n := by
    dsimp only [restored,g]
    rw [read_put_other _ _ plReg s1Reg (by decide),
      read_put_other _ _ s2Reg s1Reg (by decide),walkFile_s1]
  have hra : regValue restored acReg=regValue file acReg := by
    dsimp only [restored,g]
    rw [read_put_other _ _ plReg acReg (by decide),
      read_put_other _ _ s2Reg acReg (by decide),walkFile_ac]
  have ha := move_s1_ac restored
  rw [hr1,hra] at ha
  have hput1 : put s1Reg 0 file=file := by rw [←h1]; exact put_same _ _
  have hput2 : put s2Reg 0 file=file := by rw [←h2]; exact put_same _ _
  have hf : put acReg (regValue file acReg+first n) (put s1Reg 0 restored)=
      put acReg (regValue file acReg+first n) (put plReg (second n) file) := by
    simp only [restored,g,walkFile,show regValue file plReg=n from rfl,tsub_self,
      put_commute s1Reg plReg (by decide),put_commute s2Reg plReg (by decide),
      put_commute s2Reg s1Reg (by decide),put_twice,hput1,hput2]
  refine ⟨((time+1)+(3*second n+1))+(3*first n+1),?_,?_⟩
  · rw [show ((time+1)+(3*second n+1))+(3*first n+1)=
        (((time+1)+(3*second n+1))+3*first n)+1 by ring]
    exact le_add_of_nonneg_left (Arithmetic.zero_le _)
  · rw [controlRun_add ((time+1)+(3*second n+1)) (3*first n+1)
        (liveValue (number readEntry : V) file),
      controlRun_add (time+1) (3*second n+1) (liveValue (number readEntry : V) file),
      controlRun_succ time _,hreach]
    rw [←run_one (liveValue (number readEntry : V) g),hfirst,hp,ha,hf]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlRead254

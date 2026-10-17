import BusyBeaver.ZFC.ArithmeticControlUnpair254

set_option autoImplicit false
noncomputable section

/-!
Actual numbered-control transfer/copy/pair helpers. The source/target fields
are literal physical bindings, and every finite control premise concerns the
current Prog254 catalogue. These helpers do not assert full L2/Enum equivalence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 (put s1Reg fetchTest)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlDispatch254
open ArithmeticControlUnpair254 (wsReg)
open FiniteControlTable254 RegisterPath

/-- Top formula/logical1 is stored in physical2. -/
def twReg : Fin 9 := 2

structure MoveShape where
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

/-- Copy-loop test, two increments, cont3, and literal zero exit. -/
structure CopyShape where
  test : Control
  firstInc : Control
  secondInc : Control
  again : Control
  exit : Control
  sourceLogical : Nat
  firstLogical : Nat
  secondLogical : Nat
  sourceIndex : Fin 9
  firstIndex : Fin 9
  secondIndex : Fin 9
  source_physical : Permutation252Frame.physOf sourceLogical=sourceIndex.val
  first_physical : Permutation252Frame.physOf firstLogical=firstIndex.val
  second_physical : Permutation252Frame.physOf secondLogical=secondIndex.val
  source_ne_first : sourceIndex≠firstIndex
  source_ne_second : sourceIndex≠secondIndex
  first_ne_second : firstIndex≠secondIndex
  test_edge : (source test).2=.decnz sourceLogical
  first_edge : (source firstInc).2=.inc firstLogical
  second_edge : (source secondInc).2=.inc secondLogical
  again_edge : (source again).2=.cont 3
  positive_target : resolveControl (incPath (source test).1)=firstInc
  first_target : resolveControl (incPath (source firstInc).1)=secondInc
  second_target : resolveControl (incPath (source secondInc).1)=again
  repeat_target : resolveControl (continuePath 3 (source again).1)=test
  zero_target : resolveControl (breakPath 1 (source test).1)=exit

/-- The actual pairing control has a copy, a decrement, one increment, a
transfer, and cont3. The register equalities are literal bindings. -/
structure PairShape where
  copy : CopyShape
  testS1 : Control
  incS2 : Control
  move : MoveShape
  again : Control
  exit : Control
  copy_source : copy.sourceIndex=twReg
  copy_first : copy.firstIndex=s2Reg
  copy_second : copy.secondIndex=s1Reg
  copy_exit : copy.exit=testS1
  move_source : move.sourceIndex=s1Reg
  move_target : move.targetIndex=twReg
  move_exit : move.exit=again
  test_edge : (source testS1).2=.decnz 6
  increment_edge : (source incS2).2=.inc 7
  again_edge : (source again).2=.cont 3
  positive_target : resolveControl (incPath (source testS1).1)=incS2
  zero_target : resolveControl (breakPath 1 (source testS1).1)=exit
  increment_target : resolveControl (incPath (source incS2).1)=move.test
  repeat_target : resolveControl (continuePath 3 (source again).1)=copy.test

section Scalar
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

lemma cantor_cycle {a b n : V} (hs : a+b=n+1) :
    cantor a b=cantor 0 n+b+1 := by
  rw [cantor,hs,triangle_succ]
  simp only [cantor,zero_add]
  ring

lemma cantor_cycle_accumulate (c : V) {a b n : V} (hs : a+b=n+1) :
    (c+b+1)+cantor 0 n=c+cantor a b := by
  calc
    (c+b+1)+cantor 0 n=c+(cantor 0 n+b+1) := by ring
    _=c+cantor a b := congrArg (fun z : V => c+z) (cantor_cycle hs).symm

end Scalar

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

private theorem move_read_source (c : MoveShape) (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf c.sourceLogical) 0=
      regValue file c.sourceIndex := by
  rw [c.source_physical]
  exact physicalValues_getD file c.sourceIndex
private theorem move_read_target (c : MoveShape) (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf c.targetLogical) 0=
      regValue file c.targetIndex := by
  rw [c.target_physical]
  exact physicalValues_getD file c.targetIndex
private theorem move_step_positive (c : MoveShape) (file : V)
    (h : regValue file c.sourceIndex≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.increment : V)
        (put c.sourceIndex (regValue file c.sourceIndex-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf c.sourceLogical) 0≠0 := by
    rwa [move_read_source]
  rw [step_decnz_positive c.test c.sourceLogical c.test_edge file hn,
    c.positive_target,move_read_source]
  simp only [put,c.source_physical]
private theorem move_step_zero (c : MoveShape) (file : V)
    (h : regValue file c.sourceIndex=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf c.sourceLogical) 0=0 := by
    rwa [move_read_source]
  rw [step_decnz_zero c.test c.sourceLogical c.test_edge file hz,c.zero_target]
private theorem move_step_increment (c : MoveShape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.increment : V) file)=
      liveValue (number c.again : V)
        (put c.targetIndex (regValue file c.targetIndex+1) file) := by
  rw [step_inc c.increment c.targetLogical c.increment_edge,c.increment_target,move_read_target]
  simp only [put,c.target_physical]
private theorem move_step_again (c : MoveShape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.again : V) file)=
      liveValue (number c.test : V) file := by
  rw [step_continue c.again 2 c.again_edge,c.repeat_target]

private def moveFile (c : MoveShape) (file t : V) : V :=
  put c.targetIndex (regValue file c.targetIndex+t)
    (put c.sourceIndex (regValue file c.sourceIndex-t) file)
private def moveCycle (c : MoveShape) (file : V) : V :=
  put c.targetIndex (regValue file c.targetIndex+1)
    (put c.sourceIndex (regValue file c.sourceIndex-1) file)
private theorem moveFile_source (c : MoveShape) (file t : V) :
    regValue (moveFile c file t) c.sourceIndex=regValue file c.sourceIndex-t := by
  rw [moveFile,read_put_other _ _ c.targetIndex c.sourceIndex c.distinct.symm,read_put_self]
private theorem moveFile_target (c : MoveShape) (file t : V) :
    regValue (moveFile c file t) c.targetIndex=regValue file c.targetIndex+t := by
  rw [moveFile,read_put_self]
private theorem moveFile_zero (c : MoveShape) (file : V) : moveFile c file 0=file := by
  simp only [moveFile,add_zero,tsub_zero,put_same]
private theorem moveFile_succ (c : MoveShape) (file t : V) :
    moveCycle c (moveFile c file t)=moveFile c file (t+1) := by
  rw [moveCycle,moveFile_source,moveFile_target]
  simp only [moveFile,put_commute c.sourceIndex c.targetIndex c.distinct,
    put_twice,←tsub_add_eq_tsub_tsub,add_assoc]
private theorem move_cycle (c : MoveShape) (file : V)
    (h : regValue file c.sourceIndex≠0) :
    controlRun 3 (liveValue (number c.test : V) file)=
      liveValue (number c.test : V) (moveCycle c file) := by
  rw [show (3 : V)=((0+1)+1)+1 by ring,
    controlRun_succ,controlRun_succ,controlRun_succ,controlRun_zero,
    move_step_positive c file h,move_step_increment,move_step_again]
  simp only [moveCycle,read_put_other _ _ c.sourceIndex c.targetIndex c.distinct]
private theorem move_run_internal (c : MoveShape) (file : V) :
    controlRun (3*regValue file c.sourceIndex+1) (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V) (moveFile c file (regValue file c.sourceIndex)) := by
  let n := regValue file c.sourceIndex
  have reach (t : V) : t≤n →
      controlRun (3*t) (liveValue (number c.test : V) file)=
        liveValue (number c.test : V) (moveFile c file t) := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold moveFile put
      definability
    case zero => intro _; rw [mul_zero,controlRun_zero,moveFile_zero]
    case succ t ih =>
      intro ht
      have hp := ih (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) ht)
      have hn : regValue (moveFile c file t) c.sourceIndex≠0 := by
        rw [moveFile_source]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) ht))
      rw [show 3*(t+1)=3*t+3 by ring,controlRun_add,hp,move_cycle _ _ hn,moveFile_succ]
  have hend := reach n le_rfl
  rw [controlRun_succ,hend,move_step_zero c _ (by rw [moveFile_source,tsub_self])]

/-- Exact all-internal transfer, preserving every other physical field. -/
theorem move_run (c : MoveShape) (file : V) :
    controlRun (3*regValue file c.sourceIndex+1) (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V)
        (put c.targetIndex (regValue file c.targetIndex+regValue file c.sourceIndex)
          (put c.sourceIndex 0 file)) := by
  simpa only [moveFile,tsub_self] using move_run_internal c file

private theorem copy_read_source (c : CopyShape) (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf c.sourceLogical) 0=
      regValue file c.sourceIndex := by
  rw [c.source_physical]
  exact physicalValues_getD file c.sourceIndex
private theorem copy_read_first (c : CopyShape) (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf c.firstLogical) 0=
      regValue file c.firstIndex := by
  rw [c.first_physical]
  exact physicalValues_getD file c.firstIndex
private theorem copy_read_second (c : CopyShape) (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf c.secondLogical) 0=
      regValue file c.secondIndex := by
  rw [c.second_physical]
  exact physicalValues_getD file c.secondIndex
private theorem copy_step_positive (c : CopyShape) (file : V)
    (h : regValue file c.sourceIndex≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.firstInc : V)
        (put c.sourceIndex (regValue file c.sourceIndex-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf c.sourceLogical) 0≠0 := by
    rwa [copy_read_source]
  rw [step_decnz_positive c.test c.sourceLogical c.test_edge file hn,
    c.positive_target,copy_read_source]
  simp only [put,c.source_physical]
private theorem copy_step_zero (c : CopyShape) (file : V)
    (h : regValue file c.sourceIndex=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf c.sourceLogical) 0=0 := by
    rwa [copy_read_source]
  rw [step_decnz_zero c.test c.sourceLogical c.test_edge file hz,c.zero_target]
private theorem copy_step_first (c : CopyShape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.firstInc : V) file)=
      liveValue (number c.secondInc : V)
        (put c.firstIndex (regValue file c.firstIndex+1) file) := by
  rw [step_inc c.firstInc c.firstLogical c.first_edge,c.first_target,copy_read_first]
  simp only [put,c.first_physical]
private theorem copy_step_second (c : CopyShape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.secondInc : V) file)=
      liveValue (number c.again : V)
        (put c.secondIndex (regValue file c.secondIndex+1) file) := by
  rw [step_inc c.secondInc c.secondLogical c.second_edge,c.second_target,copy_read_second]
  simp only [put,c.second_physical]
private theorem copy_step_again (c : CopyShape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.again : V) file)=
      liveValue (number c.test : V) file := by
  rw [step_continue c.again 3 c.again_edge,c.repeat_target]

private def copyFile (c : CopyShape) (file t : V) : V :=
  put c.secondIndex (regValue file c.secondIndex+t)
    (put c.firstIndex (regValue file c.firstIndex+t)
      (put c.sourceIndex (regValue file c.sourceIndex-t) file))
private def copyCycle (c : CopyShape) (file : V) : V :=
  put c.secondIndex (regValue file c.secondIndex+1)
    (put c.firstIndex (regValue file c.firstIndex+1)
      (put c.sourceIndex (regValue file c.sourceIndex-1) file))
private theorem copyFile_source (c : CopyShape) (file t : V) :
    regValue (copyFile c file t) c.sourceIndex=regValue file c.sourceIndex-t := by
  rw [copyFile,read_put_other _ _ c.secondIndex c.sourceIndex c.source_ne_second.symm,
    read_put_other _ _ c.firstIndex c.sourceIndex c.source_ne_first.symm,read_put_self]
private theorem copyFile_first (c : CopyShape) (file t : V) :
    regValue (copyFile c file t) c.firstIndex=regValue file c.firstIndex+t := by
  rw [copyFile,read_put_other _ _ c.secondIndex c.firstIndex c.first_ne_second.symm,read_put_self]
private theorem copyFile_second (c : CopyShape) (file t : V) :
    regValue (copyFile c file t) c.secondIndex=regValue file c.secondIndex+t := by
  rw [copyFile,read_put_self]
private theorem copyFile_zero (c : CopyShape) (file : V) : copyFile c file 0=file := by
  simp only [copyFile,add_zero,tsub_zero,put_same]
private theorem copyFile_succ (c : CopyShape) (file t : V) :
    copyCycle c (copyFile c file t)=copyFile c file (t+1) := by
  rw [copyCycle,copyFile_source,copyFile_first,copyFile_second]
  simp only [copyFile,put_commute c.sourceIndex c.firstIndex c.source_ne_first,
    put_commute c.sourceIndex c.secondIndex c.source_ne_second,
    put_commute c.firstIndex c.secondIndex c.first_ne_second,
    put_twice,←tsub_add_eq_tsub_tsub,add_assoc]
private theorem copy_cycle (c : CopyShape) (file : V)
    (h : regValue file c.sourceIndex≠0) :
    controlRun 4 (liveValue (number c.test : V) file)=
      liveValue (number c.test : V) (copyCycle c file) := by
  rw [show (4 : V)=(((0+1)+1)+1)+1 by ring,
    controlRun_succ,controlRun_succ,controlRun_succ,controlRun_succ,controlRun_zero,
    copy_step_positive c file h,copy_step_first,copy_step_second,copy_step_again]
  simp only [copyCycle,read_put_other _ _ c.sourceIndex c.firstIndex c.source_ne_first,
    read_put_other _ _ c.firstIndex c.secondIndex c.first_ne_second,
    read_put_other _ _ c.sourceIndex c.secondIndex c.source_ne_second]

/-- Exact copy to two distinct fields; all counters may be internal. -/
theorem copy_run (c : CopyShape) (file : V) :
    controlRun (4*regValue file c.sourceIndex+1) (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V)
        (put c.secondIndex (regValue file c.secondIndex+regValue file c.sourceIndex)
          (put c.firstIndex (regValue file c.firstIndex+regValue file c.sourceIndex)
            (put c.sourceIndex 0 file))) := by
  let n := regValue file c.sourceIndex
  have reach (t : V) : t≤n →
      controlRun (4*t) (liveValue (number c.test : V) file)=
        liveValue (number c.test : V) (copyFile c file t) := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold copyFile put
      definability
    case zero => intro _; rw [mul_zero,controlRun_zero,copyFile_zero]
    case succ t ih =>
      intro ht
      have hp := ih (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) ht)
      have hn : regValue (copyFile c file t) c.sourceIndex≠0 := by
        rw [copyFile_source]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) ht))
      rw [show 4*(t+1)=4*t+4 by ring,controlRun_add,hp,copy_cycle _ _ hn,copyFile_succ]
  have hend := reach n le_rfl
  rw [controlRun_succ,hend,copy_step_zero c _ (by rw [copyFile_source,tsub_self])]
  simp only [copyFile,n,tsub_self]

private theorem run_one (state : V) : controlRun 1 state=ArithmeticControlStep254.stepValue state := by
  rw [show (1 : V)=0+1 by ring,controlRun_succ,controlRun_zero]

/-- Only these three fields vary during pairing. -/
def pairFile (file a b c : V) : V := put s1Reg a (put s2Reg c (put twReg b file))
private theorem pairFile_s1 (file a b c : V) : regValue (pairFile file a b c) s1Reg=a := by
  rw [pairFile,read_put_self]
private theorem pairFile_s2 (file a b c : V) : regValue (pairFile file a b c) s2Reg=c := by
  rw [pairFile,read_put_other _ _ s1Reg s2Reg (by decide),read_put_self]
private theorem pairFile_tw (file a b c : V) : regValue (pairFile file a b c) twReg=b := by
  rw [pairFile,read_put_other _ _ s1Reg twReg (by decide),
    read_put_other _ _ s2Reg twReg (by decide),read_put_self]
private theorem pairFile_same (file : V) :
    pairFile file (regValue file s1Reg) (regValue file twReg) (regValue file s2Reg)=file := by
  simp only [pairFile,put_same]
private theorem pairFile_put_s1 (file a b c x : V) :
    put s1Reg x (pairFile file a b c)=pairFile file x b c := by
  simp only [pairFile,put_twice]
private theorem pairFile_put_s2 (file a b c x : V) :
    put s2Reg x (pairFile file a b c)=pairFile file a b x := by
  simp only [pairFile,put_commute s2Reg s1Reg (by decide),put_twice]
private theorem pairFile_put_tw (file a b c x : V) :
    put twReg x (pairFile file a b c)=pairFile file a x c := by
  simp only [pairFile,put_commute twReg s1Reg (by decide),
    put_commute twReg s2Reg (by decide),put_twice]
private theorem pairFile_overwrite (file a b c x y z : V) :
    pairFile (pairFile file a b c) x y z=pairFile file x y z := by
  simp only [pairFile,put_commute twReg s1Reg (by decide),
    put_commute twReg s2Reg (by decide),put_commute s2Reg s1Reg (by decide),put_twice]

private theorem pair_copy (c : PairShape) (file : V) :
    controlRun (4*regValue file twReg+1) (liveValue (number c.copy.test : V) file)=
      liveValue (number c.testS1 : V)
        (pairFile file (regValue file s1Reg+regValue file twReg) 0
          (regValue file s2Reg+regValue file twReg)) := by
  simpa only [c.copy_source,c.copy_first,c.copy_second,c.copy_exit,pairFile] using copy_run c.copy file
private theorem pair_move (c : PairShape) (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number c.move.test : V) file)=
      liveValue (number c.again : V)
        (put twReg (regValue file twReg+regValue file s1Reg) (put s1Reg 0 file)) := by
  simpa only [c.move_source,c.move_target,c.move_exit] using move_run c.move file
private theorem pair_step_positive (c : PairShape) (file : V)
    (h : regValue file s1Reg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.testS1 : V) file)=
      liveValue (number c.incS2 : V) (put s1Reg (regValue file s1Reg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 6) 0≠0 := by
    rw [show (physicalValues file).getD (Permutation252Frame.physOf 6) 0=regValue file s1Reg from physicalValues_getD file s1Reg]
    exact h
  rw [step_decnz_positive c.testS1 6 c.test_edge file hn,c.positive_target,
    show (physicalValues file).getD (Permutation252Frame.physOf 6) 0=regValue file s1Reg from physicalValues_getD file s1Reg]
  rfl
private theorem pair_step_zero (c : PairShape) (file : V) (h : regValue file s1Reg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.testS1 : V) file)=
      liveValue (number c.exit : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 6) 0=0 := by
    rw [show (physicalValues file).getD (Permutation252Frame.physOf 6) 0=regValue file s1Reg from physicalValues_getD file s1Reg,h]
  rw [step_decnz_zero c.testS1 6 c.test_edge file hz,c.zero_target]
private theorem pair_step_increment (c : PairShape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.incS2 : V) file)=
      liveValue (number c.move.test : V) (put s2Reg (regValue file s2Reg+1) file) := by
  rw [step_inc c.incS2 7 c.increment_edge,c.increment_target,
    show (physicalValues file).getD (Permutation252Frame.physOf 7) 0=regValue file s2Reg from physicalValues_getD file s2Reg]
  rfl
private theorem pair_step_again (c : PairShape) (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number c.again : V) file)=
      liveValue (number c.copy.test : V) file := by
  rw [step_continue c.again 3 c.again_edge,c.repeat_target]

/-- One positive internal pairing cycle, without a totality oracle. -/
theorem pair_cycle (c : PairShape) (file : V)
    (hn : regValue file s1Reg+regValue file twReg≠0) :
    controlRun (4*regValue file twReg+3*(regValue file s1Reg+regValue file twReg)+2)
      (liveValue (number c.copy.test : V) file)=
      liveValue (number c.copy.test : V)
        (pairFile file 0 (regValue file s1Reg+regValue file twReg-1)
          (regValue file s2Reg+regValue file twReg+1)) := by
  let n := regValue file s1Reg+regValue file twReg
  let b := regValue file twReg
  let z := regValue file s2Reg
  have hnpos : 0<n := lt_of_le_of_ne (Arithmetic.zero_le n) (Ne.symm hn)
  have hn1 : 1≤n := by simpa only [zero_add] using (lt_iff_succ_le.mp hnpos)
  have hns : n-1+1=n := tsub_add_cancel_of_le hn1
  let g := pairFile file n 0 (z+b)
  have h2 : controlRun 2 (liveValue (number c.testS1 : V) g)=
      liveValue (number c.move.test : V) (pairFile file (n-1) 0 (z+b+1)) := by
    rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,
      pair_step_positive c g (by dsimp only [g]; rwa [pairFile_s1]),
      show put s1Reg (regValue g s1Reg-1) g=pairFile file (n-1) 0 (z+b) by
        simp only [g,pairFile_s1,pairFile_put_s1],pair_step_increment,
      pairFile_s2,pairFile_put_s2]
  have hp : controlRun (4*b+3) (liveValue (number c.copy.test : V) file)=
      liveValue (number c.move.test : V) (pairFile file (n-1) 0 (z+b+1)) := by
    rw [show 4*b+3=(4*b+1)+2 by ring,controlRun_add,pair_copy]
    exact h2
  have hm := pair_move c (pairFile file (n-1) 0 (z+b+1))
  simp only [pairFile_s1,pairFile_tw,zero_add,pairFile_put_s1,pairFile_put_tw] at hm
  have ht : 4*b+3*n+2=((4*b+3)+(3*(n-1)+1))+1 := by
    calc
      _ = 4*b+3*((n-1)+1)+2 := congrArg (fun x : V => 4*b+3*x+2) hns.symm
      _ = _ := by ring
  rw [ht,controlRun_add ((4*b+3)+(3*(n-1)+1)) 1 (liveValue (number c.copy.test : V) file),
    controlRun_add (4*b+3) (3*(n-1)+1) (liveValue (number c.copy.test : V) file),
    hp,hm,run_one,pair_step_again]

private theorem cantor_zero : cantor (0 : V) 0=0 := by simp [cantor,triangle]

/-- The terminal zero-input pairing test takes exactly two instructions. -/
theorem pair_zero (c : PairShape) (file : V)
    (ha : regValue file s1Reg=0) (hb : regValue file twReg=0) :
    controlRun 2 (liveValue (number c.copy.test : V) file)=liveValue (number c.exit : V) file := by
  have hz : regValue file c.copy.sourceIndex=0 := by rwa [c.copy_source]
  rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,copy_step_zero c.copy file hz,
    c.copy_exit,pair_step_zero c file ha]

local instance cantor_definable : 𝚺₀-Function₂[V] cantor := cantor_defined.to_definable

/-- Internal pairing totality uses a fixed original file and a bounded elapsed
count. All clocks/current coordinates are existential inside a Σ1 predicate. -/
theorem pair_run (p : PairShape) (file : V) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number p.copy.test : V) file)=
      liveValue (number p.exit : V)
        (pairFile file 0 0
          (regValue file s2Reg+cantor (regValue file s1Reg) (regValue file twReg))) := by
  let n := regValue file s1Reg+regValue file twReg
  let q := regValue file s2Reg+cantor (regValue file s1Reg) (regValue file twReg)
  have reach (t : V) : t≤n → ∃ time a b z : V,
      controlRun time (liveValue (number p.copy.test : V) file)=
        liveValue (number p.copy.test : V) (pairFile file a b z) ∧
      a+b+t=n ∧ z+cantor a b=q := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold pairFile put
      definability
    case zero =>
      intro _
      refine ⟨0,regValue file s1Reg,regValue file twReg,regValue file s2Reg,?_,?_,rfl⟩
      · rw [controlRun_zero,pairFile_same]
      · simp only [add_zero,n]
    case succ t ih =>
      intro ht
      obtain ⟨time,a,b,z,hr,hs,hq⟩ := ih
        (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) ht)
      have hn : a+b≠0 := by
        intro hz
        have htn : t=n := by simpa only [hz,zero_add] using hs
        rw [←htn] at ht
        exact not_le_of_gt (lt_add_one t) ht
      have hnpos : 0<a+b := lt_of_le_of_ne (Arithmetic.zero_le (a+b)) (Ne.symm hn)
      have hn1 : 1≤a+b := by simpa only [zero_add] using (lt_iff_succ_le.mp hnpos)
      have hns : a+b-1+1=a+b := tsub_add_cancel_of_le hn1
      have hc := pair_cycle p (pairFile file a b z)
        (by simpa only [pairFile_s1,pairFile_tw] using hn)
      simp only [pairFile_s1,pairFile_tw,pairFile_s2,pairFile_overwrite] at hc
      refine ⟨time+(4*b+3*(a+b)+2),0,a+b-1,z+b+1,?_,?_,?_⟩
      · rw [controlRun_add,hr,hc]
      · calc
          0+(a+b-1)+(t+1)=((a+b-1)+1)+t := by ring
          _=(a+b)+t := by rw [hns]
          _=n := hs
      · exact (cantor_cycle_accumulate z hns.symm).trans hq
  obtain ⟨time,a,b,z,hr,hs,hq⟩ := reach n le_rfl
  have hab : a+b=0 := add_right_cancel (show a+b+n=0+n by simpa only [zero_add] using hs)
  have ha : a=0 := le_antisymm
    (by
      calc
        a≤a+b := le_add_of_nonneg_right (Arithmetic.zero_le b)
        _=0 := hab)
    (Arithmetic.zero_le a)
  have hb : b=0 := le_antisymm
    (by
      calc
        b≤a+b := le_add_of_nonneg_left (Arithmetic.zero_le a)
        _=0 := hab)
    (Arithmetic.zero_le b)
  have hz : z=q := by simpa only [ha,hb,cantor_zero,add_zero] using hq
  rw [ha,hb,hz] at hr
  refine ⟨time+2,?_,?_⟩
  · rw [show time+2=(time+1)+1 by ring]
    exact le_add_of_nonneg_left (Arithmetic.zero_le _)
  · rw [controlRun_add,hr,pair_zero p _ (by rw [pairFile_s1]) (by rw [pairFile_tw])]

end Model

private theorem literal_source (P Q : List Bool) (e : Edge)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0=some (e,Q.length))
    (hc : consume P Q.length=Q) : source (resolveControl P)=(Q,e) := by
  rw [resolve_source P e Q.length hw,hc]

def dropPairTest : Control := resolveControl [true,true,true,false,true,false,true,false,true,true,false,false,false]
def dropPairCopyS2 : Control := resolveControl (incPath (source dropPairTest).1)
def dropPairCopyS1 : Control := resolveControl (incPath (source dropPairCopyS2).1)
def dropPairCopyAgain : Control := resolveControl (incPath (source dropPairCopyS1).1)
def dropPairTestS1 : Control := resolveControl (breakPath 1 (source dropPairTest).1)
def dropPairIncS2 : Control := resolveControl (incPath (source dropPairTestS1).1)
def dropPairMoveTest : Control := resolveControl (incPath (source dropPairIncS2).1)
def dropPairMoveInc : Control := resolveControl (incPath (source dropPairMoveTest).1)
def dropPairMoveAgain : Control := resolveControl (incPath (source dropPairMoveInc).1)
def dropPairAgain : Control := resolveControl (breakPath 1 (source dropPairMoveTest).1)
def dropPairExit : Control := resolveControl (breakPath 1 (source dropPairTestS1).1)

theorem dropPairTest_source : source dropPairTest=([true,true,true,false,true,false,true,false,true,true,false,false,false],.decnz 1) := by
  unfold dropPairTest
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairCopyS2_source : source dropPairCopyS2=([true,true,true,false,true,false,true,false,true,true,false,false,true,false],.inc 7) := by
  rw [dropPairCopyS2,dropPairTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairCopyS1_source : source dropPairCopyS1=([true,true,true,false,true,false,true,false,true,true,false,false,true,true,false],.inc 6) := by
  rw [dropPairCopyS1,dropPairCopyS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairCopyAgain_source : source dropPairCopyAgain=([true,true,true,false,true,false,true,false,true,true,false,false,true,true,true],.cont 3) := by
  rw [dropPairCopyAgain,dropPairCopyS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairTestS1_source : source dropPairTestS1=([true,true,true,false,true,false,true,false,true,true,false,true,false],.decnz 6) := by
  rw [dropPairTestS1,dropPairTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairIncS2_source : source dropPairIncS2=([true,true,true,false,true,false,true,false,true,true,false,true,true,false,false],.inc 7) := by
  rw [dropPairIncS2,dropPairTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairMoveTest_source : source dropPairMoveTest=([true,true,true,false,true,false,true,false,true,true,false,true,true,false,true,false],.decnz 6) := by
  rw [dropPairMoveTest,dropPairIncS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairMoveInc_source : source dropPairMoveInc=([true,true,true,false,true,false,true,false,true,true,false,true,true,false,true,true,false],.inc 1) := by
  rw [dropPairMoveInc,dropPairMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairMoveAgain_source : source dropPairMoveAgain=([true,true,true,false,true,false,true,false,true,true,false,true,true,false,true,true,true],.cont 2) := by
  rw [dropPairMoveAgain,dropPairMoveInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairAgain_source : source dropPairAgain=([true,true,true,false,true,false,true,false,true,true,false,true,true,true],.cont 3) := by
  rw [dropPairAgain,dropPairMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropPairExit_source : source dropPairExit=([true,true,true,false,true,false,true,false,true,true,true,false],.decnz 7) := by
  rw [dropPairExit,dropPairTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

def dropCopy : CopyShape where
  test := dropPairTest
  firstInc := dropPairCopyS2
  secondInc := dropPairCopyS1
  again := dropPairCopyAgain
  exit := dropPairTestS1
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
  test_edge := congrArg Prod.snd dropPairTest_source
  first_edge := congrArg Prod.snd dropPairCopyS2_source
  second_edge := congrArg Prod.snd dropPairCopyS1_source
  again_edge := congrArg Prod.snd dropPairCopyAgain_source
  positive_target := by
    apply source_injective
    rw [dropPairTest_source,dropPairCopyS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  first_target := by
    apply source_injective
    rw [dropPairCopyS2_source,dropPairCopyS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  second_target := by
    apply source_injective
    rw [dropPairCopyS1_source,dropPairCopyAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [dropPairCopyAgain_source,dropPairTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [dropPairTest_source,dropPairTestS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def dropMove : MoveShape where
  test := dropPairMoveTest
  increment := dropPairMoveInc
  again := dropPairMoveAgain
  exit := dropPairAgain
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd dropPairMoveTest_source
  increment_edge := congrArg Prod.snd dropPairMoveInc_source
  again_edge := congrArg Prod.snd dropPairMoveAgain_source
  positive_target := by
    apply source_injective
    rw [dropPairMoveTest_source,dropPairMoveInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [dropPairMoveInc_source,dropPairMoveAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [dropPairMoveAgain_source,dropPairMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [dropPairMoveTest_source,dropPairAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def dropPair : PairShape where
  copy := dropCopy
  testS1 := dropPairTestS1
  incS2 := dropPairIncS2
  move := dropMove
  again := dropPairAgain
  exit := dropPairExit
  copy_source := rfl
  copy_first := rfl
  copy_second := rfl
  copy_exit := by simp only [dropCopy]
  move_source := rfl
  move_target := rfl
  move_exit := by simp only [dropMove]
  test_edge := congrArg Prod.snd dropPairTestS1_source
  increment_edge := congrArg Prod.snd dropPairIncS2_source
  again_edge := congrArg Prod.snd dropPairAgain_source
  positive_target := by
    apply source_injective
    rw [dropPairTestS1_source,dropPairIncS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [dropPairTestS1_source,dropPairExit_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    dsimp only [dropMove]
    apply source_injective
    rw [dropPairIncS2_source,dropPairMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    dsimp only [dropCopy]
    apply source_injective
    rw [dropPairAgain_source,dropPairTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

/-- The actual DROP pairing occurrence accumulates scratch2; it is not
an unconditional pure push when that scratch field starts dirty. -/
theorem drop_pair_run {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (file : V) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number dropPairTest : V) file)=
      liveValue (number dropPairExit : V)
        (pairFile file 0 0
          (regValue file s2Reg+cantor (regValue file s1Reg) (regValue file twReg))) := by
  simpa only [dropPair,dropCopy] using pair_run dropPair file
def mpPairTest : Control := resolveControl [true,true,true,true,false,false,false,false,true,true,false,false,false]
def mpPairCopyS2 : Control := resolveControl (incPath (source mpPairTest).1)
def mpPairCopyS1 : Control := resolveControl (incPath (source mpPairCopyS2).1)
def mpPairCopyAgain : Control := resolveControl (incPath (source mpPairCopyS1).1)
def mpPairTestS1 : Control := resolveControl (breakPath 1 (source mpPairTest).1)
def mpPairIncS2 : Control := resolveControl (incPath (source mpPairTestS1).1)
def mpPairMoveTest : Control := resolveControl (incPath (source mpPairIncS2).1)
def mpPairMoveInc : Control := resolveControl (incPath (source mpPairMoveTest).1)
def mpPairMoveAgain : Control := resolveControl (incPath (source mpPairMoveInc).1)
def mpPairAgain : Control := resolveControl (breakPath 1 (source mpPairMoveTest).1)
def mpPairExit : Control := resolveControl (breakPath 1 (source mpPairTestS1).1)

theorem mpPairTest_source : source mpPairTest=([true,true,true,true,false,false,false,false,true,true,false,false,false],.decnz 1) := by
  unfold mpPairTest
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairCopyS2_source : source mpPairCopyS2=([true,true,true,true,false,false,false,false,true,true,false,false,true,false],.inc 7) := by
  rw [mpPairCopyS2,mpPairTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairCopyS1_source : source mpPairCopyS1=([true,true,true,true,false,false,false,false,true,true,false,false,true,true,false],.inc 6) := by
  rw [mpPairCopyS1,mpPairCopyS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairCopyAgain_source : source mpPairCopyAgain=([true,true,true,true,false,false,false,false,true,true,false,false,true,true,true],.cont 3) := by
  rw [mpPairCopyAgain,mpPairCopyS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairTestS1_source : source mpPairTestS1=([true,true,true,true,false,false,false,false,true,true,false,true,false],.decnz 6) := by
  rw [mpPairTestS1,mpPairTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairIncS2_source : source mpPairIncS2=([true,true,true,true,false,false,false,false,true,true,false,true,true,false,false],.inc 7) := by
  rw [mpPairIncS2,mpPairTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairMoveTest_source : source mpPairMoveTest=([true,true,true,true,false,false,false,false,true,true,false,true,true,false,true,false],.decnz 6) := by
  rw [mpPairMoveTest,mpPairIncS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairMoveInc_source : source mpPairMoveInc=([true,true,true,true,false,false,false,false,true,true,false,true,true,false,true,true,false],.inc 1) := by
  rw [mpPairMoveInc,mpPairMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairMoveAgain_source : source mpPairMoveAgain=([true,true,true,true,false,false,false,false,true,true,false,true,true,false,true,true,true],.cont 2) := by
  rw [mpPairMoveAgain,mpPairMoveInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairAgain_source : source mpPairAgain=([true,true,true,true,false,false,false,false,true,true,false,true,true,true],.cont 3) := by
  rw [mpPairAgain,mpPairMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPairExit_source : source mpPairExit=([true,true,true,true,false,false,false,false,true,true,true,false],.decnz 7) := by
  rw [mpPairExit,mpPairTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

def mpCopy : CopyShape where
  test := mpPairTest
  firstInc := mpPairCopyS2
  secondInc := mpPairCopyS1
  again := mpPairCopyAgain
  exit := mpPairTestS1
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
  test_edge := congrArg Prod.snd mpPairTest_source
  first_edge := congrArg Prod.snd mpPairCopyS2_source
  second_edge := congrArg Prod.snd mpPairCopyS1_source
  again_edge := congrArg Prod.snd mpPairCopyAgain_source
  positive_target := by
    apply source_injective
    rw [mpPairTest_source,mpPairCopyS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  first_target := by
    apply source_injective
    rw [mpPairCopyS2_source,mpPairCopyS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  second_target := by
    apply source_injective
    rw [mpPairCopyS1_source,mpPairCopyAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpPairCopyAgain_source,mpPairTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpPairTest_source,mpPairTestS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpMove : MoveShape where
  test := mpPairMoveTest
  increment := mpPairMoveInc
  again := mpPairMoveAgain
  exit := mpPairAgain
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd mpPairMoveTest_source
  increment_edge := congrArg Prod.snd mpPairMoveInc_source
  again_edge := congrArg Prod.snd mpPairMoveAgain_source
  positive_target := by
    apply source_injective
    rw [mpPairMoveTest_source,mpPairMoveInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [mpPairMoveInc_source,mpPairMoveAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpPairMoveAgain_source,mpPairMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpPairMoveTest_source,mpPairAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpPair : PairShape where
  copy := mpCopy
  testS1 := mpPairTestS1
  incS2 := mpPairIncS2
  move := mpMove
  again := mpPairAgain
  exit := mpPairExit
  copy_source := rfl
  copy_first := rfl
  copy_second := rfl
  copy_exit := by simp only [mpCopy]
  move_source := rfl
  move_target := rfl
  move_exit := by simp only [mpMove]
  test_edge := congrArg Prod.snd mpPairTestS1_source
  increment_edge := congrArg Prod.snd mpPairIncS2_source
  again_edge := congrArg Prod.snd mpPairAgain_source
  positive_target := by
    apply source_injective
    rw [mpPairTestS1_source,mpPairIncS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpPairTestS1_source,mpPairExit_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    dsimp only [mpMove]
    apply source_injective
    rw [mpPairIncS2_source,mpPairMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    dsimp only [mpCopy]
    apply source_injective
    rw [mpPairAgain_source,mpPairTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

/-- The actual MP pairing occurrence accumulates scratch2; it is not
an unconditional pure push when that scratch field starts dirty. -/
theorem mp_pair_run {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (file : V) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpPairTest : V) file)=
      liveValue (number mpPairExit : V)
        (pairFile file 0 0
          (regValue file s2Reg+cantor (regValue file s1Reg) (regValue file twReg))) := by
  simpa only [mpPair,mpCopy] using pair_run mpPair file

end SetTheory.BusyBeaver.ZFC.ArithmeticControlPair254

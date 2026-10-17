import BusyBeaver.ZFC.ArithmeticControlClear254

set_option autoImplicit false
noncomputable section

/-!
Actual fetch contracts for the numbered literal interpreter.
The control constants name only the first eleven actual catalogue leaves.
The all-internal copy/restore loops below serve this concrete fetch block;
no full internal L2/Enum equivalence is asserted here.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlRun254 ArithmeticControlSimulation254 ArithmeticControlStep254
open ArithmeticControlFrame254 ArithmeticControlClear254 FiniteControlTable254 RegisterPath

-- The literal prefix of Prog254 rows 0--9, in actual leaf-catalogue order.
def fetchTest : Control := ⟨0,by decide⟩
def fetchBreak : Control := ⟨1,by decide⟩
def copyTest : Control := ⟨2,by decide⟩
def copyPL : Control := ⟨3,by decide⟩
def copyS1 : Control := ⟨4,by decide⟩
def copyContinue : Control := ⟨5,by decide⟩
def restoreTest : Control := ⟨6,by decide⟩
def restoreNP : Control := ⟨7,by decide⟩
def restoreContinue : Control := ⟨8,by decide⟩
def bumpNP : Control := ⟨9,by decide⟩
def readEntry : Control := ⟨10,by decide⟩

theorem fetchTest_source : source fetchTest=([false,false,false],.decnz 8) := by rfl
theorem fetchBreak_source : source fetchBreak=([false,false,true],.brk 1) := by rfl
theorem copyTest_source : source copyTest=([false,true,false,false],.decnz 0) := by rfl
theorem copyPL_source : source copyPL=([false,true,false,true,false],.inc 8) := by rfl
theorem copyS1_source : source copyS1=([false,true,false,true,true,false],.inc 6) := by rfl
theorem copyContinue_source : source copyContinue=([false,true,false,true,true,true],.cont 3) := by rfl
theorem restoreTest_source : source restoreTest=([false,true,true,false,false],.decnz 6) := by rfl
theorem restoreNP_source : source restoreNP=([false,true,true,false,true,false],.inc 0) := by rfl
theorem restoreContinue_source : source restoreContinue=([false,true,true,false,true,true],.cont 2) := by rfl
theorem bumpNP_source : source bumpNP=([false,true,true,true],.inc 0) := by rfl
theorem readEntry_source : source readEntry=([true,false,false,false,false],.decnz 8) := by rfl

theorem first_entry : initialControl=fetchTest := by rw [initialControl,empty_control]; rfl
theorem read_entry : resolveControl [true]=readEntry := by rfl

theorem next_fetch_positive : resolveControl (incPath (source fetchTest).1)=fetchBreak := by rfl
theorem next_fetch_zero : resolveControl (breakPath 1 (source fetchTest).1)=copyTest := by rfl
theorem next_fetch_break : resolveControl (breakPath 1 (source fetchBreak).1)=readEntry := by rfl
theorem next_copy_positive : resolveControl (incPath (source copyTest).1)=copyPL := by rfl
theorem next_copy_pl : resolveControl (incPath (source copyPL).1)=copyS1 := by rfl
theorem next_copy_s1 : resolveControl (incPath (source copyS1).1)=copyContinue := by rfl
theorem next_copy_continue : resolveControl (continuePath 3 (source copyContinue).1)=copyTest := by rfl
theorem next_copy_zero : resolveControl (breakPath 1 (source copyTest).1)=restoreTest := by rfl
theorem next_restore_positive : resolveControl (incPath (source restoreTest).1)=restoreNP := by rfl
theorem next_restore_np : resolveControl (incPath (source restoreNP).1)=restoreContinue := by rfl
theorem next_restore_continue : resolveControl (continuePath 2 (source restoreContinue).1)=restoreTest := by rfl
theorem next_restore_zero : resolveControl (breakPath 1 (source restoreTest).1)=bumpNP := by rfl
theorem next_bump : resolveControl (incPath (source bumpNP).1)=readEntry := by rfl

-- Actual logical-to-physical mapping: NP=6, PL=1, scratch1=8.
def npReg : Fin 9 := 6
def plReg : Fin 9 := 1
def s1Reg : Fin 9 := 8

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def put (p : Fin 9) (x file : V) : V := writeValue (p.val : V) x file
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

private theorem read_np (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 0) 0=regValue file npReg :=
  physicalValues_getD file npReg
private theorem read_pl (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 8) 0=regValue file plReg :=
  physicalValues_getD file plReg
private theorem read_s1 (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 6) 0=regValue file s1Reg :=
  physicalValues_getD file s1Reg

private theorem step_fetch_positive (file : V) (h : regValue file plReg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number fetchTest : V) file)=
      liveValue (number fetchBreak : V) (put plReg (regValue file plReg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 8) 0≠0 := by rwa [read_pl]
  rw [step_decnz_positive fetchTest 8 (congrArg Prod.snd fetchTest_source) file hn,
    next_fetch_positive,read_pl]
  rfl
private theorem step_fetch_zero (file : V) (h : regValue file plReg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number fetchTest : V) file)=
      liveValue (number copyTest : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 8) 0=0 := by rwa [read_pl]
  rw [step_decnz_zero fetchTest 8 (congrArg Prod.snd fetchTest_source) file hz,next_fetch_zero]
private theorem step_fetch_break (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number fetchBreak : V) file)=
      liveValue (number readEntry : V) file := by
  rw [step_break fetchBreak 1 (congrArg Prod.snd fetchBreak_source),next_fetch_break]

private theorem step_copy_positive (file : V) (h : regValue file npReg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number copyTest : V) file)=
      liveValue (number copyPL : V) (put npReg (regValue file npReg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 0) 0≠0 := by rwa [read_np]
  rw [step_decnz_positive copyTest 0 (congrArg Prod.snd copyTest_source) file hn,
    next_copy_positive,read_np]
  rfl
private theorem step_copy_zero (file : V) (h : regValue file npReg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number copyTest : V) file)=
      liveValue (number restoreTest : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 0) 0=0 := by rwa [read_np]
  rw [step_decnz_zero copyTest 0 (congrArg Prod.snd copyTest_source) file hz,next_copy_zero]
private theorem step_copy_pl (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number copyPL : V) file)=
      liveValue (number copyS1 : V) (put plReg (regValue file plReg+1) file) := by
  rw [step_inc copyPL 8 (congrArg Prod.snd copyPL_source),next_copy_pl,read_pl]
  rfl
private theorem step_copy_s1 (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number copyS1 : V) file)=
      liveValue (number copyContinue : V) (put s1Reg (regValue file s1Reg+1) file) := by
  rw [step_inc copyS1 6 (congrArg Prod.snd copyS1_source),next_copy_s1,read_s1]
  rfl
private theorem step_copy_continue (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number copyContinue : V) file)=
      liveValue (number copyTest : V) file := by
  rw [step_continue copyContinue 3 (congrArg Prod.snd copyContinue_source),next_copy_continue]

private theorem step_restore_positive (file : V) (h : regValue file s1Reg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number restoreTest : V) file)=
      liveValue (number restoreNP : V) (put s1Reg (regValue file s1Reg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 6) 0≠0 := by rwa [read_s1]
  rw [step_decnz_positive restoreTest 6 (congrArg Prod.snd restoreTest_source) file hn,
    next_restore_positive,read_s1]
  rfl
private theorem step_restore_zero (file : V) (h : regValue file s1Reg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number restoreTest : V) file)=
      liveValue (number bumpNP : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 6) 0=0 := by rwa [read_s1]
  rw [step_decnz_zero restoreTest 6 (congrArg Prod.snd restoreTest_source) file hz,next_restore_zero]
private theorem step_restore_np (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number restoreNP : V) file)=
      liveValue (number restoreContinue : V) (put npReg (regValue file npReg+1) file) := by
  rw [step_inc restoreNP 0 (congrArg Prod.snd restoreNP_source),next_restore_np,read_np]
  rfl
private theorem step_restore_continue (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number restoreContinue : V) file)=
      liveValue (number restoreTest : V) file := by
  rw [step_continue restoreContinue 2 (congrArg Prod.snd restoreContinue_source),next_restore_continue]
private theorem step_bump (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number bumpNP : V) file)=
      liveValue (number readEntry : V) (put npReg (regValue file npReg+1) file) := by
  rw [step_inc bumpNP 0 (congrArg Prod.snd bumpNP_source),next_bump,read_np]
  rfl

def copyFile (file t : V) : V :=
  put s1Reg (regValue file s1Reg+t)
    (put plReg (regValue file plReg+t) (put npReg (regValue file npReg-t) file))
private def copyCycle (file : V) : V :=
  put s1Reg (regValue file s1Reg+1)
    (put plReg (regValue file plReg+1) (put npReg (regValue file npReg-1) file))
private theorem copyFile_np (file t : V) : regValue (copyFile file t) npReg=regValue file npReg-t := by
  rw [copyFile,read_put_other _ _ s1Reg npReg (by decide),
    read_put_other _ _ plReg npReg (by decide),read_put_self]
private theorem copyFile_pl (file t : V) : regValue (copyFile file t) plReg=regValue file plReg+t := by
  rw [copyFile,read_put_other _ _ s1Reg plReg (by decide),read_put_self]
private theorem copyFile_s1 (file t : V) : regValue (copyFile file t) s1Reg=regValue file s1Reg+t := by
  rw [copyFile,read_put_self]
private theorem copyFile_zero (file : V) : copyFile file 0=file := by
  simp only [copyFile,add_zero,tsub_zero,put_same]
private theorem copyFile_succ (file t : V) : copyCycle (copyFile file t)=copyFile file (t+1) := by
  rw [copyCycle,copyFile_np,copyFile_pl,copyFile_s1]
  simp only [copyFile,
    put_commute npReg s1Reg (by decide),put_commute npReg plReg (by decide),
    put_commute plReg s1Reg (by decide),put_twice,←tsub_add_eq_tsub_tsub,add_assoc]

private theorem copy_cycle (file : V) (h : regValue file npReg≠0) :
    controlRun 4 (liveValue (number copyTest : V) file)=
      liveValue (number copyTest : V) (copyCycle file) := by
  rw [show (4 : V)=(((0+1)+1)+1)+1 by ring,
    controlRun_succ,controlRun_succ,controlRun_succ,controlRun_succ,controlRun_zero,
    step_copy_positive file h,step_copy_pl,step_copy_s1,step_copy_continue]
  simp only [copyCycle,read_put_other _ _ npReg plReg (by decide),
    read_put_other _ _ plReg s1Reg (by decide),read_put_other _ _ npReg s1Reg (by decide)]

local instance write_definable : 𝚺₁-Function₃[V] writeValue := write_defined.to_definable
local instance live_definable : 𝚺₁-Function₂[V] liveValue := live_defined.to_definable

/-- Actual copy loop: the internal source value is exhausted into PL and s1.
This ends at the following restore test, not at a synthetic return control. -/
theorem copy_run (file : V) :
    controlRun (4*regValue file npReg+1) (liveValue (number copyTest : V) file)=
      liveValue (number restoreTest : V) (copyFile file (regValue file npReg)) := by
  let n := regValue file npReg
  have reach (t : V) : t≤n →
      controlRun (4*t) (liveValue (number copyTest : V) file)=
        liveValue (number copyTest : V) (copyFile file t) := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold copyFile put
      definability
    case zero => intro _; rw [mul_zero,controlRun_zero,copyFile_zero]
    case succ t ih =>
      intro ht
      have hp := ih (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) ht)
      have hn : regValue (copyFile file t) npReg≠0 := by
        rw [copyFile_np]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) ht))
      rw [show 4*(t+1)=4*t+4 by ring,controlRun_add,hp,copy_cycle _ hn,copyFile_succ]
  have hend := reach n le_rfl
  rw [controlRun_succ,hend,step_copy_zero _ (by rw [copyFile_np,tsub_self])]

def restoreFile (file t : V) : V :=
  put npReg (regValue file npReg+t) (put s1Reg (regValue file s1Reg-t) file)
private def restoreCycle (file : V) : V :=
  put npReg (regValue file npReg+1) (put s1Reg (regValue file s1Reg-1) file)
private theorem restoreFile_np (file t : V) : regValue (restoreFile file t) npReg=regValue file npReg+t := by
  rw [restoreFile,read_put_self]
private theorem restoreFile_s1 (file t : V) : regValue (restoreFile file t) s1Reg=regValue file s1Reg-t := by
  rw [restoreFile,read_put_other _ _ npReg s1Reg (by decide),read_put_self]
private theorem restoreFile_zero (file : V) : restoreFile file 0=file := by
  simp only [restoreFile,add_zero,tsub_zero,put_same]
private theorem restoreFile_succ (file t : V) : restoreCycle (restoreFile file t)=restoreFile file (t+1) := by
  rw [restoreCycle,restoreFile_np,restoreFile_s1]
  simp only [restoreFile,
    put_commute s1Reg npReg (by decide),put_twice,←tsub_add_eq_tsub_tsub,add_assoc]
private theorem restore_cycle (file : V) (h : regValue file s1Reg≠0) :
    controlRun 3 (liveValue (number restoreTest : V) file)=
      liveValue (number restoreTest : V) (restoreCycle file) := by
  rw [show (3 : V)=((0+1)+1)+1 by ring,
    controlRun_succ,controlRun_succ,controlRun_succ,controlRun_zero,
    step_restore_positive file h,step_restore_np,step_restore_continue]
  simp only [restoreCycle,read_put_other _ _ s1Reg npReg (by decide)]

/-- Actual restore loop: consume s1 into NP and stop at the literal final NP
increment. The loop is valid for arbitrary initial NP and s1. -/
theorem restore_run (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number restoreTest : V) file)=
      liveValue (number bumpNP : V) (restoreFile file (regValue file s1Reg)) := by
  let n := regValue file s1Reg
  have reach (t : V) : t≤n →
      controlRun (3*t) (liveValue (number restoreTest : V) file)=
        liveValue (number restoreTest : V) (restoreFile file t) := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold restoreFile put
      definability
    case zero => intro _; rw [mul_zero,controlRun_zero,restoreFile_zero]
    case succ t ih =>
      intro ht
      have hp := ih (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) ht)
      have hn : regValue (restoreFile file t) s1Reg≠0 := by
        rw [restoreFile_s1]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) ht))
      rw [show 3*(t+1)=3*t+3 by ring,controlRun_add,hp,restore_cycle _ hn,restoreFile_succ]
  have hend := reach n le_rfl
  rw [controlRun_succ,hend,step_restore_zero _ (by rw [restoreFile_s1,tsub_self])]

private theorem run_one (state : V) : controlRun 1 state=ArithmeticControlStep254.stepValue state := by
  rw [show (1 : V)=0+1 by ring,controlRun_succ,controlRun_zero]

/-- The positive-PL branch is exactly two instructions, regardless of NP or
scratch values. It stops at the actual first read leaf. -/
theorem fetch_positive (file : V) (hpl : regValue file plReg≠0) :
    controlRun 2 (liveValue (number fetchTest : V) file)=
      liveValue (number readEntry : V) (put plReg (regValue file plReg-1) file) := by
  rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,
    step_fetch_positive file hpl,step_fetch_break]

/-- Fetch a new candidate from an exhausted PL and clean scratch1. Every
counter/file value may be internal; the count is logical interpreter time. -/
theorem fetch_zero (file : V) (hpl : regValue file plReg=0) (hs1 : regValue file s1Reg=0) :
    controlRun (7*regValue file npReg+4) (liveValue (number fetchTest : V) file)=
      liveValue (number readEntry : V)
        (put npReg (regValue file npReg+1) (put plReg (regValue file npReg) file)) := by
  let n := regValue file npReg
  have hfirst : controlRun 1 (liveValue (number fetchTest : V) file)=
      liveValue (number copyTest : V) file := by rw [run_one,step_fetch_zero file hpl]
  have hc := copy_run file
  have hr := restore_run (copyFile file n)
  rw [copyFile_s1,hs1,zero_add] at hr
  have hzput : put s1Reg 0 file=file := by rw [←hs1]; exact put_same s1Reg file
  have hfile : put npReg (regValue (restoreFile (copyFile file n) n) npReg+1)
      (restoreFile (copyFile file n) n)=put npReg (n+1) (put plReg n file) := by
    rw [restoreFile_np,copyFile_np]
    simp only [restoreFile,copyFile_np,copyFile_s1]
    simp only [copyFile,hpl,hs1,
      show regValue file npReg=n from rfl,tsub_self,zero_add,
      put_commute plReg npReg (by decide),put_commute s1Reg npReg (by decide),
      put_commute s1Reg plReg (by decide),put_twice,hzput]
  have hlast : controlRun 1
      (liveValue (number bumpNP : V) (restoreFile (copyFile file n) n))=
      liveValue (number readEntry : V) (put npReg (n+1) (put plReg n file)) := by
    rw [run_one,step_bump,hfile]
  rw [show 7*regValue file npReg+4=((1+(4*n+1))+(3*n+1))+1 by dsimp [n]; ring,
    controlRun_add ((1+(4*n+1))+(3*n+1)) 1 (liveValue (number fetchTest : V) file),
    controlRun_add (1+(4*n+1)) (3*n+1) (liveValue (number fetchTest : V) file),
    controlRun_add 1 (4*n+1) (liveValue (number fetchTest : V) file),hfirst,hc,hr,hlast]

/-- Actual initial numbered control is this fetch test. No bootstrap clock is
consumed by the equality; it does not identify the full interpreter with Enum. -/
theorem fetch_zero_initial (file : V) (hpl : regValue file plReg=0) (hs1 : regValue file s1Reg=0) :
    controlRun (7*regValue file npReg+4) (liveValue (number initialControl : V) file)=
      liveValue (number readEntry : V)
        (put npReg (regValue file npReg+1) (put plReg (regValue file npReg) file)) := by
  rw [first_entry]
  exact fetch_zero file hpl hs1

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlFetch254

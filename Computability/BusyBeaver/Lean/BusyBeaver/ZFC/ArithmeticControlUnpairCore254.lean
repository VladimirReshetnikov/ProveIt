import BusyBeaver.ZFC.ArithmeticControlParamPush254

set_option autoImplicit false
noncomputable section

/-!
The actual MP unpair stops after restoration of its second component. This
short finite shape has no output-transfer requirement. It retains the first
component in scratch1 and reuses the checked generic transfer contract.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 (put s1Reg fetchTest)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlPair254 (MoveShape move_run twReg)
open ArithmeticControlUnpair254 (wsReg bodyFile bodyClock)
open ArithmeticControlParamPush254 (mpPopEntry mpPopEntry_source paramPushFile mpParam_run)
open ArithmeticControlDispatch254 (mpEntry)
open FiniteControlTable254 RegisterPath

/-- Literal prefix of the unpair algorithm, with its actual restore-loop exit.
The main field is distinct from both scratch fields; no output loop is assumed. -/
structure UnpairCoreShape where
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
  exit : Control
  mainLogical : Nat
  mainIndex : Fin 9
  main_physical : Permutation252Frame.physOf mainLogical=mainIndex.val
  main_ne_s1 : mainIndex≠s1Reg
  main_ne_s2 : mainIndex≠s2Reg
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
  next_restore_main_zero : resolveControl (breakPath 1 (source restoreMainTest).1)=exit

private def bodyTransfer (c : UnpairCoreShape) : MoveShape where
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

private def restoreMainTransfer (c : UnpairCoreShape) : MoveShape where
  test := c.restoreMainTest
  increment := c.restoreMainInc
  again := c.restoreMainContinue
  exit := c.exit
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

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (c : UnpairCoreShape)
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

/-- The nested body transfer, including its zero test and exit. -/
theorem move_s2_s1 (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.bodyMoveTest : V) file)=
      liveValue (number c.bodyContinue : V)
        (put s1Reg (regValue file s1Reg+regValue file s2Reg) (put s2Reg 0 file)) := by
  simpa only [bodyTransfer] using move_run (bodyTransfer c) file

/-- Restore the second component into main and stop at the core's actual exit. -/
theorem move_s2_main (file : V) :
    controlRun (3*regValue file s2Reg+1) (liveValue (number c.restoreMainTest : V) file)=
      liveValue (number c.exit : V)
        (put c.mainIndex (regValue file c.mainIndex+regValue file s2Reg) (put s2Reg 0 file)) := by
  simpa only [restoreMainTransfer] using move_run (restoreMainTransfer c) file

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

/-- The core leaves the first Cantor component in scratch1 and restores the
second to main. Both input scratch fields must be zero; all other fields are
preserved in the whole-file endpoint. The runtime witness may be internal. -/
theorem core_run (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number c.readEntry : V) file)=
        liveValue (number c.exit : V)
          (put s1Reg (first (regValue file c.mainIndex))
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
  have hput2 : put s2Reg 0 file=file := by rw [←h2]; exact put_same _ _
  have hf : put c.mainIndex (second n) (put s2Reg 0 g)=
      put s1Reg (first n) (put c.mainIndex (second n) file) := by
    simp only [g,walkFile,show regValue file c.mainIndex=n from rfl,tsub_self,
      put_commute c.mainIndex s1Reg c.main_ne_s1,
      put_commute s2Reg c.mainIndex c.main_ne_s2.symm,
      put_commute s2Reg s1Reg (by decide),put_twice,hput2]
  refine ⟨(time+1)+(3*second n+1),?_,?_⟩
  · rw [show (time+1)+(3*second n+1)=((time+1)+3*second n)+1 by ring]
    exact le_add_of_nonneg_left (Arithmetic.zero_le _)
  · rw [controlRun_add (time+1) (3*second n+1) (liveValue (number c.readEntry : V) file),
      controlRun_succ time _,hreach]
    rw [←run_one (liveValue (number c.readEntry : V) g),hfirst,hp,hf]

end Model

private theorem literal_source (P Q : List Bool) (e : Edge)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0=some (e,Q.length))
    (hc : consume P Q.length=Q) : source (resolveControl P)=(Q,e) := by
  rw [resolve_source P e Q.length hw,hc]

def mpCoreIncS2 : Control := resolveControl (incPath (source mpPopEntry).1)
def mpCoreTestS1 : Control := resolveControl (incPath (source mpCoreIncS2).1)
def mpCoreBreak : Control := resolveControl (incPath (source mpCoreTestS1).1)
def mpCoreMoveTest : Control := resolveControl (breakPath 1 (source mpCoreTestS1).1)
def mpCoreMoveInc : Control := resolveControl (incPath (source mpCoreMoveTest).1)
def mpCoreMoveAgain : Control := resolveControl (incPath (source mpCoreMoveInc).1)
def mpCoreAgain : Control := resolveControl (breakPath 1 (source mpCoreBreak).1)
def mpCoreRestoreTest : Control := resolveControl (breakPath 1 (source mpPopEntry).1)
def mpCoreRestoreInc : Control := resolveControl (incPath (source mpCoreRestoreTest).1)
def mpCoreRestoreAgain : Control := resolveControl (incPath (source mpCoreRestoreInc).1)
def mpConstructorEntry : Control := resolveControl (breakPath 1 (source mpCoreRestoreTest).1)

theorem mpCoreIncS2_source : source mpCoreIncS2=([true,true,true,true,false,false,true,false,false,true,false],.inc 7) := by
  rw [mpCoreIncS2,mpPopEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCoreTestS1_source : source mpCoreTestS1=([true,true,true,true,false,false,true,false,false,true,true,false,false,false],.decnz 6) := by
  rw [mpCoreTestS1,mpCoreIncS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCoreBreak_source : source mpCoreBreak=([true,true,true,true,false,false,true,false,false,true,true,false,false,true],.brk 1) := by
  rw [mpCoreBreak,mpCoreTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCoreMoveTest_source : source mpCoreMoveTest=([true,true,true,true,false,false,true,false,false,true,true,false,true,false],.decnz 7) := by
  rw [mpCoreMoveTest,mpCoreTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCoreMoveInc_source : source mpCoreMoveInc=([true,true,true,true,false,false,true,false,false,true,true,false,true,true,false],.inc 6) := by
  rw [mpCoreMoveInc,mpCoreMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCoreMoveAgain_source : source mpCoreMoveAgain=([true,true,true,true,false,false,true,false,false,true,true,false,true,true,true],.cont 2) := by
  rw [mpCoreMoveAgain,mpCoreMoveInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCoreAgain_source : source mpCoreAgain=([true,true,true,true,false,false,true,false,false,true,true,true],.cont 3) := by
  rw [mpCoreAgain,mpCoreBreak_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCoreRestoreTest_source : source mpCoreRestoreTest=([true,true,true,true,false,false,true,false,true,false],.decnz 7) := by
  rw [mpCoreRestoreTest,mpPopEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCoreRestoreInc_source : source mpCoreRestoreInc=([true,true,true,true,false,false,true,false,true,true,false],.inc 2) := by
  rw [mpCoreRestoreInc,mpCoreRestoreTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpCoreRestoreAgain_source : source mpCoreRestoreAgain=([true,true,true,true,false,false,true,false,true,true,true],.cont 2) := by
  rw [mpCoreRestoreAgain,mpCoreRestoreInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpConstructorEntry_source : source mpConstructorEntry=([true,true,true,true,false,false,true,true,false,false,false],.decnz 1) := by
  rw [mpConstructorEntry,mpCoreRestoreTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

/-- The actual short WS unpair, whose exit is the constructor's `.decnz 1`.
No `.decnz 6` output-transfer field is required or silently supplied. -/
def mpCore : UnpairCoreShape where
  readEntry := mpPopEntry
  bodyIncS2 := mpCoreIncS2
  bodyTestS1 := mpCoreTestS1
  bodyBreak := mpCoreBreak
  bodyMoveTest := mpCoreMoveTest
  bodyMoveInc := mpCoreMoveInc
  bodyMoveContinue := mpCoreMoveAgain
  bodyContinue := mpCoreAgain
  restoreMainTest := mpCoreRestoreTest
  restoreMainInc := mpCoreRestoreInc
  restoreMainContinue := mpCoreRestoreAgain
  exit := mpConstructorEntry
  mainLogical := 2
  mainIndex := wsReg
  main_physical := rfl
  main_ne_s1 := by decide
  main_ne_s2 := by decide
  read_edge := congrArg Prod.snd mpPopEntry_source
  body_inc_edge := congrArg Prod.snd mpCoreIncS2_source
  body_test_edge := congrArg Prod.snd mpCoreTestS1_source
  body_break_edge := congrArg Prod.snd mpCoreBreak_source
  body_move_test_edge := congrArg Prod.snd mpCoreMoveTest_source
  body_move_inc_edge := congrArg Prod.snd mpCoreMoveInc_source
  body_move_continue_edge := congrArg Prod.snd mpCoreMoveAgain_source
  body_continue_edge := congrArg Prod.snd mpCoreAgain_source
  restore_test_edge := congrArg Prod.snd mpCoreRestoreTest_source
  restore_inc_edge := congrArg Prod.snd mpCoreRestoreInc_source
  restore_continue_edge := congrArg Prod.snd mpCoreRestoreAgain_source
  next_read_positive := by
    apply source_injective
    rw [mpPopEntry_source,mpCoreIncS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_read_zero := by
    apply source_injective
    rw [mpPopEntry_source,mpCoreRestoreTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_inc := by
    apply source_injective
    rw [mpCoreIncS2_source,mpCoreTestS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_test_positive := by
    apply source_injective
    rw [mpCoreTestS1_source,mpCoreBreak_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_test_zero := by
    apply source_injective
    rw [mpCoreTestS1_source,mpCoreMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_break := by
    apply source_injective
    rw [mpCoreBreak_source,mpCoreAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_move_positive := by
    apply source_injective
    rw [mpCoreMoveTest_source,mpCoreMoveInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_move_inc := by
    apply source_injective
    rw [mpCoreMoveInc_source,mpCoreMoveAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_move_continue := by
    apply source_injective
    rw [mpCoreMoveAgain_source,mpCoreMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_move_zero := by
    apply source_injective
    rw [mpCoreMoveTest_source,mpCoreAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_body_continue := by
    apply source_injective
    rw [mpCoreAgain_source,mpPopEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_restore_main_positive := by
    apply source_injective
    rw [mpCoreRestoreTest_source,mpCoreRestoreInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_restore_main_inc := by
    apply source_injective
    rw [mpCoreRestoreInc_source,mpCoreRestoreAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_restore_main_continue := by
    apply source_injective
    rw [mpCoreRestoreAgain_source,mpCoreRestoreTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  next_restore_main_zero := by
    apply source_injective
    rw [mpCoreRestoreTest_source,mpConstructorEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Actual MP unpair-to-scratch at controls 6393–6403, ending at 6404. -/
theorem mp_unpair_run (file : V) (h1 : regValue file s1Reg=0)
    (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpPopEntry : V) file)=
      liveValue (number mpConstructorEntry : V)
        (put s1Reg (first (regValue file wsReg)) (put wsReg (second (regValue file wsReg)) file)) := by
  simpa only [mpCore] using core_run mpCore file h1 h2

/-- File at the constructor after pushing TW and then unpairing that WS value. -/
def mpInitialFile (file : V) : V :=
  put s1Reg (regValue file twReg) (put twReg (regValue file p1Reg) file)

/-- The checked initial parameter push followed by the actual short unpair.
The original WS is recovered, TW holds param1, and scratch1 holds the old TW. -/
theorem mp_initial_pop_run (file : V) (h1 : regValue file s1Reg=0)
    (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpEntry : V) file)=
      liveValue (number mpConstructorEntry : V) (mpInitialFile file) := by
  obtain ⟨tp,_,hpush⟩ := mpParam_run file h1 h2
  let g := paramPushFile file
  have hg1 : regValue g s1Reg=0 := by
    dsimp only [g,paramPushFile]
    rw [read_put_other _ _ twReg s1Reg (by decide),
      read_put_other _ _ wsReg s1Reg (by decide)]
    exact h1
  have hg2 : regValue g s2Reg=0 := by
    dsimp only [g,paramPushFile]
    rw [read_put_other _ _ twReg s2Reg (by decide),
      read_put_other _ _ wsReg s2Reg (by decide)]
    exact h2
  have hgws : regValue g wsReg=cantor (regValue file twReg) (regValue file wsReg) := by
    dsimp only [g,paramPushFile]
    rw [read_put_other _ _ twReg wsReg (by decide),read_put_self]
  obtain ⟨tu,htu,hpop⟩ := mp_unpair_run g hg1 hg2
  rw [hgws,first_cantor,second_cantor] at hpop
  have hf : put s1Reg (regValue file twReg) (put wsReg (regValue file wsReg) g)=
      mpInitialFile file := by
    simp only [g,paramPushFile,mpInitialFile,
      put_commute wsReg twReg (by decide),put_twice,put_same]
  refine ⟨tp+tu,le_trans htu (le_add_of_nonneg_left (Arithmetic.zero_le tp)),?_⟩
  rw [controlRun_add,hpush,hpop,hf]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlUnpairCore254

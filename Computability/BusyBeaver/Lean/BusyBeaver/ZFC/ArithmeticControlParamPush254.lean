import BusyBeaver.ZFC.ArithmeticControlCompare254

set_option autoImplicit false
noncomputable section

/-!
The two actual MP parameter-push occurrences, with a reusable finite shape.
The checked Move/Copy/Pair contracts provide all unbounded runtime reasoning.
Both scratch-zero premises remain explicit; full MP is not asserted.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 (put s1Reg fetchTest fetchTest_source)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlReadTemplate254 (p1Reg)
open ArithmeticControlDispatch254 (mpEntry mpEntry_source cacheReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlPair254
open ArithmeticControlCompare254 (successEntry successEntry_source)
open FiniteControlTable254 RegisterPath

/-- A literal push occurrence: TW→scratch1, WS→TW, pairing, scratch2→WS. -/
structure PushShape where
  first : MoveShape
  second : MoveShape
  pairing : PairShape
  output : MoveShape
  first_source : first.sourceIndex=twReg
  first_target : first.targetIndex=s1Reg
  second_source : second.sourceIndex=wsReg
  second_target : second.targetIndex=twReg
  output_source : output.sourceIndex=s2Reg
  output_target : output.targetIndex=wsReg
  first_exit : first.exit=second.test
  second_exit : second.exit=pairing.copy.test
  pair_exit : pairing.exit=output.test

/-- Push followed by copying param1 into TW and scratch1, restoring param1. -/
structure ParamPushShape where
  push : PushShape
  copy : CopyShape
  restore : MoveShape
  copy_source : copy.sourceIndex=p1Reg
  copy_first : copy.firstIndex=twReg
  copy_second : copy.secondIndex=s1Reg
  restore_source : restore.sourceIndex=s1Reg
  restore_target : restore.targetIndex=p1Reg
  push_exit : push.output.exit=copy.test
  copy_exit : copy.exit=restore.test

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) : regValue (put p x file) p=x :=
  write_at file x p
private theorem read_put_other (file x : V) (p q : Fin 9) (h : p≠q) :
    regValue (put p x file) q=regValue file q := write_other file x p q h
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

private def prefixFile (file : V) : V :=
  put twReg (regValue file wsReg)
    (put wsReg 0 (put s1Reg (regValue file twReg) (put twReg 0 file)))
private theorem prefix_run (c : PushShape) (file : V) (h1 : regValue file s1Reg=0) :
    controlRun ((3*regValue file twReg+1)+(3*regValue file wsReg+1))
      (liveValue (number c.first.test : V) file)=
      liveValue (number c.pairing.copy.test : V) (prefixFile file) := by
  let g := put s1Reg (regValue file twReg) (put twReg 0 file)
  have hfirst : controlRun (3*regValue file twReg+1)
      (liveValue (number c.first.test : V) file)=
      liveValue (number c.second.test : V) g := by
    simpa only [c.first_source,c.first_target,c.first_exit,h1,zero_add,g] using move_run c.first file
  have hgws : regValue g wsReg=regValue file wsReg := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg wsReg (by decide),
      read_put_other _ _ twReg wsReg (by decide)]
  have hgtw : regValue g twReg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg twReg (by decide),read_put_self]
  have hsecond : controlRun (3*regValue file wsReg+1)
      (liveValue (number c.second.test : V) g)=
      liveValue (number c.pairing.copy.test : V) (prefixFile file) := by
    simpa only [c.second_source,c.second_target,c.second_exit,hgws,hgtw,zero_add,
      prefixFile,g] using move_run c.second g
  rw [controlRun_add,hfirst,hsecond]
private theorem prefix_s1 (file : V) : regValue (prefixFile file) s1Reg=regValue file twReg := by
  rw [prefixFile,read_put_other _ _ twReg s1Reg (by decide),
    read_put_other _ _ wsReg s1Reg (by decide),read_put_self]
private theorem prefix_tw (file : V) : regValue (prefixFile file) twReg=regValue file wsReg := by
  rw [prefixFile,read_put_self]
private theorem prefix_s2 (file : V) : regValue (prefixFile file) s2Reg=regValue file s2Reg := by
  rw [prefixFile,read_put_other _ _ twReg s2Reg (by decide),
    read_put_other _ _ wsReg s2Reg (by decide),
    read_put_other _ _ s1Reg s2Reg (by decide),
    read_put_other _ _ twReg s2Reg (by decide)]

/-- The clean push writes only TW and WS. -/
def pushFile (file : V) : V :=
  put wsReg (cantor (regValue file twReg) (regValue file wsReg)) (put twReg 0 file)

theorem push_run (c : PushShape) (file : V) (h1 : regValue file s1Reg=0)
    (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number c.first.test : V) file)=
      liveValue (number c.output.exit : V) (pushFile file) := by
  let p := cantor (regValue file twReg) (regValue file wsReg)
  let g := pairFile (prefixFile file) 0 0 p
  obtain ⟨tp,htp,hpair⟩ := pair_run c.pairing (prefixFile file)
  rw [prefix_s1,prefix_tw,prefix_s2,h2,zero_add,c.pair_exit] at hpair
  have hgs2 : regValue g s2Reg=p := by
    dsimp only [g,pairFile]
    rw [read_put_other _ _ s1Reg s2Reg (by decide),read_put_self]
  have hgws : regValue g wsReg=0 := by
    dsimp only [g,pairFile]
    rw [read_put_other _ _ s1Reg wsReg (by decide),
      read_put_other _ _ s2Reg wsReg (by decide),
      read_put_other _ _ twReg wsReg (by decide),prefixFile,
      read_put_other _ _ twReg wsReg (by decide),read_put_self]
  have hf : put wsReg p (put s2Reg 0 g)=pushFile file := by
    apply file_ext
    intro i
    have h1' : regValue file (8 : Fin 9)=0 := h1
    have h2' : regValue file (5 : Fin 9)=0 := h2
    by_cases hi0 : i=(0 : Fin 9)
    · subst i
      simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg]
    by_cases hi2 : i=(2 : Fin 9)
    · subst i
      simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg]
    by_cases hi5 : i=(5 : Fin 9)
    · subst i
      simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg,h2']
    by_cases hi8 : i=(8 : Fin 9)
    · subst i
      simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg,h1']
    simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg,
      Ne.symm hi0,Ne.symm hi2,Ne.symm hi5,Ne.symm hi8]
  have hpush : controlRun (3*p+1) (liveValue (number c.output.test : V) g)=
      liveValue (number c.output.exit : V) (pushFile file) := by
    simpa only [c.output_source,c.output_target,hgs2,hgws,zero_add,hf] using move_run c.output g
  let t0 := (3*regValue file twReg+1)+(3*regValue file wsReg+1)
  refine ⟨t0+(tp+(3*p+1)),?_,?_⟩
  · exact le_trans htp (le_trans
      (le_add_of_nonneg_right (Arithmetic.zero_le (3*p+1)))
      (le_add_of_nonneg_left (Arithmetic.zero_le t0)))
  · rw [controlRun_add t0 (tp+(3*p+1)),prefix_run c file h1,
      controlRun_add tp (3*p+1),hpair,hpush]

/-- Copy/restore adds param1 to TW in exactly 7*param1+2 steps. -/
theorem param_copy_run (c : ParamPushShape) (file : V) (h1 : regValue file s1Reg=0) :
    controlRun (7*regValue file p1Reg+2) (liveValue (number c.copy.test : V) file)=
      liveValue (number c.restore.exit : V)
        (put twReg (regValue file twReg+regValue file p1Reg) file) := by
  let h := regValue file p1Reg
  let g := put s1Reg h (put twReg (regValue file twReg+h) (put p1Reg 0 file))
  have hcopy : controlRun (4*h+1) (liveValue (number c.copy.test : V) file)=
      liveValue (number c.restore.test : V) g := by
    simpa only [c.copy_source,c.copy_first,c.copy_second,c.copy_exit,h1,zero_add,h,g] using copy_run c.copy file
  have hgs1 : regValue g s1Reg=h := by
    dsimp only [g]
    rw [read_put_self]
  have hgp : regValue g p1Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg p1Reg (by decide),
      read_put_other _ _ twReg p1Reg (by decide),read_put_self]
  have hf : put p1Reg h (put s1Reg 0 g)=
      put twReg (regValue file twReg+regValue file p1Reg) file := by
    apply file_ext
    intro i
    have h1' : regValue file (8 : Fin 9)=0 := h1
    by_cases hi2 : i=(2 : Fin 9)
    · subst i
      simp [read_put,g,h,twReg,p1Reg,s1Reg]
    by_cases hi3 : i=(3 : Fin 9)
    · subst i
      simp [read_put,g,h,twReg,p1Reg,s1Reg]
    by_cases hi8 : i=(8 : Fin 9)
    · subst i
      simp [read_put,g,h,twReg,p1Reg,s1Reg,h1']
    simp [read_put,g,h,twReg,p1Reg,s1Reg,Ne.symm hi2,Ne.symm hi3,Ne.symm hi8]
  have hrestore : controlRun (3*h+1) (liveValue (number c.restore.test : V) g)=
      liveValue (number c.restore.exit : V)
        (put twReg (regValue file twReg+regValue file p1Reg) file) := by
    simpa only [c.restore_source,c.restore_target,hgs1,hgp,zero_add,hf] using move_run c.restore g
  rw [show 7*regValue file p1Reg+2=(4*h+1)+(3*h+1) by dsimp only [h]; ring,
    controlRun_add,hcopy,hrestore]

/-- The completed parameter push changes only TW and WS, preserving param1. -/
def paramPushFile (file : V) : V :=
  put twReg (regValue file p1Reg)
    (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)

theorem param_push_run (c : ParamPushShape) (file : V)
    (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number c.push.first.test : V) file)=
      liveValue (number c.restore.exit : V) (paramPushFile file) := by
  let g := pushFile file
  have hg1 : regValue g s1Reg=0 := by
    dsimp only [g,pushFile]
    rw [read_put_other _ _ wsReg s1Reg (by decide),
      read_put_other _ _ twReg s1Reg (by decide)]
    exact h1
  have hgtw : regValue g twReg=0 := by
    dsimp only [g,pushFile]
    rw [read_put_other _ _ wsReg twReg (by decide),read_put_self]
  have hgp : regValue g p1Reg=regValue file p1Reg := by
    dsimp only [g,pushFile]
    rw [read_put_other _ _ wsReg p1Reg (by decide),
      read_put_other _ _ twReg p1Reg (by decide)]
  have hf : put twReg (regValue g twReg+regValue g p1Reg) g=paramPushFile file := by
    rw [hgtw,hgp,zero_add]
    apply file_ext
    intro i
    by_cases hi0 : i=(0 : Fin 9)
    · subst i
      simp [read_put,g,pushFile,paramPushFile,twReg,wsReg,p1Reg]
    by_cases hi2 : i=(2 : Fin 9)
    · subst i
      simp [read_put,g,pushFile,paramPushFile,twReg,wsReg,p1Reg]
    simp [read_put,g,pushFile,paramPushFile,twReg,wsReg,p1Reg,Ne.symm hi0,Ne.symm hi2]
  obtain ⟨tp,htp,hpush⟩ := push_run c.push file h1 h2
  rw [c.push_exit] at hpush
  have hcopy := param_copy_run c g hg1
  rw [hf,hgp] at hcopy
  refine ⟨tp+(7*regValue file p1Reg+2),
    le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)),?_⟩
  rw [controlRun_add,hpush,hcopy]

end Model

private theorem literal_source (P Q : List Bool) (e : Edge)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0=some (e,Q.length))
    (hc : consume P Q.length=Q) : source (resolveControl P)=(Q,e) := by
  rw [resolve_source P e Q.length hw,hc]
def mpParamTWInc : Control := resolveControl (incPath (source mpEntry).1)
def mpParamTWAgain : Control := resolveControl (incPath (source mpParamTWInc).1)
def mpParamWSTest : Control := resolveControl (breakPath 1 (source mpEntry).1)
def mpParamWSInc : Control := resolveControl (incPath (source mpParamWSTest).1)
def mpParamWSAgain : Control := resolveControl (incPath (source mpParamWSInc).1)
def mpParamOutInc : Control := resolveControl (incPath (source mpPairExit).1)
def mpParamOutAgain : Control := resolveControl (incPath (source mpParamOutInc).1)
def mpParamCopyTest : Control := resolveControl (breakPath 1 (source mpPairExit).1)
def mpParamCopyTW : Control := resolveControl (incPath (source mpParamCopyTest).1)
def mpParamCopyS1 : Control := resolveControl (incPath (source mpParamCopyTW).1)
def mpParamCopyAgain : Control := resolveControl (incPath (source mpParamCopyS1).1)
def mpParamRestoreTest : Control := resolveControl (breakPath 1 (source mpParamCopyTest).1)
def mpParamRestoreInc : Control := resolveControl (incPath (source mpParamRestoreTest).1)
def mpParamRestoreAgain : Control := resolveControl (incPath (source mpParamRestoreInc).1)
def mpPopEntry : Control := resolveControl (breakPath 1 (source mpParamRestoreTest).1)

theorem mpParamTWInc_source : source mpParamTWInc=([true,true,true,true,false,false,false,false,false,true,false],.inc 6) := by
  rw [mpParamTWInc,mpEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamTWAgain_source : source mpParamTWAgain=([true,true,true,true,false,false,false,false,false,true,true],.cont 2) := by
  rw [mpParamTWAgain,mpParamTWInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamWSTest_source : source mpParamWSTest=([true,true,true,true,false,false,false,false,true,false,false],.decnz 2) := by
  rw [mpParamWSTest,mpEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamWSInc_source : source mpParamWSInc=([true,true,true,true,false,false,false,false,true,false,true,false],.inc 1) := by
  rw [mpParamWSInc,mpParamWSTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamWSAgain_source : source mpParamWSAgain=([true,true,true,true,false,false,false,false,true,false,true,true],.cont 2) := by
  rw [mpParamWSAgain,mpParamWSInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamOutInc_source : source mpParamOutInc=([true,true,true,true,false,false,false,false,true,true,true,true,false],.inc 2) := by
  rw [mpParamOutInc,mpPairExit_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamOutAgain_source : source mpParamOutAgain=([true,true,true,true,false,false,false,false,true,true,true,true,true],.cont 2) := by
  rw [mpParamOutAgain,mpParamOutInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamCopyTest_source : source mpParamCopyTest=([true,true,true,true,false,false,false,true,false,false],.decnz 4) := by
  rw [mpParamCopyTest,mpPairExit_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamCopyTW_source : source mpParamCopyTW=([true,true,true,true,false,false,false,true,false,true,false],.inc 1) := by
  rw [mpParamCopyTW,mpParamCopyTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamCopyS1_source : source mpParamCopyS1=([true,true,true,true,false,false,false,true,false,true,true,false],.inc 6) := by
  rw [mpParamCopyS1,mpParamCopyTW_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamCopyAgain_source : source mpParamCopyAgain=([true,true,true,true,false,false,false,true,false,true,true,true],.cont 3) := by
  rw [mpParamCopyAgain,mpParamCopyS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamRestoreTest_source : source mpParamRestoreTest=([true,true,true,true,false,false,false,true,true,false],.decnz 6) := by
  rw [mpParamRestoreTest,mpParamCopyTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamRestoreInc_source : source mpParamRestoreInc=([true,true,true,true,false,false,false,true,true,true,false],.inc 4) := by
  rw [mpParamRestoreInc,mpParamRestoreTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpParamRestoreAgain_source : source mpParamRestoreAgain=([true,true,true,true,false,false,false,true,true,true,true],.cont 2) := by
  rw [mpParamRestoreAgain,mpParamRestoreInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem mpPopEntry_source : source mpPopEntry=([true,true,true,true,false,false,true,false,false,false],.decnz 2) := by
  rw [mpPopEntry,mpParamRestoreTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

def mpParamTW : MoveShape where
  test := mpEntry
  increment := mpParamTWInc
  again := mpParamTWAgain
  exit := mpParamWSTest
  sourceLogical := 1
  targetLogical := 6
  sourceIndex := twReg
  targetIndex := s1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd mpEntry_source
  increment_edge := congrArg Prod.snd mpParamTWInc_source
  again_edge := congrArg Prod.snd mpParamTWAgain_source
  positive_target := by
    apply source_injective
    rw [mpEntry_source,mpParamTWInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [mpParamTWInc_source,mpParamTWAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpParamTWAgain_source,mpEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpEntry_source,mpParamWSTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpParamWS : MoveShape where
  test := mpParamWSTest
  increment := mpParamWSInc
  again := mpParamWSAgain
  exit := mpPairTest
  sourceLogical := 2
  targetLogical := 1
  sourceIndex := wsReg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd mpParamWSTest_source
  increment_edge := congrArg Prod.snd mpParamWSInc_source
  again_edge := congrArg Prod.snd mpParamWSAgain_source
  positive_target := by
    apply source_injective
    rw [mpParamWSTest_source,mpParamWSInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [mpParamWSInc_source,mpParamWSAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpParamWSAgain_source,mpParamWSTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpParamWSTest_source,mpPairTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpParamOutput : MoveShape where
  test := mpPairExit
  increment := mpParamOutInc
  again := mpParamOutAgain
  exit := mpParamCopyTest
  sourceLogical := 7
  targetLogical := 2
  sourceIndex := s2Reg
  targetIndex := wsReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd mpPairExit_source
  increment_edge := congrArg Prod.snd mpParamOutInc_source
  again_edge := congrArg Prod.snd mpParamOutAgain_source
  positive_target := by
    apply source_injective
    rw [mpPairExit_source,mpParamOutInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [mpParamOutInc_source,mpParamOutAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpParamOutAgain_source,mpPairExit_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpPairExit_source,mpParamCopyTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpParamCopy : CopyShape where
  test := mpParamCopyTest
  firstInc := mpParamCopyTW
  secondInc := mpParamCopyS1
  again := mpParamCopyAgain
  exit := mpParamRestoreTest
  sourceLogical := 4
  firstLogical := 1
  secondLogical := 6
  sourceIndex := p1Reg
  firstIndex := twReg
  secondIndex := s1Reg
  source_physical := rfl
  first_physical := rfl
  second_physical := rfl
  source_ne_first := by decide
  source_ne_second := by decide
  first_ne_second := by decide
  test_edge := congrArg Prod.snd mpParamCopyTest_source
  first_edge := congrArg Prod.snd mpParamCopyTW_source
  second_edge := congrArg Prod.snd mpParamCopyS1_source
  again_edge := congrArg Prod.snd mpParamCopyAgain_source
  positive_target := by
    apply source_injective
    rw [mpParamCopyTest_source,mpParamCopyTW_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  first_target := by
    apply source_injective
    rw [mpParamCopyTW_source,mpParamCopyS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  second_target := by
    apply source_injective
    rw [mpParamCopyS1_source,mpParamCopyAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpParamCopyAgain_source,mpParamCopyTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpParamCopyTest_source,mpParamRestoreTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpParamRestore : MoveShape where
  test := mpParamRestoreTest
  increment := mpParamRestoreInc
  again := mpParamRestoreAgain
  exit := mpPopEntry
  sourceLogical := 6
  targetLogical := 4
  sourceIndex := s1Reg
  targetIndex := p1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd mpParamRestoreTest_source
  increment_edge := congrArg Prod.snd mpParamRestoreInc_source
  again_edge := congrArg Prod.snd mpParamRestoreAgain_source
  positive_target := by
    apply source_injective
    rw [mpParamRestoreTest_source,mpParamRestoreInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [mpParamRestoreInc_source,mpParamRestoreAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [mpParamRestoreAgain_source,mpParamRestoreTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [mpParamRestoreTest_source,mpPopEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def mpParamPush : PushShape where
  first := mpParamTW
  second := mpParamWS
  pairing := mpPair
  output := mpParamOutput
  first_source := rfl
  first_target := rfl
  second_source := rfl
  second_target := rfl
  output_source := rfl
  output_target := rfl
  first_exit := by simp only [mpParamTW,mpParamWS]
  second_exit := by simp only [mpParamWS,mpPair,mpCopy]
  pair_exit := by simp only [mpPair,mpParamOutput]

def mpParam : ParamPushShape where
  push := mpParamPush
  copy := mpParamCopy
  restore := mpParamRestore
  copy_source := rfl
  copy_first := rfl
  copy_second := rfl
  restore_source := rfl
  restore_target := rfl
  push_exit := by simp only [mpParamPush,mpParamOutput,mpParamCopy]
  copy_exit := by simp only [mpParamCopy,mpParamRestore]

/-- Actual initial MP parameter push, stopping before WS unpairing. -/
theorem mpParam_run {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (file : V)
    (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number mpEntry : V) file)=
      liveValue (number mpPopEntry : V) (paramPushFile file) := by
  simpa only [mpParam,mpParamPush,mpParamTW,mpParamRestore] using param_push_run mpParam file h1 h2
def successParamTWInc : Control := resolveControl (incPath (source successEntry).1)
def successParamTWAgain : Control := resolveControl (incPath (source successParamTWInc).1)
def successParamWSTest : Control := resolveControl (breakPath 1 (source successEntry).1)
def successParamWSInc : Control := resolveControl (incPath (source successParamWSTest).1)
def successParamWSAgain : Control := resolveControl (incPath (source successParamWSInc).1)
def successPairTest : Control := resolveControl (breakPath 1 (source successParamWSTest).1)
def successPairCopyS2 : Control := resolveControl (incPath (source successPairTest).1)
def successPairCopyS1 : Control := resolveControl (incPath (source successPairCopyS2).1)
def successPairCopyAgain : Control := resolveControl (incPath (source successPairCopyS1).1)
def successPairTestS1 : Control := resolveControl (breakPath 1 (source successPairTest).1)
def successPairIncS2 : Control := resolveControl (incPath (source successPairTestS1).1)
def successPairMoveTest : Control := resolveControl (incPath (source successPairIncS2).1)
def successPairMoveInc : Control := resolveControl (incPath (source successPairMoveTest).1)
def successPairMoveAgain : Control := resolveControl (incPath (source successPairMoveInc).1)
def successPairAgain : Control := resolveControl (breakPath 1 (source successPairMoveTest).1)
def successPairExit : Control := resolveControl (breakPath 1 (source successPairTestS1).1)
def successParamOutInc : Control := resolveControl (incPath (source successPairExit).1)
def successParamOutAgain : Control := resolveControl (incPath (source successParamOutInc).1)
def successParamCopyTest : Control := resolveControl (breakPath 1 (source successPairExit).1)
def successParamCopyTW : Control := resolveControl (incPath (source successParamCopyTest).1)
def successParamCopyS1 : Control := resolveControl (incPath (source successParamCopyTW).1)
def successParamCopyAgain : Control := resolveControl (incPath (source successParamCopyS1).1)
def successParamRestoreTest : Control := resolveControl (breakPath 1 (source successParamCopyTest).1)
def successParamRestoreInc : Control := resolveControl (incPath (source successParamRestoreTest).1)
def successParamRestoreAgain : Control := resolveControl (incPath (source successParamRestoreInc).1)

theorem successParamTWInc_source : source successParamTWInc=([true,true,true,true,true,true,false,false,true,false],.inc 6) := by
  rw [successParamTWInc,successEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamTWAgain_source : source successParamTWAgain=([true,true,true,true,true,true,false,false,true,true],.cont 2) := by
  rw [successParamTWAgain,successParamTWInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamWSTest_source : source successParamWSTest=([true,true,true,true,true,true,false,true,false,false],.decnz 2) := by
  rw [successParamWSTest,successEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamWSInc_source : source successParamWSInc=([true,true,true,true,true,true,false,true,false,true,false],.inc 1) := by
  rw [successParamWSInc,successParamWSTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamWSAgain_source : source successParamWSAgain=([true,true,true,true,true,true,false,true,false,true,true],.cont 2) := by
  rw [successParamWSAgain,successParamWSInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairTest_source : source successPairTest=([true,true,true,true,true,true,false,true,true,false,false,false],.decnz 1) := by
  rw [successPairTest,successParamWSTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairCopyS2_source : source successPairCopyS2=([true,true,true,true,true,true,false,true,true,false,false,true,false],.inc 7) := by
  rw [successPairCopyS2,successPairTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairCopyS1_source : source successPairCopyS1=([true,true,true,true,true,true,false,true,true,false,false,true,true,false],.inc 6) := by
  rw [successPairCopyS1,successPairCopyS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairCopyAgain_source : source successPairCopyAgain=([true,true,true,true,true,true,false,true,true,false,false,true,true,true],.cont 3) := by
  rw [successPairCopyAgain,successPairCopyS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairTestS1_source : source successPairTestS1=([true,true,true,true,true,true,false,true,true,false,true,false],.decnz 6) := by
  rw [successPairTestS1,successPairTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairIncS2_source : source successPairIncS2=([true,true,true,true,true,true,false,true,true,false,true,true,false,false],.inc 7) := by
  rw [successPairIncS2,successPairTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairMoveTest_source : source successPairMoveTest=([true,true,true,true,true,true,false,true,true,false,true,true,false,true,false],.decnz 6) := by
  rw [successPairMoveTest,successPairIncS2_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairMoveInc_source : source successPairMoveInc=([true,true,true,true,true,true,false,true,true,false,true,true,false,true,true,false],.inc 1) := by
  rw [successPairMoveInc,successPairMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairMoveAgain_source : source successPairMoveAgain=([true,true,true,true,true,true,false,true,true,false,true,true,false,true,true,true],.cont 2) := by
  rw [successPairMoveAgain,successPairMoveInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairAgain_source : source successPairAgain=([true,true,true,true,true,true,false,true,true,false,true,true,true],.cont 3) := by
  rw [successPairAgain,successPairMoveTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successPairExit_source : source successPairExit=([true,true,true,true,true,true,false,true,true,true,false],.decnz 7) := by
  rw [successPairExit,successPairTestS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamOutInc_source : source successParamOutInc=([true,true,true,true,true,true,false,true,true,true,true,false],.inc 2) := by
  rw [successParamOutInc,successPairExit_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamOutAgain_source : source successParamOutAgain=([true,true,true,true,true,true,false,true,true,true,true,true],.cont 2) := by
  rw [successParamOutAgain,successParamOutInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamCopyTest_source : source successParamCopyTest=([true,true,true,true,true,true,true,false,false],.decnz 4) := by
  rw [successParamCopyTest,successPairExit_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamCopyTW_source : source successParamCopyTW=([true,true,true,true,true,true,true,false,true,false],.inc 1) := by
  rw [successParamCopyTW,successParamCopyTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamCopyS1_source : source successParamCopyS1=([true,true,true,true,true,true,true,false,true,true,false],.inc 6) := by
  rw [successParamCopyS1,successParamCopyTW_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamCopyAgain_source : source successParamCopyAgain=([true,true,true,true,true,true,true,false,true,true,true],.cont 3) := by
  rw [successParamCopyAgain,successParamCopyS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamRestoreTest_source : source successParamRestoreTest=([true,true,true,true,true,true,true,true,false],.decnz 6) := by
  rw [successParamRestoreTest,successParamCopyTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamRestoreInc_source : source successParamRestoreInc=([true,true,true,true,true,true,true,true,true,false],.inc 4) := by
  rw [successParamRestoreInc,successParamRestoreTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successParamRestoreAgain_source : source successParamRestoreAgain=([true,true,true,true,true,true,true,true,true,true],.cont 2) := by
  rw [successParamRestoreAgain,successParamRestoreInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

def successPairCopy : CopyShape where
  test := successPairTest
  firstInc := successPairCopyS2
  secondInc := successPairCopyS1
  again := successPairCopyAgain
  exit := successPairTestS1
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
  test_edge := congrArg Prod.snd successPairTest_source
  first_edge := congrArg Prod.snd successPairCopyS2_source
  second_edge := congrArg Prod.snd successPairCopyS1_source
  again_edge := congrArg Prod.snd successPairCopyAgain_source
  positive_target := by
    apply source_injective
    rw [successPairTest_source,successPairCopyS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  first_target := by
    apply source_injective
    rw [successPairCopyS2_source,successPairCopyS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  second_target := by
    apply source_injective
    rw [successPairCopyS1_source,successPairCopyAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [successPairCopyAgain_source,successPairTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [successPairTest_source,successPairTestS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def successPairMove : MoveShape where
  test := successPairMoveTest
  increment := successPairMoveInc
  again := successPairMoveAgain
  exit := successPairAgain
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd successPairMoveTest_source
  increment_edge := congrArg Prod.snd successPairMoveInc_source
  again_edge := congrArg Prod.snd successPairMoveAgain_source
  positive_target := by
    apply source_injective
    rw [successPairMoveTest_source,successPairMoveInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [successPairMoveInc_source,successPairMoveAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [successPairMoveAgain_source,successPairMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [successPairMoveTest_source,successPairAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def successPair : PairShape where
  copy := successPairCopy
  testS1 := successPairTestS1
  incS2 := successPairIncS2
  move := successPairMove
  again := successPairAgain
  exit := successPairExit
  copy_source := rfl
  copy_first := rfl
  copy_second := rfl
  copy_exit := by simp only [successPairCopy]
  move_source := rfl
  move_target := rfl
  move_exit := by simp only [successPairMove]
  test_edge := congrArg Prod.snd successPairTestS1_source
  increment_edge := congrArg Prod.snd successPairIncS2_source
  again_edge := congrArg Prod.snd successPairAgain_source
  positive_target := by
    apply source_injective
    rw [successPairTestS1_source,successPairIncS2_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [successPairTestS1_source,successPairExit_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    dsimp only [successPairMove]
    apply source_injective
    rw [successPairIncS2_source,successPairMoveTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    dsimp only [successPairCopy]
    apply source_injective
    rw [successPairAgain_source,successPairTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def successParamTW : MoveShape where
  test := successEntry
  increment := successParamTWInc
  again := successParamTWAgain
  exit := successParamWSTest
  sourceLogical := 1
  targetLogical := 6
  sourceIndex := twReg
  targetIndex := s1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd successEntry_source
  increment_edge := congrArg Prod.snd successParamTWInc_source
  again_edge := congrArg Prod.snd successParamTWAgain_source
  positive_target := by
    apply source_injective
    rw [successEntry_source,successParamTWInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [successParamTWInc_source,successParamTWAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [successParamTWAgain_source,successEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [successEntry_source,successParamWSTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def successParamWS : MoveShape where
  test := successParamWSTest
  increment := successParamWSInc
  again := successParamWSAgain
  exit := successPairTest
  sourceLogical := 2
  targetLogical := 1
  sourceIndex := wsReg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd successParamWSTest_source
  increment_edge := congrArg Prod.snd successParamWSInc_source
  again_edge := congrArg Prod.snd successParamWSAgain_source
  positive_target := by
    apply source_injective
    rw [successParamWSTest_source,successParamWSInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [successParamWSInc_source,successParamWSAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [successParamWSAgain_source,successParamWSTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [successParamWSTest_source,successPairTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def successParamOutput : MoveShape where
  test := successPairExit
  increment := successParamOutInc
  again := successParamOutAgain
  exit := successParamCopyTest
  sourceLogical := 7
  targetLogical := 2
  sourceIndex := s2Reg
  targetIndex := wsReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd successPairExit_source
  increment_edge := congrArg Prod.snd successParamOutInc_source
  again_edge := congrArg Prod.snd successParamOutAgain_source
  positive_target := by
    apply source_injective
    rw [successPairExit_source,successParamOutInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [successParamOutInc_source,successParamOutAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [successParamOutAgain_source,successPairExit_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [successPairExit_source,successParamCopyTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def successParamCopy : CopyShape where
  test := successParamCopyTest
  firstInc := successParamCopyTW
  secondInc := successParamCopyS1
  again := successParamCopyAgain
  exit := successParamRestoreTest
  sourceLogical := 4
  firstLogical := 1
  secondLogical := 6
  sourceIndex := p1Reg
  firstIndex := twReg
  secondIndex := s1Reg
  source_physical := rfl
  first_physical := rfl
  second_physical := rfl
  source_ne_first := by decide
  source_ne_second := by decide
  first_ne_second := by decide
  test_edge := congrArg Prod.snd successParamCopyTest_source
  first_edge := congrArg Prod.snd successParamCopyTW_source
  second_edge := congrArg Prod.snd successParamCopyS1_source
  again_edge := congrArg Prod.snd successParamCopyAgain_source
  positive_target := by
    apply source_injective
    rw [successParamCopyTest_source,successParamCopyTW_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  first_target := by
    apply source_injective
    rw [successParamCopyTW_source,successParamCopyS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  second_target := by
    apply source_injective
    rw [successParamCopyS1_source,successParamCopyAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [successParamCopyAgain_source,successParamCopyTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [successParamCopyTest_source,successParamRestoreTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def successParamRestore : MoveShape where
  test := successParamRestoreTest
  increment := successParamRestoreInc
  again := successParamRestoreAgain
  exit := fetchTest
  sourceLogical := 6
  targetLogical := 4
  sourceIndex := s1Reg
  targetIndex := p1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd successParamRestoreTest_source
  increment_edge := congrArg Prod.snd successParamRestoreInc_source
  again_edge := congrArg Prod.snd successParamRestoreAgain_source
  positive_target := by
    apply source_injective
    rw [successParamRestoreTest_source,successParamRestoreInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [successParamRestoreInc_source,successParamRestoreAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [successParamRestoreAgain_source,successParamRestoreTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [successParamRestoreTest_source,fetchTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def successParamPush : PushShape where
  first := successParamTW
  second := successParamWS
  pairing := successPair
  output := successParamOutput
  first_source := rfl
  first_target := rfl
  second_source := rfl
  second_target := rfl
  output_source := rfl
  output_target := rfl
  first_exit := by simp only [successParamTW,successParamWS]
  second_exit := by simp only [successParamWS,successPair,successPairCopy]
  pair_exit := by simp only [successPair,successParamOutput]

def successParam : ParamPushShape where
  push := successParamPush
  copy := successParamCopy
  restore := successParamRestore
  copy_source := rfl
  copy_first := rfl
  copy_second := rfl
  restore_source := rfl
  restore_target := rfl
  push_exit := by simp only [successParamPush,successParamOutput,successParamCopy]
  copy_exit := by simp only [successParamCopy,successParamRestore]

/-- Actual MP success parameter push, returning directly to fetch. -/
theorem successParam_run {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (file : V)
    (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number successEntry : V) file)=
      liveValue (number fetchTest : V) (paramPushFile file) := by
  simpa only [successParam,successParamPush,successParamTW,successParamRestore] using param_push_run successParam file h1 h2

section Tail
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The whole actual MP tail, from destructive comparison through the success
push when equality holds. Only scratch2 must initially be zero; comparison
itself clears scratch1 and cache before entering the success block. -/
theorem mp_compare_tail_run (file : V) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number ArithmeticControlCompare254.compareEntry : V) file)=
      if regValue file s1Reg=regValue file cacheReg then
        liveValue (number fetchTest : V)
          (paramPushFile (ArithmeticControlCompare254.compareFile file 0 0))
      else liveValue (number fetchTest : V)
        (ArithmeticControlCompare254.compareFile file 0 0) := by
  let g := ArithmeticControlCompare254.compareFile file 0 0
  obtain ⟨tc,htc,hcompare⟩ := ArithmeticControlCompare254.compare_terminates file
  by_cases he : regValue file s1Reg=regValue file cacheReg
  · rw [if_pos he] at hcompare
    have hg1 : regValue g s1Reg=0 := by
      dsimp only [g,ArithmeticControlCompare254.compareFile]
      rw [read_put_other _ _ cacheReg s1Reg (by decide),read_put_self]
    have hg2 : regValue g s2Reg=0 := by
      dsimp only [g,ArithmeticControlCompare254.compareFile]
      rw [read_put_other _ _ cacheReg s2Reg (by decide),
        read_put_other _ _ s1Reg s2Reg (by decide)]
      exact h2
    obtain ⟨tp,htp,hpush⟩ := successParam_run g hg1 hg2
    refine ⟨tc+tp,le_trans htc (le_add_of_nonneg_right (Arithmetic.zero_le _)),?_⟩
    rw [if_pos he,controlRun_add,hcompare,hpush]
  · rw [if_neg he] at hcompare
    refine ⟨tc,htc,?_⟩
    rw [if_neg he]
    exact hcompare

end Tail

end SetTheory.BusyBeaver.ZFC.ArithmeticControlParamPush254

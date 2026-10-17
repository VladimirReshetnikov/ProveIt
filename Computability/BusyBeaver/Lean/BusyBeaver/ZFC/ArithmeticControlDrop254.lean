import BusyBeaver.ZFC.ArithmeticControlPair254

set_option autoImplicit false
noncomputable section

/-!
The complete actual DROP instruction in every internal IΣ₁ model. The two
scratch-zero premises are explicit. All finite controls are tied to the
current Prog254 source; the only unbounded helpers are the checked Move,
Copy, and Pair contracts. This does not assert full L2/Enum equivalence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 (put s1Reg fetchTest fetchTest_source)
open ArithmeticControlRead254 (s2Reg acReg)
open ArithmeticControlDispatch254
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlPair254
open FiniteControlTable254 RegisterPath

private theorem literal_source (P Q : List Bool) (e : Edge)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0=some (e,Q.length))
    (hc : consume P Q.length=Q) : source (resolveControl P)=(Q,e) := by
  rw [resolve_source P e Q.length hw,hc]

def prefixTWInc : Control := resolveControl (incPath (source dropEntry).1)
def prefixTWAgain : Control := resolveControl (incPath (source prefixTWInc).1)
def prefixWSTest : Control := resolveControl (breakPath 1 (source dropEntry).1)
def prefixWSInc : Control := resolveControl (incPath (source prefixWSTest).1)
def prefixWSAgain : Control := resolveControl (incPath (source prefixWSInc).1)
def pushWSInc : Control := resolveControl (incPath (source dropPairExit).1)
def pushWSAgain : Control := resolveControl (incPath (source pushWSInc).1)
def cacheCopyTest : Control := resolveControl (breakPath 1 (source dropPairExit).1)
def cacheCopyTW : Control := resolveControl (incPath (source cacheCopyTest).1)
def cacheCopyS1 : Control := resolveControl (incPath (source cacheCopyTW).1)
def cacheCopyAgain : Control := resolveControl (incPath (source cacheCopyS1).1)
def cacheRestoreTest : Control := resolveControl (breakPath 1 (source cacheCopyTest).1)
def cacheRestoreInc : Control := resolveControl (incPath (source cacheRestoreTest).1)
def cacheRestoreAgain : Control := resolveControl (incPath (source cacheRestoreInc).1)
def dropReturn : Control := resolveControl (breakPath 1 (source cacheRestoreTest).1)

theorem prefixTWInc_source : source prefixTWInc=([true,true,true,false,true,false,true,false,false,true,false],.inc 6) := by
  rw [prefixTWInc,dropEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem prefixTWAgain_source : source prefixTWAgain=([true,true,true,false,true,false,true,false,false,true,true],.cont 2) := by
  rw [prefixTWAgain,prefixTWInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem prefixWSTest_source : source prefixWSTest=([true,true,true,false,true,false,true,false,true,false,false],.decnz 2) := by
  rw [prefixWSTest,dropEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem prefixWSInc_source : source prefixWSInc=([true,true,true,false,true,false,true,false,true,false,true,false],.inc 1) := by
  rw [prefixWSInc,prefixWSTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem prefixWSAgain_source : source prefixWSAgain=([true,true,true,false,true,false,true,false,true,false,true,true],.cont 2) := by
  rw [prefixWSAgain,prefixWSInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem pushWSInc_source : source pushWSInc=([true,true,true,false,true,false,true,false,true,true,true,true,false],.inc 2) := by
  rw [pushWSInc,dropPairExit_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem pushWSAgain_source : source pushWSAgain=([true,true,true,false,true,false,true,false,true,true,true,true,true],.cont 2) := by
  rw [pushWSAgain,pushWSInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem cacheCopyTest_source : source cacheCopyTest=([true,true,true,false,true,false,true,true,false,false],.decnz 5) := by
  rw [cacheCopyTest,dropPairExit_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem cacheCopyTW_source : source cacheCopyTW=([true,true,true,false,true,false,true,true,false,true,false],.inc 1) := by
  rw [cacheCopyTW,cacheCopyTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem cacheCopyS1_source : source cacheCopyS1=([true,true,true,false,true,false,true,true,false,true,true,false],.inc 6) := by
  rw [cacheCopyS1,cacheCopyTW_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem cacheCopyAgain_source : source cacheCopyAgain=([true,true,true,false,true,false,true,true,false,true,true,true],.cont 3) := by
  rw [cacheCopyAgain,cacheCopyS1_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem cacheRestoreTest_source : source cacheRestoreTest=([true,true,true,false,true,false,true,true,true,false],.decnz 6) := by
  rw [cacheRestoreTest,cacheCopyTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem cacheRestoreInc_source : source cacheRestoreInc=([true,true,true,false,true,false,true,true,true,true,false],.inc 5) := by
  rw [cacheRestoreInc,cacheRestoreTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem cacheRestoreAgain_source : source cacheRestoreAgain=([true,true,true,false,true,false,true,true,true,true,true],.cont 2) := by
  rw [cacheRestoreAgain,cacheRestoreInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem dropReturn_source : source dropReturn=([true,true,true,false,true,true],.brk 1) := by
  rw [dropReturn,cacheRestoreTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

def prefixTW : MoveShape where
  test := dropEntry
  increment := prefixTWInc
  again := prefixTWAgain
  exit := prefixWSTest
  sourceLogical := 1
  targetLogical := 6
  sourceIndex := twReg
  targetIndex := s1Reg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd dropEntry_source
  increment_edge := congrArg Prod.snd prefixTWInc_source
  again_edge := congrArg Prod.snd prefixTWAgain_source
  positive_target := by
    apply source_injective
    rw [dropEntry_source,prefixTWInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [prefixTWInc_source,prefixTWAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [prefixTWAgain_source,dropEntry_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [dropEntry_source,prefixWSTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def prefixWS : MoveShape where
  test := prefixWSTest
  increment := prefixWSInc
  again := prefixWSAgain
  exit := dropPairTest
  sourceLogical := 2
  targetLogical := 1
  sourceIndex := wsReg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd prefixWSTest_source
  increment_edge := congrArg Prod.snd prefixWSInc_source
  again_edge := congrArg Prod.snd prefixWSAgain_source
  positive_target := by
    apply source_injective
    rw [prefixWSTest_source,prefixWSInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [prefixWSInc_source,prefixWSAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [prefixWSAgain_source,prefixWSTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [prefixWSTest_source,dropPairTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def pushWS : MoveShape where
  test := dropPairExit
  increment := pushWSInc
  again := pushWSAgain
  exit := cacheCopyTest
  sourceLogical := 7
  targetLogical := 2
  sourceIndex := s2Reg
  targetIndex := wsReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd dropPairExit_source
  increment_edge := congrArg Prod.snd pushWSInc_source
  again_edge := congrArg Prod.snd pushWSAgain_source
  positive_target := by
    apply source_injective
    rw [dropPairExit_source,pushWSInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [pushWSInc_source,pushWSAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [pushWSAgain_source,dropPairExit_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [dropPairExit_source,cacheCopyTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def cacheRestore : MoveShape where
  test := cacheRestoreTest
  increment := cacheRestoreInc
  again := cacheRestoreAgain
  exit := dropReturn
  sourceLogical := 6
  targetLogical := 5
  sourceIndex := s1Reg
  targetIndex := cacheReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd cacheRestoreTest_source
  increment_edge := congrArg Prod.snd cacheRestoreInc_source
  again_edge := congrArg Prod.snd cacheRestoreAgain_source
  positive_target := by
    apply source_injective
    rw [cacheRestoreTest_source,cacheRestoreInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [cacheRestoreInc_source,cacheRestoreAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [cacheRestoreAgain_source,cacheRestoreTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [cacheRestoreTest_source,dropReturn_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

def cacheCopy : CopyShape where
  test := cacheCopyTest
  firstInc := cacheCopyTW
  secondInc := cacheCopyS1
  again := cacheCopyAgain
  exit := cacheRestoreTest
  sourceLogical := 5
  firstLogical := 1
  secondLogical := 6
  sourceIndex := cacheReg
  firstIndex := twReg
  secondIndex := s1Reg
  source_physical := rfl
  first_physical := rfl
  second_physical := rfl
  source_ne_first := by decide
  source_ne_second := by decide
  first_ne_second := by decide
  test_edge := congrArg Prod.snd cacheCopyTest_source
  first_edge := congrArg Prod.snd cacheCopyTW_source
  second_edge := congrArg Prod.snd cacheCopyS1_source
  again_edge := congrArg Prod.snd cacheCopyAgain_source
  positive_target := by
    apply source_injective
    rw [cacheCopyTest_source,cacheCopyTW_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  first_target := by
    apply source_injective
    rw [cacheCopyTW_source,cacheCopyS1_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  second_target := by
    apply source_injective
    rw [cacheCopyS1_source,cacheCopyAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [cacheCopyAgain_source,cacheCopyTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [cacheCopyTest_source,cacheRestoreTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_drop_return : resolveControl (breakPath 1 (source dropReturn).1)=fetchTest := by
  apply source_injective
  rw [dropReturn_source,fetchTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) : regValue (put p x file) p=x :=
  write_at file x p
private theorem read_put_other (file x : V) (p q : Fin 9) (h : p≠q) :
    regValue (put p x file) q=regValue file q := write_other file x p q h
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
private theorem run_one (state : V) : controlRun 1 state=ArithmeticControlStep254.stepValue state := by
  rw [show (1 : V)=0+1 by ring,controlRun_succ,controlRun_zero]

/-- The two literal transfer loops move the original TW to scratch1 and
WS to TW. Scratch2 is untouched, with no cleanliness premise at this stage. -/
def prefixFile (file : V) : V :=
  put twReg (regValue file wsReg)
    (put wsReg 0 (put s1Reg (regValue file twReg) (put twReg 0 file)))

theorem prefix_run (file : V) (h1 : regValue file s1Reg=0) :
    controlRun ((3*regValue file twReg+1)+(3*regValue file wsReg+1))
      (liveValue (number dropEntry : V) file)=
      liveValue (number dropPairTest : V) (prefixFile file) := by
  let g := put s1Reg (regValue file twReg) (put twReg 0 file)
  have hfirst : controlRun (3*regValue file twReg+1)
      (liveValue (number dropEntry : V) file)=
      liveValue (number prefixWSTest : V) g := by
    simpa only [prefixTW,h1,zero_add,g] using move_run prefixTW file
  have hgws : regValue g wsReg=regValue file wsReg := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg wsReg (by decide),
      read_put_other _ _ twReg wsReg (by decide)]
  have hgtw : regValue g twReg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg twReg (by decide),read_put_self]
  have hsecond : controlRun (3*regValue file wsReg+1)
      (liveValue (number prefixWSTest : V) g)=
      liveValue (number dropPairTest : V) (prefixFile file) := by
    simpa only [prefixWS,hgws,hgtw,zero_add,prefixFile,g] using move_run prefixWS g
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

/-- Pushing the top formula clears TW and replaces WS by its Cantor pair
with the original TW. The two scratch fields remain unchanged. -/
def pushFile (file : V) : V :=
  put wsReg (cantor (regValue file twReg) (regValue file wsReg)) (put twReg 0 file)

/-- Actual DROP push prefix, including both transfers, pairing, and the
scratch2-to-WS transfer. Both scratch-zero premises are necessary here. -/
theorem push_run (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number dropEntry : V) file)=
        liveValue (number cacheCopyTest : V) (pushFile file) := by
  let p := cantor (regValue file twReg) (regValue file wsReg)
  let g := pairFile (prefixFile file) 0 0 p
  obtain ⟨tp,htp,hpair⟩ := drop_pair_run (prefixFile file)
  rw [prefix_s1,prefix_tw,prefix_s2,h2,zero_add] at hpair
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
      simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg,h1',h2']
    by_cases hi2 : i=(2 : Fin 9)
    · subst i
      simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg,h1',h2']
    by_cases hi5 : i=(5 : Fin 9)
    · subst i
      simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg,h1',h2']
    by_cases hi8 : i=(8 : Fin 9)
    · subst i
      simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg,h1',h2']
    simp [read_put,g,pairFile,prefixFile,pushFile,p,twReg,wsReg,s1Reg,s2Reg,h1',h2',Ne.symm hi0,Ne.symm hi2,Ne.symm hi5,Ne.symm hi8]
  have hpush : controlRun (3*p+1) (liveValue (number dropPairExit : V) g)=
      liveValue (number cacheCopyTest : V) (pushFile file) := by
    have h := move_run pushWS g
    simpa only [pushWS,hgs2,hgws,zero_add,hf] using h
  let t0 := (3*regValue file twReg+1)+(3*regValue file wsReg+1)
  refine ⟨t0+(tp+(3*p+1)),?_,?_⟩
  · exact le_trans htp (le_trans
      (le_add_of_nonneg_right (Arithmetic.zero_le (3*p+1)))
      (le_add_of_nonneg_left (Arithmetic.zero_le t0)))
  · rw [controlRun_add t0 (tp+(3*p+1)),prefix_run file h1,
      controlRun_add tp (3*p+1),hpair,hpush]

/-- The actual cache copy/restore adds the cache to TW and preserves the
cache. It is an overwrite only when its caller has first cleared TW. -/
theorem cache_restore_run (file : V) (h1 : regValue file s1Reg=0) :
    controlRun (7*regValue file cacheReg+2)
      (liveValue (number cacheCopyTest : V) file)=
      liveValue (number dropReturn : V)
        (put twReg (regValue file twReg+regValue file cacheReg) file) := by
  let h := regValue file cacheReg
  let g := put s1Reg h (put twReg (regValue file twReg+h) (put cacheReg 0 file))
  have hcopy : controlRun (4*h+1) (liveValue (number cacheCopyTest : V) file)=
      liveValue (number cacheRestoreTest : V) g := by
    simpa only [cacheCopy,h1,zero_add,h,g] using copy_run cacheCopy file
  have hgs1 : regValue g s1Reg=h := by
    dsimp only [g]
    rw [read_put_self]
  have hgh : regValue g cacheReg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg cacheReg (by decide),
      read_put_other _ _ twReg cacheReg (by decide),read_put_self]
  have hf : put cacheReg h (put s1Reg 0 g)=
      put twReg (regValue file twReg+regValue file cacheReg) file := by
    apply file_ext
    intro i
    have h1' : regValue file (8 : Fin 9)=0 := h1
    by_cases hi2 : i=(2 : Fin 9)
    · subst i
      simp [read_put,g,h,twReg,cacheReg,s1Reg,h1']
    by_cases hi7 : i=(7 : Fin 9)
    · subst i
      simp [read_put,g,h,twReg,cacheReg,s1Reg,h1']
    by_cases hi8 : i=(8 : Fin 9)
    · subst i
      simp [read_put,g,h,twReg,cacheReg,s1Reg,h1']
    simp [read_put,g,h,twReg,cacheReg,s1Reg,h1',Ne.symm hi2,Ne.symm hi7,Ne.symm hi8]
  have hrestore : controlRun (3*h+1) (liveValue (number cacheRestoreTest : V) g)=
      liveValue (number dropReturn : V)
        (put twReg (regValue file twReg+regValue file cacheReg) file) := by
    simpa only [cacheRestore,hgs1,hgh,zero_add,hf] using move_run cacheRestore g
  rw [show 7*regValue file cacheReg+2=(4*h+1)+(3*h+1) by dsimp only [h]; ring,
    controlRun_add,hcopy,hrestore]

/-- The one remaining literal break reaches the actual fetch test. -/
theorem drop_return_run (file : V) :
    controlRun 1 (liveValue (number dropReturn : V) file)=
      liveValue (number fetchTest : V) file := by
  rw [run_one,step_break dropReturn 1 (congrArg Prod.snd dropReturn_source),next_drop_return]

/-- The complete DROP file effect. Every physical field except TW and WS
retains its original value, including the cache and both scratch fields. -/
def dropFile (file : V) : V :=
  put twReg (regValue file cacheReg)
    (put wsReg (cantor (regValue file twReg) (regValue file wsReg)) file)

theorem drop_run (file : V) (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number dropEntry : V) file)=
        liveValue (number fetchTest : V) (dropFile file) := by
  let g := pushFile file
  have hg1 : regValue g s1Reg=0 := by
    dsimp only [g,pushFile]
    rw [read_put_other _ _ wsReg s1Reg (by decide),
      read_put_other _ _ twReg s1Reg (by decide)]
    exact h1
  have hgtw : regValue g twReg=0 := by
    dsimp only [g,pushFile]
    rw [read_put_other _ _ wsReg twReg (by decide),read_put_self]
  have hgh : regValue g cacheReg=regValue file cacheReg := by
    dsimp only [g,pushFile]
    rw [read_put_other _ _ wsReg cacheReg (by decide),
      read_put_other _ _ twReg cacheReg (by decide)]
  have hf : put twReg (regValue g twReg+regValue g cacheReg) g=dropFile file := by
    rw [hgtw,hgh,zero_add]
    apply file_ext
    intro i
    by_cases hi0 : i=(0 : Fin 9)
    · subst i
      simp [read_put,g,pushFile,dropFile,twReg,wsReg,cacheReg]
    by_cases hi2 : i=(2 : Fin 9)
    · subst i
      simp [read_put,g,pushFile,dropFile,twReg,wsReg,cacheReg]
    simp [read_put,g,pushFile,dropFile,twReg,wsReg,cacheReg,Ne.symm hi0,Ne.symm hi2]
  obtain ⟨tp,htp,hpush⟩ := push_run file h1 h2
  have hcache := cache_restore_run g hg1
  rw [hf,hgh] at hcache
  refine ⟨tp+((7*regValue file cacheReg+2)+1),
    le_trans htp (le_add_of_nonneg_right (Arithmetic.zero_le _)),?_⟩
  rw [controlRun_add tp ((7*regValue file cacheReg+2)+1),hpush,
    controlRun_add (7*regValue file cacheReg+2) 1,hcache,drop_return_run]

/-- Classification with AC=1 clears AC, executes complete DROP, and returns
to fetch with the same two scratch-zero premises. -/
theorem dispatch_drop_run (file : V) (ha : regValue file acReg=1)
    (h1 : regValue file s1Reg=0) (h2 : regValue file s2Reg=0) :
    ∃ time : V, 1≤time ∧
      controlRun time (liveValue (number dispatchEntry : V) file)=
        liveValue (number fetchTest : V) (dropFile (put acReg 0 file)) := by
  let g := put acReg 0 file
  have hg1 : regValue g s1Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ acReg s1Reg (by decide)]
    exact h1
  have hg2 : regValue g s2Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ acReg s2Reg (by decide)]
    exact h2
  obtain ⟨time,ht,hr⟩ := drop_run g hg1 hg2
  refine ⟨2+time,le_trans ht (le_add_of_nonneg_left (Arithmetic.zero_le (2 : V))),?_⟩
  rw [controlRun_add,dispatch_drop file ha,hr]

end Model

end SetTheory.BusyBeaver.ZFC.ArithmeticControlDrop254

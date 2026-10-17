import BusyBeaver.ZFC.ArithmeticControlPair254

set_option autoImplicit false
noncomputable section

/-!
Exact all-internal destructive comparison at the actual MP occurrence.
The proof fixes the original file and bounds joint-decrement iterations by
both initial values. It leaves the success body and full MP contract open.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 ArithmeticControlClear254
open ArithmeticControlFetch254 (put s1Reg fetchTest fetchTest_source)
open ArithmeticControlDispatch254 (cacheReg)
open ArithmeticControlPair254 (MoveShape move_run)
open FiniteControlTable254 RegisterPath

private theorem literal_source (P Q : List Bool) (e : Edge)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0=some (e,Q.length))
    (hc : consume P Q.length=Q) : source (resolveControl P)=(Q,e) := by
  rw [resolve_source P e Q.length hw,hc]

def compareEntry : Control := resolveControl [true,true,true,true,true,false,false,false]
def compareCache : Control := resolveControl (incPath (source compareEntry).1)
def compareAgain : Control := resolveControl (incPath (source compareCache).1)
def remainderTest : Control := resolveControl (breakPath 1 (source compareCache).1)
def remainderInc : Control := resolveControl (incPath (source remainderTest).1)
def remainderAgain : Control := resolveControl (incPath (source remainderInc).1)
def remainderBump : Control := resolveControl (breakPath 1 (source remainderTest).1)
def distanceTest : Control := resolveControl (breakPath 1 (source compareEntry).1)
def successEntry : Control := resolveControl (breakPath 1 (source distanceTest).1)

theorem compareEntry_source : source compareEntry=([true,true,true,true,true,false,false,false],.decnz 6) := by
  unfold compareEntry
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem compareCache_source : source compareCache=([true,true,true,true,true,false,false,true,false,false],.decnz 5) := by
  rw [compareCache,compareEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem compareAgain_source : source compareAgain=([true,true,true,true,true,false,false,true,false,true],.cont 2) := by
  rw [compareAgain,compareCache_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem remainderTest_source : source remainderTest=([true,true,true,true,true,false,false,true,true,false,false],.decnz 6) := by
  rw [remainderTest,compareCache_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem remainderInc_source : source remainderInc=([true,true,true,true,true,false,false,true,true,false,true,false],.inc 5) := by
  rw [remainderInc,remainderTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem remainderAgain_source : source remainderAgain=([true,true,true,true,true,false,false,true,true,false,true,true],.cont 2) := by
  rw [remainderAgain,remainderInc_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem remainderBump_source : source remainderBump=([true,true,true,true,true,false,false,true,true,true],.inc 5) := by
  rw [remainderBump,remainderTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem distanceTest_source : source distanceTest=([true,true,true,true,true,false,true,false],.decnz 5) := by
  rw [distanceTest,compareEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)
theorem successEntry_source : source successEntry=([true,true,true,true,true,true,false,false,false],.decnz 1) := by
  rw [successEntry,distanceTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_compare_positive : resolveControl (incPath (source compareEntry).1)=compareCache := by
  apply source_injective
  rw [compareEntry_source,compareCache_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_compare_zero : resolveControl (breakPath 1 (source compareEntry).1)=distanceTest := by
  apply source_injective
  rw [compareEntry_source,distanceTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_cache_positive : resolveControl (incPath (source compareCache).1)=compareAgain := by
  apply source_injective
  rw [compareCache_source,compareAgain_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_cache_zero : resolveControl (breakPath 1 (source compareCache).1)=remainderTest := by
  apply source_injective
  rw [compareCache_source,remainderTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_compare_again : resolveControl (continuePath 2 (source compareAgain).1)=compareEntry := by
  apply source_injective
  rw [compareAgain_source,compareEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_remainder_bump : resolveControl (incPath (source remainderBump).1)=distanceTest := by
  apply source_injective
  rw [remainderBump_source,distanceTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_distance_positive : resolveControl (incPath (source distanceTest).1)=literalTest := by
  apply source_injective
  rw [distanceTest_source,literal_test_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_distance_zero : resolveControl (breakPath 1 (source distanceTest).1)=successEntry := by
  apply source_injective
  rw [distanceTest_source,successEntry_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

theorem next_clear_exit : resolveControl (breakPath 1 (source literalExit).1)=fetchTest := by
  apply source_injective
  rw [literal_exit_source,fetchTest_source]
  exact literal_source _ _ _ (by rfl) (by rfl)

def remainderMove : MoveShape where
  test := remainderTest
  increment := remainderInc
  again := remainderAgain
  exit := remainderBump
  sourceLogical := 6
  targetLogical := 5
  sourceIndex := s1Reg
  targetIndex := cacheReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd remainderTest_source
  increment_edge := congrArg Prod.snd remainderInc_source
  again_edge := congrArg Prod.snd remainderAgain_source
  positive_target := by
    apply source_injective
    rw [remainderTest_source,remainderInc_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  increment_target := by
    apply source_injective
    rw [remainderInc_source,remainderAgain_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  repeat_target := by
    apply source_injective
    rw [remainderAgain_source,remainderTest_source]
    exact literal_source _ _ _ (by rfl) (by rfl)
  zero_target := by
    apply source_injective
    rw [remainderTest_source,remainderBump_source]
    exact literal_source _ _ _ (by rfl) (by rfl)

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
private theorem run_one (state : V) : controlRun 1 state=ArithmeticControlStep254.stepValue state := by
  rw [show (1 : V)=0+1 by ring,controlRun_succ,controlRun_zero]
private theorem read_s1 (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 6) 0=regValue file s1Reg :=
  physicalValues_getD file s1Reg
private theorem read_h (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 5) 0=regValue file cacheReg :=
  physicalValues_getD file cacheReg

local instance write_definable : 𝚺₁-Function₃[V] writeValue := write_defined.to_definable
local instance live_definable : 𝚺₁-Function₂[V] liveValue := live_defined.to_definable
local instance reg_definable (p : Fin 9) : 𝚺₁-Function₁[V] (fun file => regValue file p) :=
  (projection_defined 8 p).to_definable

/-- Exactly the two compared physical fields change. -/
def compareFile (file a b : V) : V := put cacheReg b (put s1Reg a file)
private theorem compareFile_s1 (file a b : V) : regValue (compareFile file a b) s1Reg=a := by
  rw [compareFile,read_put_other _ _ cacheReg s1Reg (by decide),read_put_self]
private theorem compareFile_cache (file a b : V) : regValue (compareFile file a b) cacheReg=b := by
  rw [compareFile,read_put_self]
private theorem compareFile_same (file : V) :
    compareFile file (regValue file s1Reg) (regValue file cacheReg)=file := by
  simp only [compareFile,put_same]
private theorem compareFile_put_s1 (file a b x : V) :
    put s1Reg x (compareFile file a b)=compareFile file x b := by
  simp only [compareFile,put_commute s1Reg cacheReg (by decide),put_twice]
private theorem compareFile_put_cache (file a b x : V) :
    put cacheReg x (compareFile file a b)=compareFile file a x := by
  simp only [compareFile,put_twice]
private theorem compareFile_overwrite (file a b x y : V) :
    compareFile (compareFile file a b) x y=compareFile file x y := by
  simp only [compareFile,put_commute s1Reg cacheReg (by decide),put_twice]

private theorem s1_positive (file : V) (h : regValue file s1Reg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number compareEntry : V) file)=
      liveValue (number compareCache : V) (put s1Reg (regValue file s1Reg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 6) 0≠0 := by rwa [read_s1]
  rw [step_decnz_positive compareEntry 6 (congrArg Prod.snd compareEntry_source) file hn,
    next_compare_positive,read_s1]
  rfl
private theorem s1_zero (file : V) (h : regValue file s1Reg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number compareEntry : V) file)=
      liveValue (number distanceTest : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 6) 0=0 := by rwa [read_s1]
  rw [step_decnz_zero compareEntry 6 (congrArg Prod.snd compareEntry_source) file hz,
    next_compare_zero]
private theorem cache_positive (i j : Control) (he : (source i).2=.decnz 5)
    (hj : resolveControl (incPath (source i).1)=j) (file : V)
    (h : regValue file cacheReg≠0) :
    ArithmeticControlStep254.stepValue (liveValue (number i : V) file)=
      liveValue (number j : V) (put cacheReg (regValue file cacheReg-1) file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 5) 0≠0 := by rwa [read_h]
  rw [step_decnz_positive i 5 he file hn,hj,read_h]
  rfl
private theorem cache_zero (i j : Control) (he : (source i).2=.decnz 5)
    (hj : resolveControl (breakPath 1 (source i).1)=j) (file : V)
    (h : regValue file cacheReg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number i : V) file)=
      liveValue (number j : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 5) 0=0 := by rwa [read_h]
  rw [step_decnz_zero i 5 he file hz,hj]
private theorem step_bump (file : V) :
    ArithmeticControlStep254.stepValue (liveValue (number remainderBump : V) file)=
      liveValue (number distanceTest : V) (put cacheReg (regValue file cacheReg+1) file) := by
  rw [step_inc remainderBump 5 (congrArg Prod.snd remainderBump_source),
    next_remainder_bump,read_h]
  rfl

/-- Both compared fields positive: one joint decrement takes three steps. -/
theorem compare_cycle (file : V) (ha : regValue file s1Reg≠0)
    (hb : regValue file cacheReg≠0) :
    controlRun 3 (liveValue (number compareEntry : V) file)=
      liveValue (number compareEntry : V)
        (compareFile file (regValue file s1Reg-1) (regValue file cacheReg-1)) := by
  let g := put s1Reg (regValue file s1Reg-1) file
  have hgb : regValue g cacheReg≠0 := by
    dsimp only [g]
    rwa [read_put_other _ _ s1Reg cacheReg (by decide)]
  rw [show (3 : V)=((0+1)+1)+1 by ring,
    controlRun_succ,controlRun_succ,controlRun_succ,controlRun_zero,
    s1_positive file ha,
    cache_positive compareCache compareAgain (congrArg Prod.snd compareCache_source)
      next_cache_positive g hgb,
    step_continue compareAgain 2 (congrArg Prod.snd compareAgain_source),next_compare_again]
  simp only [g,read_put_other _ _ s1Reg cacheReg (by decide),compareFile]

private def walkFile (file t : V) : V :=
  compareFile file (regValue file s1Reg-t) (regValue file cacheReg-t)
private theorem walkFile_s1 (file t : V) :
    regValue (walkFile file t) s1Reg=regValue file s1Reg-t := compareFile_s1 _ _ _
private theorem walkFile_cache (file t : V) :
    regValue (walkFile file t) cacheReg=regValue file cacheReg-t := compareFile_cache _ _ _
private theorem walkFile_zero (file : V) : walkFile file 0=file := by
  simp only [walkFile,tsub_zero,compareFile_same]
private theorem walkFile_succ (file t : V) :
    compareFile (walkFile file t) (regValue (walkFile file t) s1Reg-1)
      (regValue (walkFile file t) cacheReg-1)=walkFile file (t+1) := by
  rw [walkFile_s1,walkFile_cache]
  simp only [walkFile,compareFile_overwrite,←tsub_add_eq_tsub_tsub]

/-- The original file is fixed throughout the bounded Σ₁ induction. -/
theorem joint_reach (file t : V) (ha : t≤regValue file s1Reg)
    (hb : t≤regValue file cacheReg) :
    controlRun (3*t) (liveValue (number compareEntry : V) file)=
      liveValue (number compareEntry : V)
        (compareFile file (regValue file s1Reg-t) (regValue file cacheReg-t)) := by
  have reach (t : V) : t≤regValue file s1Reg → t≤regValue file cacheReg →
      controlRun (3*t) (liveValue (number compareEntry : V) file)=
        liveValue (number compareEntry : V) (walkFile file t) := by
    induction t using ISigma1.sigma1_succ_induction
    · unfold walkFile compareFile put
      definability
    case zero =>
      intro _ _
      rw [mul_zero,controlRun_zero,walkFile_zero]
    case succ t ih =>
      intro hta htb
      have ht : t≤t+1 := le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))
      have hp := ih (le_trans ht hta) (le_trans ht htb)
      have hpa : regValue (walkFile file t) s1Reg≠0 := by
        rw [walkFile_s1]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) hta))
      have hpb : regValue (walkFile file t) cacheReg≠0 := by
        rw [walkFile_cache]
        exact ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_lt_of_le (lt_add_one t) htb))
      rw [show 3*(t+1)=3*t+3 by ring,controlRun_add,hp,compare_cycle _ hpa hpb,
        walkFile_succ]
  exact reach t ha hb

/-- Natural absolute difference; it vanishes exactly on equality. -/
def distance (a b : V) : V := if a≤b then b-a else a-b

theorem distance_eq_zero (a b : V) : distance a b=0 ↔ a=b := by
  by_cases hab : a≤b
  · rw [distance,if_pos hab,tsub_eq_zero_iff_le]
    exact ⟨fun h => le_antisymm hab h,fun h => h.ge⟩
  · rw [distance,if_neg hab,tsub_eq_zero_iff_le]
    exact ⟨fun h => False.elim (hab h),fun h => h.le⟩

private theorem exhausted_run (file : V) (ha : regValue file s1Reg≠0)
    (hb : regValue file cacheReg=0) :
    controlRun 2 (liveValue (number compareEntry : V) file)=
      liveValue (number remainderTest : V) (put s1Reg (regValue file s1Reg-1) file) := by
  let g := put s1Reg (regValue file s1Reg-1) file
  have hgb : regValue g cacheReg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ s1Reg cacheReg (by decide),hb]
  rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,s1_positive file ha,
    cache_zero compareCache remainderTest (congrArg Prod.snd compareCache_source)
      next_cache_zero g hgb]

/-- The comparison body takes exactly 3*initialScratch1+1 instructions,
independent of the initial cache, and leaves their distance in the cache. -/
theorem compare_body_run (file : V) :
    controlRun (3*regValue file s1Reg+1) (liveValue (number compareEntry : V) file)=
      liveValue (number distanceTest : V)
        (compareFile file 0 (distance (regValue file s1Reg) (regValue file cacheReg))) := by
  let a := regValue file s1Reg
  let b := regValue file cacheReg
  by_cases hab : a≤b
  · have hr := joint_reach file a le_rfl hab
    have hz : regValue (compareFile file (a-a) (b-a)) s1Reg=0 := by
      rw [compareFile_s1,tsub_self]
    rw [controlRun_succ,hr,s1_zero _ hz]
    simp only [distance,if_pos hab,a,b,tsub_self]
  · have hba : b<a := lt_of_not_ge hab
    let r := a-b-1
    have hab1 : r+1=a-b := tsub_add_cancel_of_le (by
      simpa only [zero_add] using lt_iff_succ_le.mp (tsub_pos_iff_lt.mpr hba))
    have hclock : 3*a+1=((3*b+2)+(3*r+1))+1 := by
      calc
        3*a+1=3*((r+1)+b)+1 := by rw [hab1,tsub_add_cancel_of_le hba.le]
        _=((3*b+2)+(3*r+1))+1 := by ring
    have hr := joint_reach file b hba.le le_rfl
    have hga : regValue (compareFile file (a-b) (b-b)) s1Reg≠0 := by
      rw [compareFile_s1]
      exact ne_of_gt (tsub_pos_iff_lt.mpr hba)
    have hgb : regValue (compareFile file (a-b) (b-b)) cacheReg=0 := by
      rw [compareFile_cache,tsub_self]
    have hpre : controlRun (3*b+2) (liveValue (number compareEntry : V) file)=
        liveValue (number remainderTest : V) (compareFile file r 0) := by
      rw [controlRun_add (3*b) 2,hr,exhausted_run _ hga hgb]
      simp only [compareFile_s1,compareFile_put_s1,tsub_self,r]
    have hmove : controlRun (3*r+1)
        (liveValue (number remainderTest : V) (compareFile file r 0))=
        liveValue (number remainderBump : V) (compareFile file 0 r) := by
      simpa only [remainderMove,compareFile_s1,compareFile_cache,zero_add,
        compareFile_put_s1,compareFile_put_cache] using
        move_run remainderMove (compareFile file r 0)
    rw [hclock,controlRun_succ,controlRun_add,hpre,hmove,step_bump,
      compareFile_cache,compareFile_put_cache,hab1,distance,if_neg hab]

private theorem clear_return (file : V) :
    controlRun 1 (liveValue (number literalExit : V) file)=
      liveValue (number fetchTest : V) file := by
  rw [run_one,step_break literalExit 1 (congrArg Prod.snd literal_exit_source),next_clear_exit]

/-- The final zero test, actual literal cache clear, and actual failure break.
The other file fields, including scratch1, need no hypotheses. -/
theorem distance_tail_run (file : V) :
    controlRun (2*regValue file cacheReg+1) (liveValue (number distanceTest : V) file)=
      if regValue file cacheReg=0 then
        liveValue (number successEntry : V) (put cacheReg 0 file)
      else liveValue (number fetchTest : V) (put cacheReg 0 file) := by
  by_cases hz : regValue file cacheReg=0
  · have hf : put cacheReg 0 file=file := by rw [←hz]; exact put_same _ _
    rw [hz,mul_zero,zero_add,if_pos rfl,hf,run_one]
    exact cache_zero distanceTest successEntry (congrArg Prod.snd distanceTest_source)
      next_distance_zero file hz
  · let c := regValue file cacheReg-1
    have hc : c+1=regValue file cacheReg := tsub_add_cancel_of_le (by
      simpa only [zero_add] using lt_iff_succ_le.mp
        (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm hz)))
    let g := put cacheReg c file
    have hfirst : controlRun 1 (liveValue (number distanceTest : V) file)=
        liveValue (number literalTest : V) g := by
      rw [run_one]
      exact cache_positive distanceTest literalTest (congrArg Prod.snd distanceTest_source)
        next_distance_positive file hz
    have hclear : controlRun (2*c+1) (liveValue (number literalTest : V) g)=
        liveValue (number literalExit : V) (put cacheReg 0 file) := by
      have h : controlRun (2*regValue g cacheReg+1) (liveValue (number literalTest : V) g)=
          liveValue (number literalExit : V) (put cacheReg 0 g) := literal_clear_run g
      simpa only [g,read_put_self,put_twice] using h
    have ht : 2*regValue file cacheReg+1=(1+(2*c+1))+1 := by
      rw [←hc]
      ring
    rw [if_neg hz,ht,controlRun_add (1+(2*c+1)) 1,controlRun_add 1 (2*c+1),
      hfirst,hclear,clear_return]

/-- Complete actual MP destructive comparison. It clears scratch1 and cache,
enters the success push exactly on equality, otherwise returns to fetch. -/
theorem compare_run (file : V) :
    controlRun (3*regValue file s1Reg+
        2*distance (regValue file s1Reg) (regValue file cacheReg)+2)
      (liveValue (number compareEntry : V) file)=
      if regValue file s1Reg=regValue file cacheReg then
        liveValue (number successEntry : V) (compareFile file 0 0)
      else liveValue (number fetchTest : V) (compareFile file 0 0) := by
  let d := distance (regValue file s1Reg) (regValue file cacheReg)
  have htail := distance_tail_run (compareFile file 0 d)
  rw [compareFile_cache,compareFile_put_cache] at htail
  rw [show 3*regValue file s1Reg+2*distance (regValue file s1Reg) (regValue file cacheReg)+2=
      (3*regValue file s1Reg+1)+(2*d+1) by dsimp only [d]; ring,
    controlRun_add,compare_body_run,htail]
  simp only [d,distance_eq_zero]

/-- A positive all-internal clock witness for composing this comparison with
its callers. Neither compared field is assumed standard or initially zero. -/
theorem compare_terminates (file : V) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number compareEntry : V) file)=
      if regValue file s1Reg=regValue file cacheReg then
        liveValue (number successEntry : V) (compareFile file 0 0)
      else liveValue (number fetchTest : V) (compareFile file 0 0) := by
  refine ⟨3*regValue file s1Reg+
    2*distance (regValue file s1Reg) (regValue file cacheReg)+2,?_,compare_run file⟩
  rw [show 3*regValue file s1Reg+
      2*distance (regValue file s1Reg) (regValue file cacheReg)+2=
      (3*regValue file s1Reg+2*distance (regValue file s1Reg) (regValue file cacheReg)+1)+1 by ring]
  exact le_add_of_nonneg_left (Arithmetic.zero_le _)

end Model

end SetTheory.BusyBeaver.ZFC.ArithmeticControlCompare254

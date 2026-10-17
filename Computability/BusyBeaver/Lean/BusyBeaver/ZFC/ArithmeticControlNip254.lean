import BusyBeaver.ZFC.ArithmeticControlDispatch254

set_option autoImplicit false
noncomputable section

/-!
Actual NIP nonfalsity comparison and cache-clear phase. Its whole-file endpoint
is the literal stack-pop entry; the WS unpair/pop body is not established here.
All values and the cache-clear counter may be internal to an IΣ1 model.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 FiniteControlTable254 RegisterPath
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (acReg)
open ArithmeticControlDispatch254

private theorem resolved_source (P Q : List Bool) (e : Edge)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0=some (e,Q.length))
    (hc : consume P Q.length=Q) : source (resolveControl P)=(Q,e) := by
  rw [resolve_source P e Q.length hw,hc]

def cacheZeroS1 : Control := resolveControl (breakPath 1 (source nipTestH).1)
def cacheZeroInc : Control := resolveControl (breakPath 1 (source cacheZeroS1).1)
def cacheClearTest : Control := resolveControl (incPath (source nipZeroH).1)
def cacheClearAgain : Control := resolveControl (incPath (source cacheClearTest).1)
def cacheClearExit : Control := resolveControl (breakPath 1 (source cacheClearTest).1)
def stackPopEntry : Control := resolveControl (breakPath 1 (source cacheClearExit).1)

theorem cacheZeroS1_source : source cacheZeroS1=([true,true,true,false,true,false,false,true,false,true,true,false,false,false,true,true,false,false],.decnz 6) := by
  rw [cacheZeroS1,nipTestH_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem cacheZeroInc_source : source cacheZeroInc=([true,true,true,false,true,false,false,true,false,true,true,false,false,false,true,true,true],.inc 5) := by
  rw [cacheZeroInc,cacheZeroS1_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem cacheClearTest_source : source cacheClearTest=([true,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,false],.decnz 5) := by
  rw [cacheClearTest,nipZeroH_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem cacheClearAgain_source : source cacheClearAgain=([true,true,true,false,true,false,false,true,false,true,true,false,false,true,true,false,true],.cont 1) := by
  rw [cacheClearAgain,cacheClearTest_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem cacheClearExit_source : source cacheClearExit=([true,true,true,false,true,false,false,true,false,true,true,false,false,true,true,true],.brk 1) := by
  rw [cacheClearExit,cacheClearTest_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem stackPopEntry_source : source stackPopEntry=([true,true,true,false,true,false,false,true,false,true,true,true,false,false,false],.decnz 2) := by
  rw [stackPopEntry,cacheClearExit_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)

theorem next_cache_zero_inc : resolveControl (incPath (source cacheZeroInc).1)=nipZeroH := by
  apply source_injective
  rw [cacheZeroInc_source,nipZeroH_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)

theorem cache_clear_repeat : resolveControl (continuePath 1 (source cacheClearAgain).1)=cacheClearTest := by
  apply source_injective
  rw [cacheClearAgain_source,cacheClearTest_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)

/-- Literal cache clear, using the already checked all-internal loop theorem. -/
def cacheClear : ArithmeticControlClear254.ClearShape where
  test := cacheClearTest
  again := cacheClearAgain
  exit := cacheClearExit
  register := 5
  test_edge := congrArg Prod.snd cacheClearTest_source
  again_edge := congrArg Prod.snd cacheClearAgain_source
  positive_target := rfl
  repeat_target := cache_clear_repeat
  zero_target := rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem read_put_self (file x : V) (p : Fin 9) : regValue (put p x file) p=x :=
  write_at file x p
private theorem read_put_other (file x : V) (p q : Fin 9) (h : p≠q) :
    regValue (put p x file) q=regValue file q := write_other file x p q h
private theorem put_same (p : Fin 9) (file : V) : put p (regValue file p) file=file :=
  write_same file p
private theorem put_twice (p : Fin 9) (x y file : V) : put p y (put p x file)=put p y file :=
  ArithmeticControlClear254.write_overwrite file x y p
private theorem run_one (state : V) : controlRun 1 state=ArithmeticControlStep254.stepValue state := by
  rw [show (1 : V)=0+1 by ring,controlRun_succ,controlRun_zero]
private theorem read_s1 (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 6) 0=regValue file s1Reg :=
  physicalValues_getD file s1Reg
private theorem read_h (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 5) 0=regValue file cacheReg :=
  physicalValues_getD file cacheReg

private theorem cache_succ (i j : Control) (he : (source i).2=.decnz 5)
    (hj : resolveControl (incPath (source i).1)=j) (file v : V)
    (hv : regValue file cacheReg=v+1) :
    ArithmeticControlStep254.stepValue (liveValue (number i : V) file)=
      liveValue (number j : V) (put cacheReg v file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 5) 0≠0 := by
    rw [read_h,hv]
    exact ne_of_gt (lt_of_le_of_lt (Arithmetic.zero_le v) (lt_add_one v))
  rw [step_decnz_positive i 5 he file hn,hj,read_h,hv,add_tsub_cancel_right]
  rfl
private theorem cache_zero (i j : Control) (he : (source i).2=.decnz 5)
    (hj : resolveControl (breakPath 1 (source i).1)=j) (file : V)
    (hv : regValue file cacheReg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number i : V) file)=
      liveValue (number j : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 5) 0=0 := by rwa [read_h]
  rw [step_decnz_zero i 5 he file hz,hj]
private theorem s1_zero (i j : Control) (he : (source i).2=.decnz 6)
    (hj : resolveControl (breakPath 1 (source i).1)=j) (file : V)
    (hv : regValue file s1Reg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number i : V) file)=
      liveValue (number j : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 6) 0=0 := by rwa [read_s1]
  rw [step_decnz_zero i 6 he file hz,hj]

/-- The actual NIP increment/decrement restores scratch1 and leaves all other
fields untouched, independently of the cache value. -/
theorem nip_prepare (file : V) (hs : regValue file s1Reg=0) :
    controlRun 2 (liveValue (number nipEntry : V) file)=
      liveValue (number nipTestH : V) file := by
  let inc := put s1Reg 1 file
  have hinc : ArithmeticControlStep254.stepValue (liveValue (number nipEntry : V) file)=
      liveValue (number nipTestS1 : V) inc := by
    rw [step_inc nipEntry 6 (congrArg Prod.snd nipEntry_source),
      show resolveControl (incPath (source nipEntry).1)=nipTestS1 from rfl,read_s1,hs,zero_add]
    rfl
  have hclear : put s1Reg 0 inc=file := by
    dsimp only [inc]
    rw [put_twice,←hs]
    exact put_same _ _
  have hdec : ArithmeticControlStep254.stepValue (liveValue (number nipTestS1 : V) inc)=
      liveValue (number nipTestH : V) file := by
    have hn : (physicalValues inc).getD (Permutation252Frame.physOf 6) 0≠0 := by
      rw [read_s1,show regValue inc s1Reg=1 by exact read_put_self _ _ _]
      exact Arithmetic.one_ne_zero
    rw [step_decnz_positive nipTestS1 6 (congrArg Prod.snd nipTestS1_source) inc hn,
      show resolveControl (incPath (source nipTestS1).1)=nipTestH from rfl,
      read_s1,show regValue inc s1Reg=1 by exact read_put_self _ _ _,tsub_self]
    change liveValue (number nipTestH : V) (put s1Reg 0 inc)=_
    rw [hclear]
  rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,hinc,hdec]

/-- The checked generic clear loop is instantiated at the literal NIP cache
clear. The counter and every whole-file field may be internal. -/
theorem clear_cache (file : V) :
    controlRun (2*regValue file cacheReg+1) (liveValue (number cacheClearTest : V) file)=
      liveValue (number cacheClearExit : V) (put cacheReg 0 file) := by
  have h : controlRun (2*regValue file cacheReg+1)
      (liveValue (number cacheClear.test : V) file)=
      liveValue (number cacheClear.exit : V) (put cacheReg 0 file) :=
    ArithmeticControlClear254.clear_run cacheClear file
  simpa only [cacheClear] using h

/-- Cache0 takes eight literal instructions to the actual stack-pop entry.
The entire file is unchanged, since both tested fields were already zero. -/
theorem nip_cache_zero (file : V) (hs : regValue file s1Reg=0)
    (hh : regValue file cacheReg=0) :
    controlRun 8 (liveValue (number nipEntry : V) file)=
      liveValue (number stackPopEntry : V) file := by
  let inc := put cacheReg 1 file
  have h0 := cache_zero nipTestH cacheZeroS1
    (congrArg Prod.snd nipTestH_source) rfl file hh
  have h1 := s1_zero cacheZeroS1 cacheZeroInc
    (congrArg Prod.snd cacheZeroS1_source) rfl file hs
  have h2 : ArithmeticControlStep254.stepValue (liveValue (number cacheZeroInc : V) file)=
      liveValue (number nipZeroH : V) inc := by
    rw [step_inc cacheZeroInc 5 (congrArg Prod.snd cacheZeroInc_source),next_cache_zero_inc,
      read_h,hh,zero_add]
    rfl
  have hclear : put cacheReg 0 inc=file := by
    dsimp only [inc]
    rw [put_twice,←hh]
    exact put_same _ _
  have h3 : ArithmeticControlStep254.stepValue (liveValue (number nipZeroH : V) inc)=
      liveValue (number cacheClearTest : V) file := by
    have h := cache_succ nipZeroH cacheClearTest
      (congrArg Prod.snd nipZeroH_source) rfl inc 0
      (by rw [read_put_self]; ring)
    simpa only [hclear] using h
  have h4 := cache_zero cacheClearTest cacheClearExit
    (congrArg Prod.snd cacheClearTest_source) rfl file hh
  have h5 : ArithmeticControlStep254.stepValue (liveValue (number cacheClearExit : V) file)=
      liveValue (number stackPopEntry : V) file := by
    rw [step_break cacheClearExit 1 (congrArg Prod.snd cacheClearExit_source)]
    rfl
  have htail : controlRun 6 (liveValue (number nipTestH : V) file)=
      liveValue (number stackPopEntry : V) file := by
    rw [show (6 : V)=(((((0+1)+1)+1)+1)+1)+1 by ring,
      controlRun_succ,controlRun_succ,controlRun_succ,controlRun_succ,
      controlRun_succ,controlRun_succ,controlRun_zero,h0,h1,h2,h3,h4,h5]
  rw [show (8 : V)=2+6 by ring,controlRun_add,nip_prepare file hs,htail]

/-- Every cache=c+2 follows six fixed instructions, then the checked internal
cache-clear loop and its literal break. Only the cache field changes. -/
theorem nip_cache_positive (file c : V) (hs : regValue file s1Reg=0)
    (hh : regValue file cacheReg=c+2) :
    controlRun (2*c+8) (liveValue (number nipEntry : V) file)=
      liveValue (number stackPopEntry : V) (put cacheReg 0 file) := by
  let g1 := put cacheReg (c+1) file
  let g0 := put cacheReg c file
  have h0 := cache_succ nipTestH nipAgain
    (congrArg Prod.snd nipTestH_source) rfl file (c+1) (by rw [hh]; ring)
  have h1 : ArithmeticControlStep254.stepValue (liveValue (number nipAgain : V) g1)=
      liveValue (number nipTestS1 : V) g1 := by
    rw [step_continue nipAgain 2 (congrArg Prod.snd nipAgain_source),next_nip_again]
  have hgs : regValue g1 s1Reg=0 := by
    dsimp only [g1]
    rw [read_put_other _ _ cacheReg s1Reg (by decide)]
    exact hs
  have h2 := s1_zero nipTestS1 nipZeroH
    (congrArg Prod.snd nipTestS1_source) rfl g1 hgs
  have h3 : ArithmeticControlStep254.stepValue (liveValue (number nipZeroH : V) g1)=
      liveValue (number cacheClearTest : V) g0 := by
    have h := cache_succ nipZeroH cacheClearTest
      (congrArg Prod.snd nipZeroH_source) rfl g1 c (read_put_self _ _ _)
    simpa only [g0,g1,put_twice] using h
  have htail : controlRun 4 (liveValue (number nipTestH : V) file)=
      liveValue (number cacheClearTest : V) g0 := by
    rw [show (4 : V)=(((0+1)+1)+1)+1 by ring,controlRun_succ,controlRun_succ,
      controlRun_succ,controlRun_succ,controlRun_zero,h0,h1,h2,h3]
  have hreach : controlRun 6 (liveValue (number nipEntry : V) file)=
      liveValue (number cacheClearTest : V) g0 := by
    rw [show (6 : V)=2+4 by ring,controlRun_add,nip_prepare file hs,htail]
  have hc := clear_cache g0
  rw [show regValue g0 cacheReg=c by exact read_put_self _ _ _] at hc
  have hc' : controlRun (2*c+1) (liveValue (number cacheClearTest : V) g0)=
      liveValue (number cacheClearExit : V) (put cacheReg 0 file) := by
    simpa only [g0,put_twice] using hc
  rw [show 2*c+8=(6+(2*c+1))+1 by ring,
    controlRun_add (6+(2*c+1)) 1 (liveValue (number nipEntry : V) file),
    controlRun_add 6 (2*c+1) (liveValue (number nipEntry : V) file),hreach,hc',run_one,
    step_break cacheClearExit 1 (congrArg Prod.snd cacheClearExit_source)]
  rfl

private theorem clock_positive (c : V) : 1≤2*c+8 := by
  rw [show 2*c+8=(2*c+7)+1 by ring]
  exact le_add_of_nonneg_left (Arithmetic.zero_le _)

/-- The complete cache≠1 comparison/clear phase. Its endpoint is the actual
stack-pop entry; the stack-pop body itself is a separate obligation. -/
theorem nip_nonfalsity (file : V) (hs : regValue file s1Reg=0)
    (hh : regValue file cacheReg≠1) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number nipEntry : V) file)=
      liveValue (number stackPopEntry : V) (put cacheReg 0 file) := by
  rcases opcode_cases (regValue file cacheReg) with h0 | h1 | h2 | ⟨d,hd⟩
  · have hp : put cacheReg 0 file=file := by rw [←h0]; exact put_same _ _
    refine ⟨8,?_,?_⟩
    · simpa only [mul_zero,zero_add] using clock_positive (0 : V)
    · rw [hp]
      exact nip_cache_zero file hs h0
  · exact False.elim (hh h1)
  · refine ⟨2*0+8,clock_positive 0,?_⟩
    exact nip_cache_positive file 0 hs (by simpa only [zero_add] using h2)
  · refine ⟨2*(d+1)+8,clock_positive (d+1),?_⟩
    exact nip_cache_positive file (d+1) hs (by rw [hd]; ring)

/-- Classification followed by the actual nonfalsity comparison/cache-clear
phase. Only AC and cache are changed before the stack-pop entry. -/
theorem dispatch_nip_nonfalsity (file : V) (ha : regValue file acReg=2)
    (hs : regValue file s1Reg=0) (hh : regValue file cacheReg≠1) :
    ∃ time : V, 1≤time ∧ controlRun time (liveValue (number dispatchEntry : V) file)=
      liveValue (number stackPopEntry : V) (put cacheReg 0 (put acReg 0 file)) := by
  let g := put acReg 0 file
  have hgs : regValue g s1Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ acReg s1Reg (by decide)]
    exact hs
  have hgh : regValue g cacheReg≠1 := by
    dsimp only [g]
    rw [read_put_other _ _ acReg cacheReg (by decide)]
    exact hh
  obtain ⟨t,ht,hr⟩ := nip_nonfalsity g hgs hgh
  refine ⟨3+t,le_trans ht (le_add_of_nonneg_left (Arithmetic.zero_le (3 : V))),?_⟩
  rw [controlRun_add,dispatch_nip file ha,hr]

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlNip254

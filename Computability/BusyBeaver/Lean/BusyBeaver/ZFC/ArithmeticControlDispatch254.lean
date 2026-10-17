import BusyBeaver.ZFC.ArithmeticControlReadTemplate254

set_option autoImplicit false
noncomputable section

/-!
Actual dispatch classification and the cached-falsity NIP branch. Literal
resolved source facts connect every finite step to the current program;
all unused fields may be arbitrary internal values. No complete internal
L2/Enum or blank-start endpoint is asserted.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlSimulation254
open ArithmeticControlStep254 ArithmeticControlFrame254 FiniteControlTable254 RegisterPath
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (acReg)
open ArithmeticControlReadTemplate254 (p1Read)

/-- A literal walk binds a resolved catalogue control without reducing its
possibly large ordinal through the entire DFS list. -/
private theorem resolved_source (P Q : List Bool) (e : Edge)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0=some (e,Q.length))
    (hc : consume P Q.length=Q) : source (resolveControl P)=(Q,e) := by
  rw [resolve_source P e Q.length hw,hc]

def dispatchEntry : Control := p1Read.nextRead
def dispatchSecond : Control := ⟨39,by decide⟩
def dispatchThird : Control := ⟨40,by decide⟩
def axEntry : Control := ⟨41,by decide⟩
def mpEntry : Control := resolveControl (breakPath 1 (source dispatchEntry).1)
def dropEntry : Control := resolveControl (breakPath 1 (source dispatchSecond).1)
def nipEntry : Control := resolveControl (breakPath 1 (source dispatchThird).1)
def nipTestS1 : Control := resolveControl (incPath (source nipEntry).1)
def nipTestH : Control := resolveControl (incPath (source nipTestS1).1)
def nipAgain : Control := resolveControl (incPath (source nipTestH).1)
def nipZeroH : Control := resolveControl (breakPath 1 (source nipTestS1).1)
def nipHalt : Control := resolveControl (breakPath 1 (source nipZeroH).1)

def cacheReg : Fin 9 := 7

theorem dispatchEntry_source : source dispatchEntry=([true,true,true,false,false],.decnz 3) := ArithmeticControlReadTemplate254.p1Read_exit_source
theorem dispatchSecond_source : source dispatchSecond=([true,true,true,false,true,false,false,false],.decnz 3) := by rfl
theorem dispatchThird_source : source dispatchThird=([true,true,true,false,true,false,false,true,false,false,false],.decnz 3) := by rfl
theorem axEntry_source : source axEntry=([true,true,true,false,true,false,false,true,false,false,true,false,false,false,false,false,false,false],.decnz 1) := by rfl

theorem next_dispatch_positive : resolveControl (incPath (source dispatchEntry).1)=dispatchSecond := by rfl
theorem next_second_positive : resolveControl (incPath (source dispatchSecond).1)=dispatchThird := by rfl
theorem next_third_positive : resolveControl (incPath (source dispatchThird).1)=axEntry := by rfl

theorem mpEntry_source : source mpEntry=([true,true,true,true,false,false,false,false,false,false],.decnz 1) := by
  rw [mpEntry,dispatchEntry_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem dropEntry_source : source dropEntry=([true,true,true,false,true,false,true,false,false,false],.decnz 1) := by
  rw [dropEntry,dispatchSecond_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem nipEntry_source : source nipEntry=([true,true,true,false,true,false,false,true,false,true,false],.inc 6) := by
  rw [nipEntry,dispatchThird_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem nipTestS1_source : source nipTestS1=([true,true,true,false,true,false,false,true,false,true,true,false,false,false,false],.decnz 6) := by
  rw [nipTestS1,nipEntry_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem nipTestH_source : source nipTestH=([true,true,true,false,true,false,false,true,false,true,true,false,false,false,true,false,false],.decnz 5) := by
  rw [nipTestH,nipTestS1_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem nipAgain_source : source nipAgain=([true,true,true,false,true,false,false,true,false,true,true,false,false,false,true,false,true],.cont 2) := by
  rw [nipAgain,nipTestH_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem nipZeroH_source : source nipZeroH=([true,true,true,false,true,false,false,true,false,true,true,false,false,true,false],.decnz 5) := by
  rw [nipZeroH,nipTestS1_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)
theorem nipHalt_source : source nipHalt=([true,true,true,false,true,false,false,true,false,true,true,false,true],.halt) := by
  rw [nipHalt,nipZeroH_source]
  exact resolved_source _ _ _ (by rfl) (by rfl)

theorem next_nip_again : resolveControl (continuePath 2 (source nipAgain).1)=nipTestS1 := by
  rw [nipAgain_source,nipTestS1,nipEntry_source]
  rfl

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
private theorem read_ac (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 3) 0=regValue file acReg :=
  physicalValues_getD file acReg
private theorem read_s1 (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 6) 0=regValue file s1Reg :=
  physicalValues_getD file s1Reg
private theorem read_h (file : V) :
    (physicalValues file).getD (Permutation252Frame.physOf 5) 0=regValue file cacheReg :=
  physicalValues_getD file cacheReg

private theorem ac_positive (i j : Control) (he : (source i).2=.decnz 3)
    (hj : resolveControl (incPath (source i).1)=j) (file v : V)
    (hv : regValue file acReg=v+1) :
    ArithmeticControlStep254.stepValue (liveValue (number i : V) file)=
      liveValue (number j : V) (put acReg v file) := by
  have hn : (physicalValues file).getD (Permutation252Frame.physOf 3) 0≠0 := by
    rw [read_ac,hv]
    exact ne_of_gt (lt_of_le_of_lt (Arithmetic.zero_le v) (lt_add_one v))
  rw [step_decnz_positive i 3 he file hn,hj,read_ac,hv,add_tsub_cancel_right]
  rfl
private theorem ac_zero (i j : Control) (he : (source i).2=.decnz 3)
    (hj : resolveControl (breakPath 1 (source i).1)=j) (file : V)
    (hv : regValue file acReg=0) :
    ArithmeticControlStep254.stepValue (liveValue (number i : V) file)=
      liveValue (number j : V) file := by
  have hz : (physicalValues file).getD (Permutation252Frame.physOf 3) 0=0 := by rwa [read_ac]
  rw [step_decnz_zero i 3 he file hz,hj]

/-- Exhaustive internal opcode alternatives, with no standardness premise. -/
theorem opcode_cases (a : V) : a=0 ∨ a=1 ∨ a=2 ∨ ∃ c : V, a=c+3 := by
  have split0 (x : V) : x=0 ∨ ∃ y : V, x=y+1 := by
    by_cases hz : x=0
    · exact Or.inl hz
    · right
      refine ⟨x-1,?_⟩
      have hp : 0<x := lt_of_le_of_ne (Arithmetic.zero_le x) (Ne.symm hz)
      exact (tsub_add_cancel_of_le (by simpa using lt_iff_succ_le.mp hp)).symm
  rcases split0 a with ha | ⟨b,hb⟩
  · exact Or.inl ha
  · rcases split0 b with hb0 | ⟨c,hc⟩
    · right; left
      rw [hb,hb0]
      ring
    · rcases split0 c with hc0 | ⟨d,hd⟩
      · right; right; left
        rw [hb,hc,hc0]
        ring
      · right; right; right
        refine ⟨d,?_⟩
        rw [hb,hc,hd]
        ring

/-- AC=0 enters the actual MP branch without changing any file field. -/
theorem dispatch_mp (file : V) (ha : regValue file acReg=0) :
    controlRun 1 (liveValue (number dispatchEntry : V) file)=
      liveValue (number mpEntry : V) file := by
  rw [run_one,ac_zero dispatchEntry mpEntry (congrArg Prod.snd dispatchEntry_source) rfl file ha]

/-- AC=1 consumes its classifier decrement and enters the actual DROP branch. -/
theorem dispatch_drop (file : V) (ha : regValue file acReg=1) :
    controlRun 2 (liveValue (number dispatchEntry : V) file)=
      liveValue (number dropEntry : V) (put acReg 0 file) := by
  have hfirst := ac_positive dispatchEntry dispatchSecond
    (congrArg Prod.snd dispatchEntry_source) next_dispatch_positive file 0
    (by simpa only [zero_add] using ha)
  have hsecond := ac_zero dispatchSecond dropEntry
    (congrArg Prod.snd dispatchSecond_source) rfl (put acReg 0 file) (read_put_self _ _ _)
  rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,hfirst,hsecond]

/-- AC=2 consumes two decrements and enters the actual NIP branch. -/
theorem dispatch_nip (file : V) (ha : regValue file acReg=2) :
    controlRun 3 (liveValue (number dispatchEntry : V) file)=
      liveValue (number nipEntry : V) (put acReg 0 file) := by
  let g1 := put acReg 1 file
  let g0 := put acReg 0 file
  have hfirst := ac_positive dispatchEntry dispatchSecond
    (congrArg Prod.snd dispatchEntry_source) next_dispatch_positive file 1
    (by rw [ha]; ring)
  have hsecond : ArithmeticControlStep254.stepValue (liveValue (number dispatchSecond : V) g1)=
      liveValue (number dispatchThird : V) g0 := by
    have h := ac_positive dispatchSecond dispatchThird
      (congrArg Prod.snd dispatchSecond_source) next_second_positive g1 0
      (by rw [read_put_self]; ring)
    simpa only [g0,g1,put_twice] using h
  have hthird := ac_zero dispatchThird nipEntry
    (congrArg Prod.snd dispatchThird_source) rfl g0 (read_put_self _ _ _)
  rw [show (3 : V)=((0+1)+1)+1 by ring,controlRun_succ,controlRun_succ,
    controlRun_succ,controlRun_zero,hfirst,hsecond,hthird]

/-- The remaining internal opcodes enter AX after exactly three classifier
steps, retaining their actual c parameter and every other file field. -/
theorem dispatch_ax (file c : V) (ha : regValue file acReg=c+3) :
    controlRun 3 (liveValue (number dispatchEntry : V) file)=
      liveValue (number axEntry : V) (put acReg c file) := by
  let g2 := put acReg (c+2) file
  let g1 := put acReg (c+1) file
  let g0 := put acReg c file
  have hfirst := ac_positive dispatchEntry dispatchSecond
    (congrArg Prod.snd dispatchEntry_source) next_dispatch_positive file (c+2)
    (by rw [ha]; ring)
  have hsecond : ArithmeticControlStep254.stepValue (liveValue (number dispatchSecond : V) g2)=
      liveValue (number dispatchThird : V) g1 := by
    have h := ac_positive dispatchSecond dispatchThird
      (congrArg Prod.snd dispatchSecond_source) next_second_positive g2 (c+1)
      (by rw [read_put_self]; ring)
    simpa only [g1,g2,put_twice] using h
  have hthird : ArithmeticControlStep254.stepValue (liveValue (number dispatchThird : V) g1)=
      liveValue (number axEntry : V) g0 := by
    have h := ac_positive dispatchThird axEntry
      (congrArg Prod.snd dispatchThird_source) next_third_positive g1 c (read_put_self _ _ _)
    simpa only [g0,g1,put_twice] using h
  rw [show (3 : V)=((0+1)+1)+1 by ring,controlRun_succ,controlRun_succ,
    controlRun_succ,controlRun_zero,hfirst,hsecond,hthird]

/-- The actual cached-falsity NIP branch takes seven instructions including
halt. Only scratch1 and the cache are constrained; every other field is free. -/
theorem nip_falsity (file : V) (hs : regValue file s1Reg=0)
    (hh : regValue file cacheReg=1) :
    controlRun 7 (liveValue (number nipEntry : V) file)=0 := by
  let inc := put s1Reg 1 file
  let g := put cacheReg 0 file
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
  have htwo : controlRun 2 (liveValue (number nipEntry : V) file)=
      liveValue (number nipTestH : V) file := by
    rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,hinc,hdec]
  have hhstep : ArithmeticControlStep254.stepValue (liveValue (number nipTestH : V) file)=
      liveValue (number nipAgain : V) g := by
    have hn : (physicalValues file).getD (Permutation252Frame.physOf 5) 0≠0 := by
      rw [read_h,hh]
      exact Arithmetic.one_ne_zero
    rw [step_decnz_positive nipTestH 5 (congrArg Prod.snd nipTestH_source) file hn,
      show resolveControl (incPath (source nipTestH).1)=nipAgain from rfl,read_h,hh,tsub_self]
    rfl
  have hnexttwo : controlRun 2 (liveValue (number nipTestH : V) file)=
      liveValue (number nipTestS1 : V) g := by
    rw [show (2 : V)=1+1 by ring,controlRun_succ,run_one,hhstep,
      step_continue nipAgain 2 (congrArg Prod.snd nipAgain_source),next_nip_again]
  have hgs : regValue g s1Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ cacheReg s1Reg (by decide)]
    exact hs
  have hgh : regValue g cacheReg=0 := read_put_self _ _ _
  have hszero : ArithmeticControlStep254.stepValue (liveValue (number nipTestS1 : V) g)=
      liveValue (number nipZeroH : V) g := by
    rw [step_decnz_zero nipTestS1 6 (congrArg Prod.snd nipTestS1_source) g
      (by rwa [read_s1]),show resolveControl (breakPath 1 (source nipTestS1).1)=nipZeroH from rfl]
  have hhzero : ArithmeticControlStep254.stepValue (liveValue (number nipZeroH : V) g)=
      liveValue (number nipHalt : V) g := by
    rw [step_decnz_zero nipZeroH 5 (congrArg Prod.snd nipZeroH_source) g
      (by rwa [read_h]),show resolveControl (breakPath 1 (source nipZeroH).1)=nipHalt from rfl]
  have hlast : controlRun 3 (liveValue (number nipTestS1 : V) g)=0 := by
    rw [show (3 : V)=((0+1)+1)+1 by ring,controlRun_succ,controlRun_succ,
      controlRun_succ,controlRun_zero,hszero,hhzero,
      step_halt nipHalt (congrArg Prod.snd nipHalt_source)]
  rw [show (7 : V)=(2+2)+3 by ring,
    controlRun_add (2+2) 3 (liveValue (number nipEntry : V) file),
    controlRun_add 2 2 (liveValue (number nipEntry : V) file),htwo,hnexttwo,hlast]

/-- Three classifier instructions followed by the seven-instruction actual
NIP halt. The whole input file is arbitrary outside the three tested fields. -/
theorem dispatch_nip_falsity (file : V) (ha : regValue file acReg=2)
    (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=1) :
    controlRun 10 (liveValue (number dispatchEntry : V) file)=0 := by
  let g := put acReg 0 file
  have hgs : regValue g s1Reg=0 := by
    dsimp only [g]
    rw [read_put_other _ _ acReg s1Reg (by decide)]
    exact hs
  have hgh : regValue g cacheReg=1 := by
    dsimp only [g]
    rw [read_put_other _ _ acReg cacheReg (by decide)]
    exact hh
  rw [show (10 : V)=3+7 by ring,controlRun_add,dispatch_nip file ha,nip_falsity g hgs hgh]

/-- Actual arbitrary-internal binary-entry halting follows from the existing
positive-clock simulation. No ten-step binary clock or blank-start claim. -/
theorem dispatch_nip_falsity_binary_entry (file count gap : V)
    (ha : regValue file acReg=2) (hs : regValue file s1Reg=0) (hh : regValue file cacheReg=1) :
    ∃ time : V, first (ArithmeticMachineRunFromPerm252.runFrom time
      (entryValue (number dispatchEntry : V) file count gap))=0 := by
  exact (halts_iff_entry dispatchEntry file count gap).mp ⟨10,dispatch_nip_falsity file ha hs hh⟩

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlDispatch254

import BusyBeaver.ZFC.ArithmeticControlRun254

set_option autoImplicit false

/-!
A first actual internal loop contract for the numbered literal interpreter.
The two-leaf clear loop is closed at actual indices6431/6432/6433. Ordinary
finite `RMDag.Run` derivations are not used to represent internal loop counts.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlRun254 ArithmeticControlSimulation254 ArithmeticControlStep254
open ArithmeticControlFrame254 FiniteControlTable254 RegisterPath

/-- All premises concern the actual finite control catalogue, not an arithmetic
model or an arbitrary instruction oracle. The concrete instance below closes
these premises for one literal clear-param2 occurrence. -/
structure ClearShape where
  test : Control
  again : Control
  exit : Control
  register : Fin 9
  test_edge : (source test).2=.decnz register.val
  again_edge : (source again).2=.cont 1
  positive_target : resolveControl (incPath (source test).1)=again
  repeat_target : resolveControl (continuePath 1 (source again).1)=test
  zero_target : resolveControl (breakPath 1 (source test).1)=exit

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private noncomputable def physical (c : ClearShape) : Fin 9 :=
  SitePerm252.physical c.register.val c.register.isLt

/-- A repeated write to one valid physical field replaces the previous write. -/
theorem write_overwrite (file x y : V) (p : Fin 9) :
    writeValue (p.val : V) y (writeValue (p.val : V) x file)=writeValue (p.val : V) y file := by
  calc
    _ = fileValue (regValue (writeValue (p.val : V) y (writeValue (p.val : V) x file))) :=
      (file_reg _).symm
    _ = fileValue (regValue (writeValue (p.val : V) y file)) := by
      congr 1
      funext j
      by_cases h : (p.val : V)=(j.val : V) <;> simp only [reg_write,h,if_true,if_false]
    _ = _ := file_reg _

theorem clear_cycle (c : ClearShape) (file : V) (hn : regValue file (physical c)≠0) :
    ArithmeticControlStep254.stepValue
      (ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file))=
      liveValue (number c.test : V)
        (writeValue ((physical c).val : V) (regValue file (physical c)-1) file) := by
  have hread : (physicalValues file).getD (Permutation252Frame.physOf c.register.val) 0=
      regValue file (physical c) := physicalValues_getD file (physical c)
  have hnonzero : (physicalValues file).getD (Permutation252Frame.physOf c.register.val) 0≠0 := by
    rwa [hread]
  rw [step_decnz_positive c.test c.register.val c.test_edge file hnonzero,
    c.positive_target,step_continue c.again 1 c.again_edge,c.repeat_target,hread]
  simp only [physical,SitePerm252.physical]

theorem clear_exit (c : ClearShape) (file : V) (hz : regValue file (physical c)=0) :
    ArithmeticControlStep254.stepValue (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V) file := by
  have hread : (physicalValues file).getD (Permutation252Frame.physOf c.register.val) 0=
      regValue file (physical c) := physicalValues_getD file (physical c)
  have hzero : (physicalValues file).getD (Permutation252Frame.physOf c.register.val) 0=0 := by
    rwa [hread]
  rw [step_decnz_zero c.test c.register.val c.test_edge file hzero,c.zero_target]

local instance write_definable : 𝚺₁-Function₃[V] writeValue := write_defined.to_definable
local instance live_definable : 𝚺₁-Function₂[V] liveValue := live_defined.to_definable

/-- Exact logical instruction clock. The induction fixes the original whole
file and tracks only an internal elapsed iteration index, so it does not hide
a universal-over-files/existential-clock induction assumption. -/
theorem clear_run (c : ClearShape) (file : V) :
    controlRun (2*regValue file (physical c)+1) (liveValue (number c.test : V) file)=
      liveValue (number c.exit : V) (writeValue ((physical c).val : V) 0 file) := by
  let p := physical c
  let v := regValue file p
  have reach (t : V) : t≤v →
      controlRun (2*t) (liveValue (number c.test : V) file)=
        liveValue (number c.test : V) (writeValue (p.val : V) (v-t) file) := by
    induction t using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro _
      simpa only [mul_zero,controlRun_zero,tsub_zero] using
        (congrArg (liveValue (number c.test : V)) (write_same file p)).symm
    case succ t ih =>
      intro ht
      have hprev := ih (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (1 : V))) ht)
      have hpos : v-t≠0 := ne_of_gt (tsub_pos_iff_lt.mpr
        (lt_of_lt_of_le (lt_add_one t) ht))
      have hcurrent : regValue (writeValue (p.val : V) (v-t) file) (physical c)≠0 := by
        rw [write_at]
        exact hpos
      rw [show 2*(t+1)=(2*t+1)+1 by ring,controlRun_succ,controlRun_succ,hprev,
        clear_cycle c _ hcurrent]
      rw [write_at,write_overwrite,←tsub_add_eq_tsub_tsub]
  have hlast := reach v le_rfl
  rw [tsub_self] at hlast
  rw [controlRun_succ,hlast,clear_exit c _ (by rw [write_at])]

end Model

/-- The shortest literal clear-param2 occurrence, discovered from the actual
row table. The source equations and path/resolver facts are checked below;
the discovery script itself contributes no trusted premise. -/
def literalTest : Control := ⟨6431,by decide⟩
def literalAgain : Control := ⟨6432,by decide⟩
def literalExit : Control := ⟨6433,by decide⟩

def literalParent : List Bool := [true,true,true,true,true,false,true,true,false]

set_option maxRecDepth 8192 in
theorem literal_test_source : source literalTest=(literalParent++[false],.decnz 5) := by rfl
set_option maxRecDepth 8192 in
theorem literal_again_source : source literalAgain=(literalParent++[true],.cont 1) := by rfl
set_option maxRecDepth 8192 in
theorem literal_exit_source : source literalExit=
    ([true,true,true,true,true,false,true,true,true],.brk 1) := by rfl

def literalClear : ClearShape where
  test := literalTest
  again := literalAgain
  exit := literalExit
  register := ⟨5,by decide⟩
  test_edge := congrArg Prod.snd literal_test_source
  again_edge := congrArg Prod.snd literal_again_source
  positive_target := by
    have hp : incPath (source literalTest).1=(source literalAgain).1 := by
      rw [literal_test_source,literal_again_source]
      rfl
    rw [hp]
    exact resolve_source_self literalAgain
  repeat_target := by
    have hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root
        (continuePath 1 (source literalAgain).1) 0=
        some (.decnz 5,(source literalTest).1.length) := by
      rw [literal_again_source,literal_test_source]
      rfl
    apply source_injective
    rw [resolve_source _ _ _ hw,literal_test_source]
    rw [literal_again_source]
    rfl
  zero_target := by
    have hp : breakPath 1 (source literalTest).1=(source literalExit).1 := by
      rw [literal_test_source,literal_exit_source]
      rfl
    rw [hp]
    exact resolve_source_self literalExit

/-- Actual param2 is logical register5, stored in physical register7. The
result stops at the next literal brk1 leaf, before executing that continuation. -/
theorem literal_clear_run {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (file : V) :
    controlRun (2*regValue file (7 : Fin 9)+1) (liveValue (number literalTest : V) file)=
      liveValue (number literalExit : V) (writeValue (7 : V) 0 file) :=
  clear_run literalClear file

end SetTheory.BusyBeaver.ZFC.ArithmeticControlClear254

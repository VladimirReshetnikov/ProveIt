import BusyBeaver.ZFC.ArithmeticControlSimulation254
import BusyBeaver.ZFC.ArithmeticPositiveSimulation254
import BusyBeaver.ZFC.ArithmeticMachinePrefixPerm252

set_option autoImplicit false

/-!
The represented actual finite-control program, iterated at every internal IΣ1
time, and its concrete binary halting equivalence. The blank entry uses the
already checked bootstrap, without replaying its steps. Internal L2/Enum
scheduler equivalence remains a separate obligation.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticControlSimulation254 FiniteControlTable254
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out initial. out=initial”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index initial. !ArithmeticControlStep254.stepDef out previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef
noncomputable def construction : PR.Construction V blueprint where
  zero parameters := parameters 0
  succ _ _ previous := ArithmeticControlStep254.stepValue previous
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef]

noncomputable def controlRun (time initial : V) : V := construction.result ![initial] time
def controlRunDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def controlRunDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef
instance controlRun_defined : 𝚺₁-Function₂[V] controlRun via controlRunDef := .mk fun e => by
  have he : (fun i : Fin 1 => e i.succ.succ)=![e 2] := by
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := (construction (V := V)).result_defined.df e
  change blueprint.resultDef.val.Evalb e ↔
    e 0=construction.result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
  rw [he] at h
  change blueprint.resultDef.val.Evalb e ↔ e 0=construction.result ![e 2] (e 1)
  exact h
instance controlRun_defined_delta : 𝚫₁-Function₂[V] controlRun via controlRunDeltaDef :=
  controlRun_defined.graph_delta
instance controlRun_definable : 𝚺₁-Function₂[V] controlRun := controlRun_defined.to_definable

@[simp] theorem controlRun_zero (initial : V) : controlRun 0 initial=initial := by
  simp [controlRun,construction]
@[simp] theorem controlRun_succ (time initial : V) :
    controlRun (time+1) initial=ArithmeticControlStep254.stepValue (controlRun time initial) := by
  simp [controlRun,PR.Construction.result_succ,construction]

theorem controlRun_add (firstTime secondTime initial : V) :
    controlRun (firstTime+secondTime) initial=
      controlRun secondTime (controlRun firstTime initial) := by
  induction secondTime using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ secondTime ih => rw [←add_assoc,controlRun_succ,controlRun_succ,ih]

@[simp] theorem controlRun_halted (time : V) : controlRun time 0=0 := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact controlRun_zero 0
  case succ time ih => rw [controlRun_succ,ih,ArithmeticControlStep254.step_zero]

theorem controlRun_total (time initial : V) :
    ∃! out : V, controlRunDef.val.Evalb ![out,time,initial] := by simp

/-- Concrete all-internal equivalence from every valid numbered entry. The
binary direction uses positive clocks, without a register-growth upper bound. -/
theorem halts_iff_entry (i : Control) (file count gap : V) :
    (∃ time : V, controlRun time (liveValue (number i : V) file)=0) ↔
      (∃ time : V, first (runFrom time (entryValue (number i : V) file count gap))=0) := by
  haveI : 𝚺₁-Function₁[V] (fun time => controlRun time (liveValue (number i : V) file)) := by
    definability
  apply ArithmeticPositiveSimulation254.halts_iff
    ArithmeticControlStep254.stepValue
    (fun time => controlRun time (liveValue (number i : V) file))
    runFrom Related (fun binary => first binary=0)
    (liveValue (number i : V) file) (entryValue (number i : V) file count gap)
  · exact controlRun_zero _
  · intro time; exact controlRun_succ time _
  · exact runFrom_zero
  · exact runFrom_add
  · exact related_entry i file count gap
  · exact related_live
  · intro logical binary h hh; exact related_active logical binary h hh
  · exact related_step
  · intro logical binary h hh
    obtain ⟨time,_,ht⟩ := related_halt logical binary h hh
    exact ⟨time,ht⟩
  · intro binary hh time
    exact runFrom_halt_state time binary hh

private theorem first_zero : first (0 : V)=0 :=
  le_antisymm (projections_spec (0 : V)).1 (Arithmetic.zero_le _)
private theorem second_zero : second (0 : V)=0 :=
  le_antisymm (projections_spec (0 : V)).2.1 (Arithmetic.zero_le _)

/-- Fixed external tuple recursion, valid for every internal zero code. -/
theorem projection_zero (n : Nat) (i : Fin (n+1)) : tupleProjection n (0 : V) i=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact first_zero
      · change tupleProjection n (second (0 : V)) j=0
        rw [second_zero]
        exact ih j

theorem physicalValues_zero : physicalValues (0 : V)=List.replicate 9 0 := by
  have h : regValue (0 : V)=(fun _ => (0 : V)) := funext (fun i => projection_zero 8 i)
  rw [physicalValues,h]
  exact List.ofFn_const 9 0

/-- Canonicalizing the empty PC consumes no binary clock. The walk/resolver
argument is the same one already checked by the frame runtime lemma. -/
theorem entry_empty (file count gap : V) :
    entryValue (number (resolveControl []) : V) file count gap=
      ArithmeticSitePerm252.startValue (physicalValues file) count gap [] := by
  have h := canonical_runtime [] [] false .unchanged file file count gap 0 (by simp)
    (RegisterPathClean.clean_nil Prog254.program) (by rw [runFrom_zero]; rfl) rfl
  simpa only [runFrom_zero,ArithmeticDispatchRebasePerm252.effectCount,digit,
    Bool.false_eq_true,if_false,add_zero] using h.symm

def initialControl : Control := resolveControl []
noncomputable def initialValue : V := liveValue (number initialControl : V) 0

theorem initialControl_number : number initialControl=1 := by
  rw [initialControl,empty_control]
  rfl

theorem initialValue_live_one : initialValue (V := V)=liveValue 1 0 := by
  rw [initialValue,initialControl_number,Nat.cast_one]

/-- This exact closed entry preserves the existing literal bootstrap code;
no large numeral or 82,552-step run is recomputed. -/
theorem entry_boot : entryValue (number initialControl : V) 0 56 0=
    (ArithmeticBootstrapPerm252.bootCode : V) := by
  rw [initialControl,entry_empty,physicalValues_zero]
  exact (ArithmeticSiteBootPerm252.bootCode_start (V := V)).symm

/-- The actual blank binary evaluator halts exactly when this represented
source-derived control interpreter reaches its absorbing zero. This does not
identify the interpreter with the internal L2/Enum scheduler. -/
theorem halts_iff_blank :
    (∃ time : V, controlRun time initialValue=0) ↔
      (∃ time : V, first (ArithmeticMachineRunPerm252.run time)=0) := by
  have h := halts_iff_entry (V := V) initialControl (0 : V) 56 0
  rw [entry_boot] at h
  exact h.trans (ArithmeticMachinePrefixPerm252.boot_halts_iff (V := V))

end SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254

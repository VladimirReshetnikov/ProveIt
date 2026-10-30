import DiophantineConsistency.ArithmeticEnumStepPerm222
import DiophantineConsistency.ArithmeticUnaryRecursion

/-! Internal iteration of the actual permuted C222 enumeration step.
The fixed graph is total at every internal IΣ1 time, for every initial
scalar state. Its standard-Nat adapter uses actual EnumPerm.run on every
ordinary state. No scheduling, proof invariant or consistency bridge is
asserted here. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumRunPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticEnumStepPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out initial. out = initial”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index initial. !enumDef out previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef
noncomputable def construction : PR.Construction V blueprint where
  zero parameters := parameters 0
  succ _ _ previous := enumValue previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

noncomputable def run (time initial : V) : V := construction.result ![initial] time
def runDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def runDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef

instance run_defined : 𝚺₁-Function₂[V] run via runDef :=
  ArithmeticUnaryRecursion.result_defined blueprint construction

instance run_defined_delta : 𝚫₁-Function₂[V] run via runDeltaDef := run_defined.graph_delta
instance run_definable : 𝚺₁-Function₂[V] run := run_defined.to_definable

@[simp] theorem run_zero (initial : V) : run 0 initial = initial := by
  simp [run, construction]
@[simp] theorem run_succ (time initial : V) :
    run (time+1) initial = enumValue (run time initial) := by
  simp [run, PR.Construction.result_succ, construction]

@[simp] theorem run_halted (time : V) : run time 0 = 0 := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ time ih => rw [run_succ, ih, enum_zero]

theorem run_add (first second initial : V) :
    run (first+second) initial = run second (run first initial) := by
  induction second using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ second ih => rw [←add_assoc, run_succ, run_succ, ih]

theorem run_one (initial : V) : run 1 initial = enumValue initial := by
  simpa only [zero_add, run_zero] using run_succ (0 : V) initial

theorem run_total (time initial : V) : ∃! out, runDef.val.Evalb ![out,time,initial] := by
  simp

lemma run_succ_first (time initial : V) :
    run (time+1) initial = run time (enumValue initial) := by
  rw [add_comm time 1, run_add, run_one]

@[simp] theorem encodeStateResult_eq_zero (s : Option EnumPerm.St) :
    encodeStateResult s = 0 ↔ s = none :=
  ArithmeticEnumStepPerm222.encodeStateResult_eq_zero_iff s

/-- Exact agreement for all ordinary times and arbitrary dirty registers. -/
theorem run_encode_nat (time : ℕ) (s : EnumPerm.St) :
    run time (encodeState s) = encodeStateResult (EnumPerm.run time s) := by
  induction time generalizing s with
  | zero => simp [EnumPerm.run, encodeStateResult]
  | succ time ih =>
    rw [run_succ_first, enumValue_nat]
    cases hs : EnumPerm.enumStep s with
    | none => simp [hs, EnumPerm.run, encodeStateResult]
    | some s' =>
      simpa only [EnumPerm.run, hs, encodeStateResult] using ih s'

theorem runDef_encode_nat (out time : ℕ) (s : EnumPerm.St) :
    runDef.val.Evalb ![out,time,encodeState s] ↔
      out = encodeStateResult (EnumPerm.run time s) := by
  simp [run_encode_nat]

theorem run_zero_iff_native_none (time : ℕ) (s : EnumPerm.St) :
    run time (encodeState s) = 0 ↔ EnumPerm.run time s = none := by
  rw [run_encode_nat, encodeStateResult_eq_zero]

end DiophantineConsistency.ArithmeticEnumRunPerm222

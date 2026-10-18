import BusyBeaver.ZFC.ArithmeticMachineStepPrefix246

/-!
One fixed represented run evaluator for the exact contextual-fold246 machine. Its
Sigma1/Delta1 graph is total at every index of every ISigma1 model. The standard
Nat graph agrees with every actual Core run time; PA proof transport between
machine traces and ZFC proof codes remains separate.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachinePerm252 ArithmeticMachineStepPrefix246
open ArithmeticMachineStepPerm252 (encodeConfig)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- P(1,P(0,0)) is exactly1: the actual blank state0 configuration. -/
def zeroDef : 𝚺₁.Semisentence 1 := .mkSigma “r. r = 1”

def succDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out previous index. !ArithmeticMachineStepPrefix246.stepDef out previous”

def blueprint : PR.Blueprint 0 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 1
  succ _ _ previous := stepValue previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

noncomputable def run (time : V) : V := construction.result ![] time

def runDef : 𝚺₁.Semisentence 2 := blueprint.resultDef

def runDeltaDef : 𝚫₁.Semisentence 2 := blueprint.resultDeltaDef

instance run_defined : 𝚺₁-Function₁[V] run via runDef := .mk fun e => by
  have he : (fun i : Fin 0 => e i.succ.succ) = ![] := Subsingleton.elim _ _
  have h := (construction (V := V)).result_defined.df e
  change blueprint.resultDef.val.Evalb e ↔
    e 0 = construction.result (fun i : Fin 0 => e i.succ.succ) (e 1) at h
  rw [he] at h
  change blueprint.resultDef.val.Evalb e ↔ e 0 = construction.result ![] (e 1)
  exact h

instance run_defined_delta : 𝚫₁-Function₁[V] run via runDeltaDef := run_defined.graph_delta

instance run_definable : 𝚺₁-Function₁[V] run := run_defined.to_definable

@[simp] theorem run_zero : run (0 : V) = 1 := by simp [run, construction]

@[simp] theorem run_succ (time : V) : run (time + 1) = stepValue (run time) := by
  simp [run, PR.Construction.result_succ, construction]

theorem run_total (time : V) : ∃! out, runDef.val.Evalb ![out,time] := by simp

/-- No time or fuel cutoff: this equality holds at every ordinary natural run
time. The represented graph above separately covers nonstandard model indices. -/
theorem run_nat (time : Nat) : run time = encodeConfig (numericRun machinePrefix246 time) := by
  induction time with
  | zero => rw [run_zero]; rfl
  | succ time ih => rw [run_succ, ih, stepValue_nat_encoded]; rfl

theorem runDef_nat (out time : Nat) :
    runDef.val.Evalb ![out,time] ↔ out = encodeConfig (numericRun machinePrefix246 time) := by
  simp [run_nat]

theorem run_state_nat (time : Nat) :
    ArithmeticCantor.first (run time) = (numericRun machinePrefix246 time).state := by
  rw [run_nat]
  simp [encodeConfig, ArithmeticCantor.first_nat, Code254.unP_P]

theorem run_halt_iff (time : Nat) :
    ArithmeticCantor.first (run time) = 0 ↔ (machinePrefix246.run time).state = none := by
  rw [run_state_nat, numericRun_state_zero_iff]

/-- A literal parameter-free Sigma1 sentence for actual blank halting. -/
def haltingSentence : 𝚺₁.Sentence := .mkSigma
  “∃ time, ∃ config, !runDef config time ∧ !ArithmeticCantor.firstDef 0 config”

theorem haltingSentence_nat : haltingSentence.val.Evalb (M := Nat) ![] ↔
    ∃ time, (machinePrefix246.run time).state = none := by
  have h (time : Nat) : (0 = (SetTheory.Cantor.ofNat (run time)).1) ↔
      (machinePrefix246.run time).state = none := by
    constructor
    · intro ht
      apply (run_halt_iff time).mp
      simpa only [ArithmeticCantor.first_nat] using ht.symm
    · intro ht
      have hs := (run_halt_iff time).mpr ht
      simpa only [ArithmeticCantor.first_nat] using hs.symm
  simpa [haltingSentence] using (exists_congr h)

/-- A closed arithmetic assertion of total unique evaluation, not an internal
consistency equivalence. -/
def totalitySentence : ArithmeticSentence :=
  “∀ time, ∃ config, !runDef config time ∧
    ∀ other, !runDef other time → other = config”

theorem totalitySentence_true : totalitySentence.Evalb (M := V) ![] := by
  simp [totalitySentence]

theorem isigma1_proves_totality : 𝗜𝚺₁ ⊢ totalitySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (totalitySentence_true (V := M))

theorem peano_proves_totality : Peano ⊢ totalitySentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_totality

end SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunPrefix246

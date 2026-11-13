import DiophantineConsistency.ArithmeticMachineStep215

/-! The exact decimal215 represented run, total and unique at every index of every IΣ1 model. The standard Nat graph agrees with the actual Core machine at every time. The closed halting sentence has no machine parameter. IΣ1 and PA prove run totality; no machine/validator consistency equivalence or HA derivation is asserted. -/
namespace DiophantineConsistency.ArithmeticMachineRun215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
attribute [local irreducible] DecimalMachine215.machine
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachinePerm252 ArithmeticMachineStep215
open ArithmeticMachineStepPerm252 (encodeConfig decodeConfig decode_encode)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- P(1,P(0,0)) is exactly1: the actual blank state0 configuration. -/
def zeroDef : 𝚺₁.Semisentence 1 := .mkSigma “r. r = 1”

def succDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out previous index. !ArithmeticMachineStep215.stepDef out previous”

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
theorem run_nat (time : Nat) : run time = encodeConfig (numericRun DecimalMachine215.machine time) := by
  induction time with
  | zero => rw [run_zero]; rfl
  | succ time ih => rw [run_succ, ih, stepValue_nat_encoded]; rfl

/-- The same represented run code determines a zipper for every actual tape
cell and its absolute head, not only a matching halting-state predicate. -/
theorem run_represents (time : Nat) :
    Represents (DecimalMachine215.machine.run time) (decodeConfig (run time))
      (numericRunHead DecimalMachine215.machine time) := by
  rw [run_nat, decode_encode]
  exact numericRun_sound DecimalMachine215.machine time

theorem runDef_nat (out time : Nat) :
    runDef.val.Evalb ![out,time] ↔ out = encodeConfig (numericRun DecimalMachine215.machine time) := by
  simp [run_nat]

theorem run_state_nat (time : Nat) :
    ArithmeticCantor.first (run time) = (numericRun DecimalMachine215.machine time).state := by
  rw [run_nat]
  simp [encodeConfig, ArithmeticCantor.first_nat, Code254.unP_P]

theorem run_halt_iff (time : Nat) :
    ArithmeticCantor.first (run time) = 0 ↔ (DecimalMachine215.machine.run time).state = none := by
  rw [run_state_nat, numericRun_state_zero_iff]

/-- A literal parameter-free Sigma1 sentence for actual blank halting. -/
def haltingSentence : 𝚺₁.Sentence := .mkSigma
  “∃ time, ∃ config, !runDef config time ∧ !ArithmeticCantor.firstDef 0 config”

theorem haltingSentence_nat : haltingSentence.val.Evalb (M := Nat) ![] ↔
    ∃ time, (DecimalMachine215.machine.run time).state = none := by
  have h (time : Nat) : (0 = (SetTheory.Cantor.ofNat (run time)).1) ↔
      (DecimalMachine215.machine.run time).state = none := by
    simpa only [ArithmeticCantor.first_nat, eq_comm] using (run_halt_iff time)
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

end DiophantineConsistency.ArithmeticMachineRun215

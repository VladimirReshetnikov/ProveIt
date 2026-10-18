import BusyBeaver.ZFC.ArithmeticMachineRunPrefix246

/-!
The exact contextual-fold246 arithmetic step iterated from arbitrary initial codes.
A fixed Blueprint1 graph is total at every internal IΣ1 time. Additivity and
full-configuration absorption at stateCode0 provide the run substrate for
later concrete simulations; the published blank run is recovered at initial1.
No concrete register or scheduler simulation is assumed or proved here.
Adapted from ArithmeticMachineRunFromPerm252; the generic arithmetic helpers
retain their existing names while the table and step graph are the246 ones.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPrefix246
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor
open ArithmeticMachineGraphPerm252 (lookupValue lookupNat)
open ArithmeticMachineStepPerm252 (genericStepValue)
open ArithmeticMachineGraphPrefix246 (actionLookup literalRows)
open ArithmeticMachineStepPrefix246 (stepValue nativeStep stepValue_nat)
variable {V : Type*} [ORingStructure V]

section IOpen
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- Source stateCode0 misses every positive literal source key. This proves
lookup absence in all arithmetic models, not only on ordinary Nat inputs. -/
lemma lookupValue_zero (rows : List (Nat × Nat)) (start : Nat) (bit : V) :
    lookupValue rows start 0 bit = 0 := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    have hk : (0 : V) ≠ ORingStructure.numeral (start+1) := by
      have hp : (0 : V) < (ORingStructure.numeral (start+1) : V) := by
        simpa only [numeral_eq_natCast] using
          (Nat.cast_pos (α := V)).mpr (Nat.zero_lt_succ start)
      exact ne_of_lt hp
    simpa only [lookupValue, if_neg hk] using ih (start+1)

/-- Every fixed natural source/read key is evaluated by the same literal
lookup in every model. This is the static-row bridge for later scan proofs. -/
lemma lookupValue_numeral (rows : List (Nat × Nat)) (start q bit : Nat) :
    lookupValue rows start (ORingStructure.numeral q : V) (ORingStructure.numeral bit) =
      ORingStructure.numeral (lookupNat rows start q bit) := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    have hkey : ((ORingStructure.numeral q : V) = ORingStructure.numeral (start+1)) ↔
        q = start+1 := by
      simp only [numeral_eq_natCast, Nat.cast_inj]
    have hbit : ((ORingStructure.numeral bit : V) = 0) ↔ bit = 0 := by
      simp only [numeral_eq_natCast, Nat.cast_eq_zero]
    by_cases hq : q = start+1
    · simp only [lookupValue, hkey, if_pos hq, lookupNat, hbit]
      by_cases hb : bit = 0
      · simp only [if_pos hb]
      · simp only [if_neg hb]
    · simp only [lookupValue, hkey, if_neg hq, lookupNat]
      exact ih (start+1)

lemma actionLookup_numeral (q bit : Nat) :
    actionLookup (ORingStructure.numeral q : V) (ORingStructure.numeral bit) =
      ORingStructure.numeral (lookupNat literalRows 0 q bit) :=
  lookupValue_numeral literalRows 0 q bit

@[simp] lemma actionLookup_zero (bit : V) : actionLookup 0 bit = 0 :=
  lookupValue_zero literalRows 0 bit

/-- Halt absorption preserves the whole encoded tape, not just its state. -/
lemma step_halted (config : V) (hh : first config = 0) : stepValue config = config := by
  simp only [stepValue, genericStepValue, hh, actionLookup_zero, if_true]

end IOpen

section ISigma1
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out initial. out = initial”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index initial. !ArithmeticMachineStepPrefix246.stepDef out previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef
noncomputable def construction : PR.Construction V blueprint where
  zero parameters := parameters 0
  succ _ _ previous := stepValue previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

noncomputable def runFrom (time initial : V) : V := construction.result ![initial] time

def runFromDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def runFromDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef
instance runFrom_defined : 𝚺₁-Function₂[V] runFrom via runFromDef := .mk fun e => by
  have he : (fun i : Fin 1 => e i.succ.succ) = ![e 2] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := (construction (V := V)).result_defined.df e
  change blueprint.resultDef.val.Evalb e ↔
    e 0 = construction.result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
  rw [he] at h
  change blueprint.resultDef.val.Evalb e ↔ e 0 = construction.result ![e 2] (e 1)
  exact h
instance runFrom_defined_delta : 𝚫₁-Function₂[V] runFrom via runFromDeltaDef :=
  runFrom_defined.graph_delta
instance runFrom_definable : 𝚺₁-Function₂[V] runFrom := runFrom_defined.to_definable

@[simp] theorem runFrom_zero (initial : V) : runFrom 0 initial = initial := by
  simp [runFrom, construction]
@[simp] theorem runFrom_succ (time initial : V) :
    runFrom (time+1) initial = stepValue (runFrom time initial) := by
  simp [runFrom, PR.Construction.result_succ, construction]

theorem runFrom_one (initial : V) : runFrom 1 initial = stepValue initial := by
  simpa only [zero_add, runFrom_zero] using runFrom_succ (0 : V) initial

theorem runFrom_add (firstTime secondTime initial : V) :
    runFrom (firstTime+secondTime) initial =
      runFrom secondTime (runFrom firstTime initial) := by
  induction secondTime using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ secondTime ih => rw [←add_assoc, runFrom_succ, runFrom_succ, ih]

theorem runFrom_first (time initial : V) :
    runFrom (time+1) initial = runFrom time (stepValue initial) := by
  calc
    runFrom (time+1) initial = runFrom (1+time) initial := by rw [add_comm time 1]
    _ = runFrom time (runFrom 1 initial) := runFrom_add 1 time initial
    _ = runFrom time (stepValue initial) := by rw [runFrom_one]

/-- Every internal continuation of a halted code is that same complete code. -/
theorem runFrom_halted (time config : V) (hh : first config = 0) :
    runFrom time config = config := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact runFrom_zero config
  case succ time ih => rw [runFrom_succ, ih, step_halted config hh]

theorem runFrom_halt_state (time config : V) (hh : first config = 0) :
    first (runFrom time config) = 0 := by rw [runFrom_halted time config hh, hh]

/-- The arbitrary-initial evaluator exactly recovers the previously checked
blank evaluator, at every model time rather than only standard times. -/
theorem runFrom_blank (time : V) :
    runFrom time 1 = ArithmeticMachineRunPrefix246.run time := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ time ih =>
    rw [runFrom_succ, ArithmeticMachineRunPrefix246.run_succ, ih]

theorem runFrom_total (time initial : V) :
    ∃! out, runFromDef.val.Evalb ![out,time,initial] := by simp

/-- Computable standard-code iteration of the already checked all-code native
step; the internal graph and the ordinary Nat comparison are distinct facts. -/
def nativeRunFrom : Nat → Nat → Nat
  | 0, initial => initial
  | time+1, initial => nativeStep (nativeRunFrom time initial)

theorem runFrom_nat (time initial : Nat) : runFrom time initial = nativeRunFrom time initial := by
  induction time with
  | zero => simp [nativeRunFrom]
  | succ time ih => rw [runFrom_succ, ih, stepValue_nat]; rfl

theorem runFromDef_nat (out time initial : Nat) :
    runFromDef.val.Evalb ![out,time,initial] ↔ out = nativeRunFrom time initial := by
  simp [runFrom_nat]

end ISigma1
end SetTheory.BusyBeaver.ZFC.ArithmeticMachineRunFromPrefix246

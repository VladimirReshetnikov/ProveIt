import ConPAMachineStutter
import DiophantineConsistency.ArithmeticUnaryRecursion

/-! Iteration from arbitrary packed configurations in models of IΣ₁. -/

set_option autoImplicit false

namespace ConPA.Machine
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

def segmentBlueprint (T : Table) : PR.Blueprint 1 where
  zero := .mkSigma “y initial. y = initial”
  succ := .mkSigma “y previous time initial. !(stepDef T) y previous”

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def segmentConstruction (T : Table) : PR.Construction V (segmentBlueprint T) where
  zero parameters := parameters 0
  succ _ _ previous := step T previous
  zero_defined := .mk fun e => by simp [segmentBlueprint]
  succ_defined := .mk fun e => by simp [segmentBlueprint, stepDef_iff]

/-- The configuration after `time` steps starting from the given packed tape and control. -/
noncomputable def runFrom (T : Table) (time initial : V) : V :=
  (segmentConstruction T).result ![initial] time

theorem runFrom_definable (T : Table) : 𝚺₁-Function₂ (runFrom (V := V) T) :=
  (DiophantineConsistency.ArithmeticUnaryRecursion.result_defined
    (segmentBlueprint T) (segmentConstruction T)).to_definable

theorem runFrom_delta (T : Table) : 𝚫₁-Function₂ (runFrom (V := V) T) :=
  (DiophantineConsistency.ArithmeticUnaryRecursion.result_defined
    (segmentBlueprint T) (segmentConstruction T)).graph_delta.to_definable

@[simp] theorem runFrom_zero (T : Table) (initial : V) : runFrom T 0 initial = initial := by
  simp [runFrom, segmentConstruction]

@[simp] theorem runFrom_succ (T : Table) (time initial : V) :
    runFrom T (time + 1) initial = step T (runFrom T time initial) := by
  simp [runFrom, segmentConstruction]

theorem runFrom_blank (T : Table) (time : V) : runFrom T time 0 = run T time := by
  letI := runFrom_definable (V := V) T
  letI := Stutter.runDefinable (V := V) T
  induction time using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ time ih => rw [runFrom_succ, run_succ, ih]

/-- Concatenation of execution segments of arbitrary model-valued lengths. -/
theorem runFrom_add (T : Table) (a b initial : V) :
    runFrom T (a + b) initial = runFrom T b (runFrom T a initial) := by
  letI := runFrom_definable (V := V) T
  induction b using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ time ih => rw [← add_assoc, runFrom_succ, runFrom_succ, ih]

theorem run_add (T : Table) (a b : V) : run T (a + b) = runFrom T b (run T a) := by
  simpa only [runFrom_blank] using runFrom_add T a b (0 : V)

theorem runFrom_first (T : Table) (time initial : V) :
    runFrom T (time + 1) initial = runFrom T time (step T initial) := by
  rw [add_comm, runFrom_add]
  congr 1
  simpa only [zero_add, runFrom_succ, runFrom_zero] using
    (runFrom_succ T (0 : V) initial)

#print axioms runFrom_add
#print axioms run_add
end models
end ConPA.Machine

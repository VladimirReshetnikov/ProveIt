import BusyBeaver.ZFC.ArithmeticMachineRunFromRotation240
import BusyBeaver.ZFC.ArithmeticBootstrapRotation240

/-!
Finite-prefix transport for the exact source-rotation240 arithmetic evaluator.
Every time and configuration in the shift theorem is internal to an IΣ1 model.
Whole-configuration halt absorption handles a halt before the prefix ends.
The checked finite bootstrap specializes the shift to its literal seed code.
The fixed seed-halting sentence and its equivalence with blank halting do not
assert a register/scheduler simulation or an internal consistency equivalence.
The semantic shift follows ArithmeticMachinePrefixPrefix246; no raised proof
limits or new finite machine execution is used.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineRunFromRotation240
open ArithmeticMachineRunRotation240 (run)
open ArithmeticBootstrapRotation240 (bootCode internal_boot)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Two internal iteration blocks of the same step commute. -/
lemma runFrom_commute (t u initial : V) :
    runFrom t (runFrom u initial) = runFrom u (runFrom t initial) := by
  calc
    runFrom t (runFrom u initial) = runFrom (u+t) initial :=
      (runFrom_add u t initial).symm
    _ = runFrom (t+u) initial := by rw [add_comm u t]
    _ = runFrom u (runFrom t initial) := runFrom_add t u initial

/-- Halting is unchanged by any internal prefix, even one extending past a halt. -/
theorem halts_shift_iff (offset initial : V) :
    (∃ time : V, first (runFrom time initial) = 0) ↔
      (∃ time : V, first (runFrom time (runFrom offset initial)) = 0) := by
  constructor
  · rintro ⟨time, ht⟩
    refine ⟨time, ?_⟩
    rw [runFrom_commute time offset initial, runFrom_halted offset _ ht]
    exact ht
  · rintro ⟨time, ht⟩
    exact ⟨offset+time, by rw [runFrom_add]; exact ht⟩

/-- The blank run is recovered at initial code 1 at every internal model time. -/
theorem blank_shift_iff (offset : V) :
    (∃ time : V, first (run time) = 0) ↔
      (∃ time : V, first (runFrom time (run offset)) = 0) := by
  simpa only [runFrom_blank] using halts_shift_iff offset (1 : V)

/-- The exact 409691-step startup can be removed without a live-seed premise. -/
theorem blank_iff_seed_halts :
    (∃ time : V, first (run time) = 0) ↔
      (∃ time : V, first (runFrom time (bootCode : V)) = 0) := by
  simpa only [internal_boot] using blank_shift_iff (409691 : V)

/-- Evaluate the existing fixed blank-halting sentence in an arbitrary model. -/
theorem blankHaltingSentence_eval :
    ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] ↔
      ∃ time : V, first (run time) = 0 := by
  have h : ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] ↔
      ∃ time : V, (0 : V) = first (run time) := by
    simp [ArithmeticMachineRunRotation240.haltingSentence]
  exact h.trans (exists_congr fun _ => eq_comm)

/-- Fixed syntax for halting from an external numeral; time witnesses remain internal. -/
def haltingFromSentence (initial : Nat) : 𝚺₁.Sentence := .mkSigma
  “∃ time, ∃ config,
    !ArithmeticMachineRunFromRotation240.runFromDef config time
      !!(Semiterm.Operator.numeral ℒₒᵣ initial) ∧
    !ArithmeticCantor.firstDef 0 config”

theorem haltingFromSentence_eval (initial : Nat) :
    (haltingFromSentence initial).val.Evalb (M := V) ![] ↔
      ∃ time : V, first (runFrom time (initial : V)) = 0 := by
  have h : (haltingFromSentence initial).val.Evalb (M := V) ![] ↔
      ∃ time : V, (0 : V) = first (runFrom time (initial : V)) := by
    simp [haltingFromSentence, numeral_eq_natCast]
  exact h.trans (exists_congr fun _ => eq_comm)

/-- A single parameter-free Sigma1 sentence for the literal startup seed. -/
def seedHaltingSentence : 𝚺₁.Sentence := haltingFromSentence bootCode

theorem seedHaltingSentence_eval :
    seedHaltingSentence.val.Evalb (M := V) ![] ↔
      ∃ time : V, first (runFrom time (bootCode : V)) = 0 :=
  haltingFromSentence_eval bootCode

theorem blankSentence_iff_seedSentence :
    ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] ↔
      seedHaltingSentence.val.Evalb (M := V) ![] :=
  blankHaltingSentence_eval.trans
    (blank_iff_seed_halts.trans seedHaltingSentence_eval.symm)

/-- On ordinary Nat the seed sentence detects halting of the exact binary table. -/
theorem seedHaltingSentence_nat :
    seedHaltingSentence.val.Evalb (M := Nat) ![] ↔
      ∃ time, (machineRotation240.run time).state = none :=
  (blankSentence_iff_seedSentence (V := Nat)).symm.trans
    ArithmeticMachineRunRotation240.haltingSentence_nat

/-- Both sides use fixed syntax; the equivalence is an arithmetic sentence. -/
def startupEquivalenceSentence : ArithmeticSentence :=
  “!ArithmeticMachineRunRotation240.haltingSentence.val ↔ !seedHaltingSentence.val”

theorem startupEquivalenceSentence_true :
    startupEquivalenceSentence.Evalb (M := V) ![] := by
  simpa [startupEquivalenceSentence] using (blankSentence_iff_seedSentence (V := V))

theorem isigma1_proves_startup_equivalence : 𝗜𝚺₁ ⊢ startupEquivalenceSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (startupEquivalenceSentence_true (V := M))

theorem peano_proves_startup_equivalence : Peano ⊢ startupEquivalenceSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_startup_equivalence

end SetTheory.BusyBeaver.ZFC.ArithmeticStartupRotation240

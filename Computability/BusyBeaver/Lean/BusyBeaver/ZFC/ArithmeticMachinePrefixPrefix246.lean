import BusyBeaver.ZFC.ArithmeticMachineRunFromPrefix246
import BusyBeaver.ZFC.ArithmeticBootstrapPrefix246

/-!
Halting equivalence before and after any internal fixed prefix of the actual
contextual-fold246 arithmetic evaluator. The exact checked bootstrap specializes that
result to its literal numeric target. No unbounded register or scheduler
simulation is supplied by these prefix-composition theorems.
Adapted from ArithmeticMachinePrefixPerm252, using the checked246 startup.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachinePrefixPrefix246
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineRunFromPrefix246
open ArithmeticMachineRunPrefix246 (run)
open ArithmeticBootstrapPrefix246 (bootCode internal_boot)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Reordering two blocks of iterations of the same deterministic step. -/
lemma runFrom_commute (t u initial : V) :
    runFrom t (runFrom u initial) = runFrom u (runFrom t initial) := by
  calc
    runFrom t (runFrom u initial) = runFrom (u+t) initial :=
      (runFrom_add u t initial).symm
    _ = runFrom (t+u) initial := by rw [add_comm u t]
    _ = runFrom u (runFrom t initial) := runFrom_add t u initial

/-- A halt inside the prefix is handled by whole-configuration absorption.
No subtraction of clock bounds or assumed continuing prefix is needed. -/
theorem halts_after_prefix_iff (prefixTime initial : V) :
    (∃ time : V, first (runFrom time (runFrom prefixTime initial)) = 0) ↔
      (∃ time : V, first (runFrom time initial) = 0) := by
  constructor
  · rintro ⟨time, ht⟩
    exact ⟨prefixTime+time, by rw [runFrom_add]; exact ht⟩
  · rintro ⟨time, ht⟩
    refine ⟨time, ?_⟩
    rw [runFrom_commute time prefixTime initial, runFrom_halted prefixTime _ ht]
    exact ht

/-- The prefix time is an arbitrary internal model value. -/
theorem blank_after_prefix_iff (prefixTime : V) :
    (∃ time : V, first (runFrom time (run prefixTime)) = 0) ↔
      (∃ time : V, first (run time) = 0) := by
  simpa only [runFrom_blank] using halts_after_prefix_iff prefixTime (1 : V)

/-- The fixed numeral bootstrap may now be removed without a runtime premise. -/
theorem boot_halts_iff :
    (∃ time : V, first (runFrom time (bootCode : V)) = 0) ↔
      (∃ time : V, first (run time) = 0) := by
  simpa only [internal_boot] using blank_after_prefix_iff (410735 : V)

end SetTheory.BusyBeaver.ZFC.ArithmeticMachinePrefixPrefix246

import BusyBeaver.ZFC.ArithmeticCommandStep254
import BusyBeaver.ZFC.ArithmeticCommandWord254

/-!
Changing a raw command's rest pointer preserves its working-register effect.
All inputs range over arbitrary IOpen model elements. This local identity is
needed to compose word executions; no execution or scheduler theorem occurs.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandStepWord254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandWord254
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

lemma short_tag_iff (k : V) : k < 3 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  rw [← two_add_one_eq_three, lt_succ_iff_le, le_two_iff_eq_zero_or_one_or_two]

/-- Replacing the rest changes neither the command arguments nor its action,
even for the three short commands whose unused projections may change. -/
theorem step_replace (raw rest w : V) :
    stepValue (replaceValue raw rest) w = stepValue raw w := by
  by_cases hs : first raw < 3
  · rcases (short_tag_iff _).mp hs with h0 | h1 | h2
    · simp [stepValue, replaceValue, effectValue, h0]
    · simp [stepValue, replaceValue, effectValue, h1]
    · have h23 : (2 : V) < 3 := by
        rw [← two_add_one_eq_three, lt_succ_iff_le]
      simp [stepValue, replaceValue, effectValue, h2, h23]
  · simp [stepValue, replaceValue, hs]

/-- The rest pointer also leaves the halting condition unchanged. -/
theorem step_replace_eq_zero (raw rest w : V) :
    stepValue (replaceValue raw rest) w = 0 ↔ stepValue raw w = 0 := by
  rw [step_replace]

end SetTheory.BusyBeaver.ZFC.ArithmeticCommandStepWord254

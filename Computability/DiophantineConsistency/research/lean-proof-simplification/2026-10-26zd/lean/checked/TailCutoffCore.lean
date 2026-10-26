import Init

/-! Checked proof mechanisms only. The tile table and large repository
imports are replaced by explicit hypotheses; this is not a compilation
of CurrentSelectorTail2011. -/
namespace TailCutoffCore

theorem cutoff_duality (p c q w : Nat)
    (h : p < c ↔ q < w) : c ≤ p ↔ w ≤ q := by
  simpa only [Nat.not_lt] using not_congr h

/-- The exact production proof pattern, with upstream facts as hypotheses. -/
theorem tail_position_iff
    (position south weight : Fin 942 → Nat) (cutoff : Nat)
    (position_zero : position 0 = 0)
    (cutoff_position : position 866 = 459)
    (cutoff_weight : weight 866 = cutoff)
    (strict_order : ∀ i j, i ≠ 0 → j ≠ 0 →
      (position i < position j ↔ weight j < weight i))
    (threshold : ∀ i, weight i ≤ cutoff ↔ south i ≤ 45)
    (i : Fin 942) :
    459 ≤ position i ↔ i ≠ 0 ∧ south i ≤ 45 := by
  by_cases hi : i = 0
  · subst i
    simp only [position_zero, ne_eq, not_true_eq_false, false_and]
    decide
  · have hr := strict_order i 866 hi (by decide)
    rw [cutoff_position, cutoff_weight] at hr
    rw [and_iff_right hi, ← threshold]
    simpa only [Nat.not_lt] using not_congr hr

/-- A small elementary copy of the mathlib distributivity lemma used by
production. Its proof is present because this core imports only Init. -/
theorem mul_ite_nat (p : Prop) [Decidable p] (a b c : Nat) :
    a * (if p then b else c) = if p then a*b else a*c := by
  by_cases h : p
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- The exact conditional normalization, retaining finite successor indexing. -/
theorem selector_tail_succ
    (position south weight : Fin 942 → Nat)
    (tail : ∀ i, 459 ≤ position i ↔ i ≠ 0 ∧ south i ≤ 45)
    (j : Fin 941) :
    (if 459 ≤ position j.succ then 2 * weight j.succ else 0) =
      2 * (if south j.succ ≤ 45 then weight j.succ else 0) := by
  simp only [tail, ne_eq, Fin.succ_ne_zero, not_false_eq_true, true_and,
    mul_ite_nat, Nat.mul_zero]

#print axioms cutoff_duality
#print axioms tail_position_iff
#print axioms mul_ite_nat
#print axioms selector_tail_succ
end TailCutoffCore

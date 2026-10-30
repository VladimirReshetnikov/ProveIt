import DiophantineConsistency.ParsonsPositiveRule
/-! Joosten's three-disjunction reduction in the positive-predicate calculus. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPositiveGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsBasePositive ParsonsPositiveRule ParsonsGuard

def guard_result {T : Theory ℒₒᵣ} (φ : ArithmeticSemiformula ℕ 1) (E : Proposition ℒₒᵣ)
    (t : SyntacticTerm ℒₒᵣ) (hφ : Positive φ) (hE : Positive E)
    (hb : ParsonsPositiveRule.Proof T (base φ ⋎ E))
    (hs : ParsonsPositiveRule.Proof T (step (ParsonsGuard.guard φ E)))
    (hn : ParsonsPositiveRule.Proof T (∼(φ/[t]) ⋎ E)) : ParsonsPositiveRule.Proof T E := by
  have hb' : ParsonsPositiveRule.Proof T (base (ParsonsGuard.guard φ E)) := by simpa [base] using hb
  have ha : ParsonsPositiveRule.Proof T (∀⁰ (ParsonsGuard.guard φ E)) :=
    .induction (positive_guard hφ hE) hb' hs
  have ht : ParsonsPositiveRule.Proof T (φ/[t] ⋎ E) := by simpa using (Proof.specialize t ha)
  exact .mp (.mp (.logical (resolution (φ/[t]) E)) ht) hn

def three_disjunctions {T : Theory ℒₒᵣ} (φ : ArithmeticSemiformula ℕ 1) (E : Proposition ℒₒᵣ)
    (t : SyntacticTerm ℒₒᵣ) (hφ : Positive φ) (hE : Positive E)
    (hb : ParsonsPositiveRule.Proof T (base φ ⋎ E))
    (hs : ParsonsPositiveRule.Proof T (step φ ⋎ E))
    (hn : ParsonsPositiveRule.Proof T (∼(φ/[t]) ⋎ E)) : ParsonsPositiveRule.Proof T E :=
  guard_result φ E t hφ hE hb (.mp (.logical (guard_step_logic φ E)) hs) hn
end DiophantineConsistency.ParsonsPositiveGuard

import DiophantineConsistency.ParsonsPositiveRule
/-! A structural certificate that a particular unrestricted Parsons proof
uses positive induction predicates, and a restriction transformer. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPositiveCertificate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsBasePositive

def AllPositive {T : Theory ℒₒᵣ} : {φ : Proposition ℒₒᵣ} → ParsonsRule.Proof T φ → Prop
  | _, .logical _ => True
  | _, .axiom _ => True
  | _, .mp a b => AllPositive a ∧ AllPositive b
  | _, .generalize a => AllPositive a
  | _, .specialize _ a => AllPositive a
  | _, .induction (φ := φ) _ a b => Positive φ ∧ AllPositive a ∧ AllPositive b

def restrict {T : Theory ℒₒᵣ} : {φ : Proposition ℒₒᵣ} →
    (p : ParsonsRule.Proof T φ) → AllPositive p → ParsonsPositiveRule.Proof T φ
  | _, .logical d, _ => .logical d
  | _, .axiom h, _ => .axiom h
  | _, .mp a b, h => .mp (restrict a h.1) (restrict b h.2)
  | _, .generalize a, h => .generalize (restrict a h)
  | _, .specialize t a, h => .specialize t (restrict a h)
  | _, .induction _ a b, h => .induction h.1 (restrict a h.2.1) (restrict b h.2.2)

theorem toRule_allPositive {T : Theory ℒₒᵣ} {φ : Proposition ℒₒᵣ}
    (p : ParsonsPositiveRule.Proof T φ) : AllPositive (ParsonsPositiveRule.toRule p) := by
  induction p with
  | logical _ => trivial
  | «axiom» _ => trivial
  | mp _ _ ha hb => exact ⟨ha,hb⟩
  | generalize _ ha => exact ha
  | specialize _ _ ha => exact ha
  | induction h _ _ ha hb => exact ⟨h,ha,hb⟩

theorem restrict_roundtrip {T : Theory ℒₒᵣ} {φ : Proposition ℒₒᵣ}
    (p : ParsonsRule.Proof T φ) (h : AllPositive p) :
    ParsonsPositiveRule.toRule (restrict p h) = p := by
  induction p with
  | logical _ => rfl
  | «axiom» _ => rfl
  | mp a b ha hb => simp only [restrict, ParsonsPositiveRule.toRule]; rw [ha h.1, hb h.2]
  | generalize a ha => simp only [restrict, ParsonsPositiveRule.toRule]; rw [ha h]
  | specialize t a ha => simp only [restrict, ParsonsPositiveRule.toRule]; rw [ha h]
  | induction hh a b ha hb =>
    simp only [restrict, ParsonsPositiveRule.toRule]
    rw [ha h.2.1, hb h.2.2]
end DiophantineConsistency.ParsonsPositiveCertificate

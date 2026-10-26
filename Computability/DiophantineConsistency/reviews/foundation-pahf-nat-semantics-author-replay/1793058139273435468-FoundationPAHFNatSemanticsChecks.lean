import DiophantineConsistency.FoundationPAHFNatSemantics

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationPAHFNatSemanticsChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open SetTheory.PA FoundationPAHFSyntax FoundationPAHFNatSemantics

example (ee : ℕ → ℕ) (a b : Term) :
    Formula.Sat natStructure ee (ltFormula a b) ↔
      Term.eval natStructure ee a < Term.eval natStructure ee b := sat_ltFormula ee a b

/-- Strictness includes the zero and equal-input boundary cases. -/
example : ¬ Formula.Sat natStructure (fun _ => 0) (ltFormula .zero .zero) := by
  rw [sat_ltFormula]
  exact Nat.lt_irrefl 0

example : Formula.Sat natStructure (fun _ => 0) (ltFormula .zero (.succ .zero)) := by
  rw [sat_ltFormula]
  exact Nat.zero_lt_one

/-- One bound slot and a nontrivial free term survive two additional binders. -/
def nested : Semiformula ℒₒᵣ ℕ 1 :=
  ∀⁰ ∃⁰ ((Semiformula.rel .eq ![#0, #1]) ⋏ (Semiformula.rel .eq ![#2, &4]))

example (ee : ℕ → ℕ) :
    Formula.Sat natStructure ee (formulaAux
      (fun _ => .add (.var 7) (.succ .zero)) (fun j => .var (11+j)) nestedᴺ) ↔
      ee 7 + 1 = ee 15 := by
  rw [sat_formulaAux_GG]
  change (∀ x : ℕ, ∃ y : ℕ, y = x ∧ ee 7 + 1 = ee 15) ↔ _
  constructor
  · intro h; exact (h 0).choose_spec.2
  · intro h x; exact ⟨x, rfl, h⟩

example (φ : ArithmeticSentence) (ee ff : ℕ → ℕ) :
    Formula.Sat natStructure ee (sentence φᴺ) ↔
      Formula.Sat natStructure ff (sentence φᴺ) :=
  (sat_sentence_GG φ ee).trans (sat_sentence_GG φ ff).symm

example (ee : ℕ → ℕ) : ¬ Formula.Sat natStructure ee (sentence (⊥ : ArithmeticSentence)ᴺ) :=
  (sat_sentence_GG ⊥ ee).mp

#print axioms eval_termAux
#print axioms sat_ltFormula
#print axioms eval_liftBound
#print axioms eval_liftFree
#print axioms sat_formulaAux_GG
#print axioms sat_formula_GG
#print axioms sat_sentence_GG

end DiophantineConsistency.FoundationPAHFNatSemanticsChecks

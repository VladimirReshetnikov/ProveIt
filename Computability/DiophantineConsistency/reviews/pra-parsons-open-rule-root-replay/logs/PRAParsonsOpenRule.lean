import DiophantineConsistency.PRAInductionRule
import DiophantineConsistency.ParsonsRule

/-! Link the candidate-PRA induction rule to the Parsons-rule interface. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAParsonsOpenRule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory

/-- The candidate theory admits the parameterized Parsons-rule step for open
matrices. This does not assert admissibility for all Σ₁ matrices. -/
theorem parsons_open_induction_rule (φ : Semiproposition language 1) (hOpen : φ.Open)
    (hBase : PRA ⊢ (ParsonsRule.base φ).univCl)
    (hStep : PRA ⊢ (ParsonsRule.step φ).univCl) :
    PRA ⊢ (∀⁰ φ).univCl := by
  exact PRAInductionRule.open_induction_rule φ hOpen hBase hStep

end DiophantineConsistency.PRAParsonsOpenRule

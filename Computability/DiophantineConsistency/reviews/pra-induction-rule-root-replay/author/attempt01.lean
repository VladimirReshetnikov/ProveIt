import DiophantineConsistency.PRAOpenInduction

/-! Candidate PRA's parameterized quantifier-free induction rule. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAInductionRule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory

def base (φ : Semiproposition language 1) : Proposition language := “!φ 0”
def step (φ : Semiproposition language 1) : Proposition language := “∀ x, !φ x → !φ (x + 1)”

/-- For an open matrix, the standard induction rule with arbitrary free
parameters is admissible in candidate PRA. -/
theorem open_induction_rule (φ : Semiproposition language 1) (hOpen : φ.Open)
    (hBase : PRA ⊢ (base φ).univCl) (hStep : PRA ⊢ (step φ).univCl) :
    PRA ⊢ (∀⁰ φ).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  have hb := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hBase
  have hs := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hStep
  have hi := Theory.models (T := PRA) M (Or.inl (Or.inr ⟨φ, hOpen, rfl⟩))
  simp only [models_iff, Semiformula.eval_univCl] at hb hs hi ⊢
  intro e
  have hr := hi e
  change (succInd φ).Eval ![] e at hr
  simp [succInd, Semiformula.eval_substs] at hr
  have hb' := hb e
  have hs' := hs e
  simp [base, Semiformula.eval_substs] at hb'
  simp [step, Semiformula.eval_substs] at hs'
  exact hr hb' hs'

end DiophantineConsistency.PRAInductionRule

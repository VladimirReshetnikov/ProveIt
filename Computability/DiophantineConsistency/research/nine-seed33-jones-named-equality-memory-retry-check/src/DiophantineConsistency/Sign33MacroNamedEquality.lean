import DiophantineConsistency.Sign33MacroNamedVars

/-! Candidate exact Lean recipe-to-named-expression evaluator equality. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroNamedEquality
open Sign33MacroVarsBd Sign33MacroVarsOutput

theorem recipe_eq_expression_eval {R : Type*} [CommRing R] (a : Fin 9 → R) :
    Sign33MacroRecipe.recipe.values a (Fin.last 44) = Sign33IPRAEndpoint.expression.evalRing a := by
  calc
    Sign33MacroRecipe.recipe.values a (Fin.last 44) =
        RefinedPair.value ((vars a).rad 0) ((vars a).rad 1) ((vars a).wt 0) ((vars a).wt 1)
          (a ⟨8, by decide⟩) (vars a).dvsr (vars a).dvnd (vars a).marg := recipe_eq_refined a
    _ = RefinedPair.value ((namedVars a).rad 0) ((namedVars a).rad 1) ((namedVars a).wt 0) ((namedVars a).wt 1)
          (a ⟨8, by decide⟩) (namedVars a).dvsr (namedVars a).dvnd (namedVars a).marg := by rw [vars_eq_named]
    _ = Sign33IPRAEndpoint.expression.evalRing a := (Sign33NamedFormula.eval_current a).symm

#print axioms recipe_eq_expression_eval
end DiophantineConsistency.Sign33MacroNamedEquality

module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRealizationSyntax
public import M6PA.Calibration.NumericPAeqFormulaLogicalCertificate
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem environment_and {s r b f a w p q:V} (h:FormulaEnvironment s r b f a w (qqAnd p q)):
    FormulaEnvironment s r b f a w p ∧ FormulaEnvironment s r b f a w q := by
  have hpq := IsSemiformula.and.mp h.2.2.2.1
  have hs := (freeSupported_and hpq.1.isUFormula hpq.2.isUFormula).mp h.2.2.2.2.2.1
  exact ⟨⟨h.1,h.2.1,h.2.2.1,hpq.1,h.2.2.2.2.1,hs.1,h.2.2.2.2.2.2⟩,
    ⟨h.1,h.2.1,h.2.2.1,hpq.2,h.2.2.2.2.1,hs.2,h.2.2.2.2.2.2⟩⟩
theorem environment_or {s r b f a w p q:V} (h:FormulaEnvironment s r b f a w (qqOr p q)):
    FormulaEnvironment s r b f a w p ∧ FormulaEnvironment s r b f a w q := by
  have hpq := IsSemiformula.or.mp h.2.2.2.1
  have hs := (freeSupported_or hpq.1.isUFormula hpq.2.isUFormula).mp h.2.2.2.2.2.1
  exact ⟨⟨h.1,h.2.1,h.2.2.1,hpq.1,h.2.2.2.2.1,hs.1,h.2.2.2.2.2.2⟩,
    ⟨h.1,h.2.1,h.2.2.1,hpq.2,h.2.2.2.2.1,hs.2,h.2.2.2.2.2.2⟩⟩
theorem formulaComparison_and {s r b f a w p q:V} (h:FormulaEnvironment s r b f a w (qqAnd p q)):
    formulaComparison b f a w (qqAnd p q)=
      biCode (qqAnd (substitutedFormula b f w p) (substitutedFormula b f w q))
        (qqAnd (originalFormula a f p) (originalFormula a f q)) := by
  have hpq := IsSemiformula.and.mp h.2.2.2.1
  simp only [formulaComparison,substitutedFormula,originalFormula,biCode,
    substs_and hpq.1.isUFormula hpq.2.isUFormula,
    formulaSyntax_and _ _ _ (hpq.1.subst h.2.2.2.2.1).isUFormula (hpq.2.subst h.2.2.2.2.1).isUFormula,
    formulaSyntax_and _ _ _ hpq.1.isUFormula hpq.2.isUFormula]
theorem formulaComparison_or {s r b f a w p q:V} (h:FormulaEnvironment s r b f a w (qqOr p q)):
    formulaComparison b f a w (qqOr p q)=
      biCode (qqOr (substitutedFormula b f w p) (substitutedFormula b f w q))
        (qqOr (originalFormula a f p) (originalFormula a f q)) := by
  have hpq := IsSemiformula.or.mp h.2.2.2.1
  simp only [formulaComparison,substitutedFormula,originalFormula,biCode,
    substs_or hpq.1.isUFormula hpq.2.isUFormula,
    formulaSyntax_or _ _ _ (hpq.1.subst h.2.2.2.2.1).isUFormula (hpq.2.subst h.2.2.2.2.1).isUFormula,
    formulaSyntax_or _ _ _ hpq.1.isUFormula hpq.2.isUFormula]
#print axioms environment_and
#print axioms formulaComparison_and
#print axioms formulaComparison_or
end M6.PA.NumericPAeqFormulaRealization


module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRealizationConnectiveSyntax
public import M6PA.Calibration.NumericPAeqValueCertificatePair
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical NumericPAeqValueTotality NumericPAeqValueVectorRealization
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
def FormulaSupply (p:V):Prop :=
  ∀s r b f a w,FormulaEnvironment s r b f a w p→∀native lo z,
    FormulaCovered 0 native lo z (formulaCode s r b f a w p)→
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (formulaCode s r b f a w p)+1
theorem formula_and_step {p q:V} (ihp:FormulaSupply (V:=V) p) (ihq:FormulaSupply (V:=V) q):
    FormulaSupply (V:=V) (qqAnd p q) := by
  intro s r b f a w h native lo z hc
  obtain ⟨hp,hq⟩ := environment_and h
  apply source_implication_compose (vectorInput s r b f a w)
    (qqAnd (formulaComparison b f a w p) (formulaComparison b f a w q))
    (formulaComparison b f a w (qqAnd p q)) native lo z (input_valid h)
    (IsSemiformula.and.mpr ⟨formulaComparison_valid hp,formulaComparison_valid hq⟩) (formulaComparison_valid h) hc
  · intro native lo z hc
    apply source_implication_pair _ _ _ native lo z (input_valid h) (formulaComparison_valid hp) (formulaComparison_valid hq) hc
    · intro native lo z hc; exact ihp s r b f a w hp native lo z hc
    · intro native lo z hc; exact ihq s r b f a w hq native lo z hc
  · intro native lo z hc
    rw [formulaComparison_and h] at hc ⊢
    exact andBi_requested_certificate _ _ _ _ native lo z
      (substitutedFormula_valid hp) (originalFormula_valid hp) (substitutedFormula_valid hq) (originalFormula_valid hq) hc
theorem formula_or_step {p q:V} (ihp:FormulaSupply (V:=V) p) (ihq:FormulaSupply (V:=V) q):
    FormulaSupply (V:=V) (qqOr p q) := by
  intro s r b f a w h native lo z hc
  obtain ⟨hp,hq⟩ := environment_or h
  apply source_implication_compose (vectorInput s r b f a w)
    (qqAnd (formulaComparison b f a w p) (formulaComparison b f a w q))
    (formulaComparison b f a w (qqOr p q)) native lo z (input_valid h)
    (IsSemiformula.and.mpr ⟨formulaComparison_valid hp,formulaComparison_valid hq⟩) (formulaComparison_valid h) hc
  · intro native lo z hc
    apply source_implication_pair _ _ _ native lo z (input_valid h) (formulaComparison_valid hp) (formulaComparison_valid hq) hc
    · intro native lo z hc; exact ihp s r b f a w hp native lo z hc
    · intro native lo z hc; exact ihq s r b f a w hq native lo z hc
  · intro native lo z hc
    rw [formulaComparison_or h] at hc ⊢
    exact orBi_requested_certificate _ _ _ _ native lo z
      (substitutedFormula_valid hp) (originalFormula_valid hp) (substitutedFormula_valid hq) (originalFormula_valid hq) hc
#print axioms formula_and_step
#print axioms formula_or_step
end M6.PA.NumericPAeqFormulaRealization


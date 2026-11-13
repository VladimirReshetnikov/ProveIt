module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRealizationBinderChild
public import M6PA.Calibration.FoundationRelationalSequentRequestedUniversal
public import M6PA.Calibration.NumericPAeqFormulaQuantifierTemplatesCertificate
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical NumericPAeqValueTotality NumericPAeqValueVectorRealization
open NumericPAeqFormulaQuantifierTemplates
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem uniform_certificate {s r b f a w p:V}
    (h:FormulaEnvironment s r b f a w (qqAll p)) (ih:FormulaSupply (V:=V) p)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (qqAll (uniformMatrix s r b f a w p))):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (qqAll (uniformMatrix s r b f a w p))+1 := by
  exact requested_universal_certificate _ native lo z (uniformMatrix_valid h) hc
    (uniformMatrix_free_certificate h ih)
theorem formula_all_step {p:V} (ih:FormulaSupply (V:=V) p):FormulaSupply (qqAll p) := by
  intro s r b f a w h native lo z hc
  apply source_certificate_mp (qqAll (uniformMatrix s r b f a w p)) (formulaCode s r b f a w (qqAll p)) native lo z
    (IsSemiformula.all.mpr (by simpa using uniformMatrix_valid h)) (formulaCode_valid h) hc
  · exact uniform_certificate h ih
  · intro native lo z hc
    have he : imp language (qqAll (uniformMatrix s r b f a w p)) (formulaCode s r b f a w (qqAll p)) =
        allTemplateCode (vectorInput s r b f a w) (⌜NumericPAeqTerm.domainTemplate⌝:V)
          (binderLeft b f w p) (binderRight a f p) := by
      simp only [formulaCode,formulaComparison_all h,uniformMatrix,allTemplateCode,uniformPremiseCode,guardedAllCode]
    rw [he] at hc ⊢
    exact allTemplate_requested_certificate _ _ _ _ native lo z (input_valid h)
      (by simpa using Semiformula.quote_isSemiformula (V:=V) NumericPAeqTerm.domainTemplate)
      (binderLeft_valid h) (binderRight_valid h) hc
theorem formula_exs_step {p:V} (ih:FormulaSupply (V:=V) p):FormulaSupply (qqExs p) := by
  intro s r b f a w h native lo z hc
  have hh := environment_exs_all h
  apply source_certificate_mp (qqAll (uniformMatrix s r b f a w p)) (formulaCode s r b f a w (qqExs p)) native lo z
    (IsSemiformula.all.mpr (by simpa using uniformMatrix_valid hh)) (formulaCode_valid h) hc
  · exact uniform_certificate hh ih
  · intro native lo z hc
    have he : imp language (qqAll (uniformMatrix s r b f a w p)) (formulaCode s r b f a w (qqExs p)) =
        exsTemplateCode (vectorInput s r b f a w) (⌜NumericPAeqTerm.domainTemplate⌝:V)
          (binderLeft b f w p) (binderRight a f p) := by
      simp only [formulaCode,formulaComparison_exs h,uniformMatrix,exsTemplateCode,uniformPremiseCode,guardedExsCode]
    rw [he] at hc ⊢
    exact exsTemplate_requested_certificate _ _ _ _ native lo z (input_valid h)
      (by simpa using Semiformula.quote_isSemiformula (V:=V) NumericPAeqTerm.domainTemplate)
      (binderLeft_valid hh) (binderRight_valid hh) hc
#print axioms uniform_certificate
#print axioms formula_all_step
#print axioms formula_exs_step
end M6.PA.NumericPAeqFormulaRealization


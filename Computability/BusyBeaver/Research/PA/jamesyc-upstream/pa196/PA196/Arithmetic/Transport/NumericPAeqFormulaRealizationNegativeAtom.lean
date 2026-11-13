module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaRealizationConnectives
public import PA196.Arithmetic.Transport.NumericPAeqFormulaLogicalNegation
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical NumericPAeqValueTotality NumericPAeqValueVectorRealization
open RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem environment_nrel_rel {s r b f a w k fn ts:V}
    (h:FormulaEnvironment s r b f a w (qqNRel k fn ts)):
    FormulaEnvironment s r b f a w (qqRel k fn ts) := by
  have hv := IsSemiformula.nrel.mp h.2.2.2.1
  exact ⟨h.1,h.2.1,h.2.2.1,IsSemiformula.rel.mpr hv,h.2.2.2.2.1,
    (freeSupported_rel hv.1 hv.2.isUTerm).mpr ((freeSupported_nrel hv.1 hv.2.isUTerm).mp h.2.2.2.2.2.1),
    h.2.2.2.2.2.2⟩
theorem formulaComparison_nrel {s r b f a w k fn ts:V}
    (h:FormulaEnvironment s r b f a w (qqNRel k fn ts)):
    formulaComparison b f a w (qqNRel k fn ts)=
      biCode (neg language (substitutedFormula b f w (qqRel k fn ts)))
        (neg language (originalFormula a f (qqRel k fn ts))) := by
  have hv := IsSemiformula.nrel.mp h.2.2.2.1
  simp only [formulaComparison,substitutedFormula,originalFormula,biCode,
    substs_nrel hv.1 hv.2.isUTerm,substs_rel hv.1 hv.2.isUTerm,
    formulaSyntax_nrel _ _ _ _ hv.1 hv.2.isUTerm,formulaSyntax_rel _ _ _ _ hv.1 hv.2.isUTerm,
    formulaSyntax_nrel _ _ _ _ hv.1 (h.2.2.2.2.1.termSubstVec hv.2).isUTerm,
    formulaSyntax_rel _ _ _ _ hv.1 (h.2.2.2.2.1.termSubstVec hv.2).isUTerm]
theorem formula_nrel_of_rel {k fn ts:V} (hrel:FormulaSupply (V:=V) (qqRel k fn ts)):
    FormulaSupply (qqNRel k fn ts) := by
  intro s r b f a w h native lo z hc
  have hh := environment_nrel_rel h
  apply source_implication_compose _ (formulaComparison b f a w (qqRel k fn ts)) _ native lo z
    (input_valid h) (formulaComparison_valid hh) (formulaComparison_valid h) hc
  · exact hrel s r b f a w hh
  · intro native lo z hc
    rw [formulaComparison_nrel h] at hc ⊢
    exact negBi_requested_certificate _ _ native lo z (substitutedFormula_valid hh) (originalFormula_valid hh) hc
#print axioms environment_nrel_rel
#print axioms formulaComparison_nrel
#print axioms formula_nrel_of_rel
end PA196.Arithmetic.Transport.NumericPAeqFormulaRealization


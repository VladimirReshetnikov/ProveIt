module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaEqualityValueShape
public import M6PA.Calibration.NumericPAeqFormulaRealizationAtomTransport
public import M6PA.Calibration.NumericPAeqFormulaRealizationConnectives
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical NumericPAeqValueTotality NumericPAeqValueVectorRealization
open NumericPAeqSupportedVectorRealization NumericPAeqFormulaEqualityValueShape
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem formulaComparison_rel_two {s r b f a w t u:V}
    (ht:SupportedVectorEnvironment s r b f a w t) (hu:SupportedVectorEnvironment s r b f a w u):
    formulaComparison b f a w (qqRel 2 0 (t∷(u∷0)))=atomComparison b f a w t u := by
  have hts : IsUTermVec Presentation.language (2:V) (t∷(u∷0)) := by simp [ht.2.2.2.1.isUTerm,hu.2.2.2.1.isUTerm]
  have hl := substituted_environment ht
  have hr := substituted_environment hu
  simp only [formulaComparison,substitutedFormula,originalFormula,
    substs_rel (show Presentation.language.IsRel (2:V) 0 by simp) hts,
    termSubstVec_cons₂ ht.2.2.2.1.isUTerm hu.2.2.2.1.isUTerm,
    equality_atom_value_shape hl.1 hl.2.1 hl.2.2.1 hr.2.2.1 hl.2.2.2 hr.2.2.2,
    equality_atom_value_shape ht.2.2.1 ht.2.1 ht.2.2.2.1 hu.2.2.2.1 ht.2.2.2.2.2.1 hu.2.2.2.2.2.1,
    atomComparison,biCode]
theorem formula_rel_supply (k fn ts:V):FormulaSupply (V:=V) (qqRel k fn ts) := by
  intro s r b f a w h native lo z hc
  have hv := IsSemiformula.rel.mp h.2.2.2.1
  obtain ⟨hk,hn⟩ := (Presentation.source_relations k fn).mp hv.1
  subst k; subst fn
  obtain ⟨t,u,_,_,he⟩ := IsUTermVec.two_iff.mp hv.2.isUTerm
  subst ts
  have ht : IsSemiterm Presentation.language s t := by simpa using hv.2.nth (show (0:V)<2 by simp)
  have hu : IsSemiterm Presentation.language s u := by simpa using hv.2.nth (show (1:V)<2 by simp)
  have hs := (freeSupported_rel hv.1 hv.2.isUTerm).mp h.2.2.2.2.2.1
  have ht' := term_environment h ht (by simpa using hs 0 (by simp))
  have hu' := term_environment h hu (by simpa using hs 1 (by simp))
  have he := formulaComparison_rel_two ht' hu'
  simp only [formulaCode,he] at hc ⊢
  exact atomComparison_supply ht' hu' native lo z hc
#print axioms formulaComparison_rel_two
#print axioms formula_rel_supply
end M6.PA.NumericPAeqFormulaRealization


module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqUniversalContextUniform
public import M6PA.Calibration.NumericPAeqUniversalContextSyntax
public import M6PA.Calibration.NumericPAeqUniversalContextTemplateCertificate
@[expose] public section
namespace M6.PA.NumericPAeqUniversalContext
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqInductionInterpretation NumericPAeqValueTotality
open NumericPAeqTerm (targetShiftTerms)
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem universal_context_requested_certificate {f p S:V}
    (hf:IsSemitermVec language (len f) 0 f) (hp:IsSemiformula Presentation.language 1 p)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hS:IsFormula language S)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (contextRuleCode f p S))
    (child:∀g l z,FormulaCovered 0 g l z (imp language
      (freeDomain (qqFvar 0∷targetShiftTerms f))
      (qqOr (free language (property f p)) (shift language S)))→
      ∃code,verifyValue code=translate (parameters 0 g l z) (imp language
        (freeDomain (qqFvar 0∷targetShiftTerms f))
        (qqOr (free language (property f p)) (shift language S)))+1):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (contextRuleCode f p S)+1 :=by
  have hH:=freeDomain_valid hf
  have hP:=property_valid hf hp hs
  have hD:IsSemiformula language 1 (⌜NumericPAeqTerm.domainTemplate⌝:V):=by simp
  have hU:IsFormula language (qqAll (contextMatrix f p S)):=by
    apply IsSemiformula.all.mpr
    simpa using contextMatrix_valid hf hp hs hS
  apply source_certificate_mp (qqAll (contextMatrix f p S)) (contextRuleCode f p S)
    native lo z hU (contextRuleCode_valid hf hp hs hS) hc
  · intro g l z hc
    exact context_uniform_requested_certificate hf hp hs hS g l z hc child
  · intro g l z hc
    have he:imp language (qqAll (contextMatrix f p S)) (contextRuleCode f p S)=
        NumericPAeqUniversalContextTemplate.contextCode (freeDomain f) S
          (⌜NumericPAeqTerm.domainTemplate⌝:V) (property f p):=by
      rw [contextRuleCode,universalFormula_eq hp]
      rfl
    rw [he] at hc ⊢
    exact NumericPAeqUniversalContextTemplate.context_requested_certificate _ _ _ _ g l z hH hS hD hP hc
#print axioms universal_context_requested_certificate
end M6.PA.NumericPAeqUniversalContext


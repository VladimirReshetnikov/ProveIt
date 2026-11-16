module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceShape
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceSuccessorCalibration
public import M6PA.Calibration.NumericPAeqValueSuccessorShape
public import M6PA.Calibration.NumericPAeqTermSupportedBoundInstance
public import M6PA.Calibration.NumericPAeqSupportedValueCoherenceSyntax
public import PA196.Arithmetic.Transport.NumericPAeqValueDomainProjection
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqSupportedValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence RelationalPredicateBinary
open NumericPAeqSupportedValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem valuePredicate_valid {s b f t:V} (h:SupportedValueEnvironment s b f t):
    IsSemiformula language 1 (valuePredicate b f t) := by
  have hb : IsSemitermVec language s 1 b := by simpa [shiftTerms_zero_arity h.1] using shiftTerms_isSemitermVec h.1
  have hf : IsSemitermVec language (len f) 1 f := by simpa [shiftTerms_zero_arity h.2.1] using shiftTerms_isSemitermVec h.2.1
  apply valueSyntax_supported_isSemiformula
  refine ⟨?_,h.2.2.1,?_⟩
  · simpa [ParametersValid] using And.intro hb (And.intro hf (show IsSemiterm language 1 (qqBvar (0:V)) by simp))
  · simpa using h.2.2.2

theorem comparison_pairwise {s b c f g t:V} (h:SupportedCoherenceEnvironment s b c f g t):
    comparisonCode b c f g t=pairwiseCode (valuePredicate b f t) (valuePredicate c g t) := by
  unfold comparisonCode pairwiseCode valuePredicate
  rw [valueSyntax_supported_bound_instance h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2
      (show IsSemiterm language 2 (qqBvar 1) by simp),
    valueSyntax_supported_bound_instance h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      (show IsSemiterm language 2 (qqBvar 0) by simp)]

theorem comparison_successor {s b c f g t:V} (h:SupportedCoherenceEnvironment s b c f g t):
    comparisonCode b c f g (qqFunc 1 1 (t∷0))=
      successorComparisonCode (valuePredicate b f t) (valuePredicate c g t) := by
  simp only [comparisonCode,successorComparisonCode,valuePredicate,
    valueSyntax_successor _ _ h.1.2.2.1.isUTerm,parameters_result,
    childParameters_zero_environments h.1.1 h.1.2.1,
    childParameters_zero_environments h.2.1 h.2.2.1]

theorem valuePredicate_payload {s b f t:V} (h:SupportedValueEnvironment s b f t):
    ∃P:SF (V:=V) 1,valuePredicate b f t=(RelationalPredicateBinary.domain (V:=V)).val ^⋏ P.val := by
  obtain ⟨tail,he⟩ := valueSyntax_domain_shape (parameters b f (qqBvar (0:V))) t h.2.2.1.isUTerm
  have hv := valuePredicate_valid h
  change valuePredicate b f t=_ at he
  simp only [parameters_result] at he
  have hd : domainCode (qqBvar (0:V))=(RelationalPredicateBinary.domain (V:=V)).val := by
    change subst language (qqBvar 0 ∷ 0) (RelationalPredicateBinary.domain (V:=V)).val=_
    exact congrArg Bootstrapping.Semiformula.val (Bootstrapping.Semiformula.subst_eq_self₁ (RelationalPredicateBinary.domain (V:=V)))
  rw [hd] at he
  rw [he] at hv
  exact ⟨⟨tail,by simpa using (IsSemiformula.and.mp hv).2⟩,he⟩
#print axioms valuePredicate_valid
#print axioms comparison_pairwise
#print axioms comparison_successor
#print axioms valuePredicate_payload
end PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence


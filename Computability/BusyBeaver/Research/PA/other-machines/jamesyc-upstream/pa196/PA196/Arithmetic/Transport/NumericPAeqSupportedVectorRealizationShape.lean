module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationSyntax
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceBinaryShape
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence NumericPAeqValueVectorRealization
open NumericPAeqSupportedValueTotality NumericPAeqSupportedValueCoherence
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem vectorComparison_explicit {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t):
    vectorComparison b f a w t = qqAll (qqAll (imp language
      (qqAnd (valueSyntax (parameters b f (qqBvar 1)) (termSubst Presentation.language w t))
        (valueSyntax (parameters a f (qqBvar 0)) t)) (NumericPAeqValueIsoGuard.isoCode (qqBvar 1) (qqBvar 0)))) := by
  have hl := substituted_environment h
  have hr := original_environment h
  unfold vectorComparison pairwiseCode valuePredicate
  rw [valueSyntax_supported_bound_instance hl.1 hl.2.1 hl.2.2.1 hl.2.2.2 (show IsSemiterm language 2 (qqBvar 1) by simp),
    valueSyntax_supported_bound_instance hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 (show IsSemiterm language 2 (qqBvar 0) by simp)]
theorem vectorComparison_successor {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w (qqFunc 1 1 (t∷0))):
    vectorComparison b f a w (qqFunc 1 1 (t∷0)) =
      successorComparisonCode (valuePredicate b f (termSubst Presentation.language w t)) (valuePredicate a f t) := by
  have hv := IsSemiterm.func.mp h.2.2.2.1
  have ht := IsSemitermVec.singleton.mp hv.2
  rw [vectorComparison_explicit h]
  rw [termSubst_func hv.1 hv.2.isUTerm,termSubstVec_cons₁ ht.isUTerm]
  simp only [successorComparisonCode,valuePredicate,valueSyntax_successor _ _ ht.isUTerm,
    valueSyntax_successor _ _ (h.2.2.2.2.1.termSubst ht).isUTerm,parameters_result,
    childParameters_zero_environments h.1 h.2.1,childParameters_zero_environments h.2.2.1 h.2.1]

theorem vectorComparison_addition {s r b f a w t v:V} (h:SupportedVectorEnvironment s r b f a w (qqFunc 2 2 (t∷(v∷0)))):
    vectorComparison b f a w (qqFunc 2 2 (t∷(v∷0))) =
      pairwiseCode (binaryOutputCode additionTemplate (valuePredicate b f (termSubst Presentation.language w t)) (valuePredicate b f (termSubst Presentation.language w v)))
        (binaryOutputCode additionTemplate (valuePredicate a f t) (valuePredicate a f v)) := by
  have hv := IsSemiterm.func.mp h.2.2.2.1
  have htv := IsSemitermVec.doubleton.mp hv.2
  have ht : SupportedVectorEnvironment s r b f a w t := by simpa using vectorEnvironment_at h (show (0:V)<2 by simp)
  have hv' : SupportedVectorEnvironment s r b f a w v := by simpa using vectorEnvironment_at h (show (1:V)<2 by simp)
  unfold vectorComparison
  rw [termSubst_func hv.1 hv.2.isUTerm,termSubstVec_cons₂ htv.1.isUTerm htv.2.isUTerm,
    NumericPAeqSupportedValueCoherence.valuePredicate_addition (substituted_environment ht) (substituted_environment hv'),
    NumericPAeqSupportedValueCoherence.valuePredicate_addition (original_environment ht) (original_environment hv')]
theorem vectorComparison_multiplication {s r b f a w t v:V} (h:SupportedVectorEnvironment s r b f a w (qqFunc 2 3 (t∷(v∷0)))):
    vectorComparison b f a w (qqFunc 2 3 (t∷(v∷0))) =
      pairwiseCode (binaryOutputCode multiplicationTemplate (valuePredicate b f (termSubst Presentation.language w t)) (valuePredicate b f (termSubst Presentation.language w v)))
        (binaryOutputCode multiplicationTemplate (valuePredicate a f t) (valuePredicate a f v)) := by
  have hv := IsSemiterm.func.mp h.2.2.2.1
  have htv := IsSemitermVec.doubleton.mp hv.2
  have ht : SupportedVectorEnvironment s r b f a w t := by simpa using vectorEnvironment_at h (show (0:V)<2 by simp)
  have hv' : SupportedVectorEnvironment s r b f a w v := by simpa using vectorEnvironment_at h (show (1:V)<2 by simp)
  unfold vectorComparison
  rw [termSubst_func hv.1 hv.2.isUTerm,termSubstVec_cons₂ htv.1.isUTerm htv.2.isUTerm,
    NumericPAeqSupportedValueCoherence.valuePredicate_multiplication (substituted_environment ht) (substituted_environment hv'),
    NumericPAeqSupportedValueCoherence.valuePredicate_multiplication (original_environment ht) (original_environment hv')]
#print axioms vectorComparison_explicit
#print axioms vectorComparison_successor
#print axioms vectorComparison_addition
#print axioms vectorComparison_multiplication
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization

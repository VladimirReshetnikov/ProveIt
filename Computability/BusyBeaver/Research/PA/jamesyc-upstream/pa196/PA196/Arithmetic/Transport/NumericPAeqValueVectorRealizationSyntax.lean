module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueRealizationGuardValidity
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceShape
public import M6PA.Calibration.NumericPAeqTermVectorSubstInstance
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqValueVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
def VectorEnvironment (s r b f a w t:V):Prop :=
  IsSemitermVec language r 0 b ∧ IsSemitermVec language (len f) 0 f ∧
  IsSemitermVec language s 0 a ∧ IsSemiterm Presentation.language s t ∧
  IsSemitermVec Presentation.language s r w ∧ t≤len f ∧ ∀i<s,nth w i≤len f
noncomputable def vectorInput (s r b f a w:V):V :=
  qqAnd (inputDomain r b f) (qqAnd (inputDomain s a f) (NumericPAeqValueRealizationGuard.guard b f w a s))
noncomputable def vectorComparison (b f a w t:V):V :=
  pairwiseCode (valuePredicate b f (termSubst Presentation.language w t)) (valuePredicate a f t)
noncomputable def vectorCode (s r b f a w t:V):V := imp language (vectorInput s r b f a w) (vectorComparison b f a w t)
theorem original_environment {s r b f a w t:V} (h:VectorEnvironment s r b f a w t):ValueEnvironment s a f t :=
  ⟨h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2.2.1⟩
theorem entry_environment {s r b f a w t i:V} (h:VectorEnvironment s r b f a w t) (hi:i<s):ValueEnvironment r b f (nth w i) :=
  ⟨h.1,h.2.1,h.2.2.2.2.1.nth hi,h.2.2.2.2.2.2 i hi⟩
theorem vectorEnvironment_child {s r b f a w t v:V} (h:VectorEnvironment s r b f a w t)
    (hv:IsSemiterm Presentation.language s v) (hr:v<t):VectorEnvironment s r b f a w v :=
  ⟨h.1,h.2.1,h.2.2.1,hv,h.2.2.2.2.1,le_trans hr.le h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩
theorem vectorInput_valid {s r b f a w t:V} (h:VectorEnvironment s r b f a w t):IsFormula language (vectorInput s r b f a w) := by
  apply IsSemiformula.and.mpr
  refine ⟨?_,IsSemiformula.and.mpr ⟨inputDomain_valid (original_environment h),?_⟩⟩
  · apply IsSemiformula.and.mpr
    exact ⟨NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.1,NumericPAeqValueDomainGuard.guard_vector_isSemiformula h.2.1⟩
  · exact NumericPAeqValueRealizationGuard.guard_vector_isSemiformula h.1 h.2.1 h.2.2.2.2.1 h.2.2.1 h.2.2.2.2.2.2
theorem vectorSubstitutedPredicate_valid {s r b f a w t:V} (h:VectorEnvironment s r b f a w t):
    IsSemiformula language 1 (valuePredicate b f (termSubst Presentation.language w t)) := by
  have hb : IsSemitermVec language r 1 b := by simpa [shiftTerms_zero_arity h.1] using shiftTerms_isSemitermVec h.1
  have hf : IsSemitermVec language (len f) 1 f := by simpa [shiftTerms_zero_arity h.2.1] using shiftTerms_isSemitermVec h.2.1
  apply valueSyntax_vectorSubst_isSemiformula
  refine ⟨?_,h.2.2.2.1,?_,h.2.2.2.2.1,?_⟩
  · simpa [ParametersValid] using And.intro hb (And.intro hf (show IsSemiterm language 1 (qqBvar (0:V)) by simp))
  · simpa using h.2.2.2.2.2.1
  · simpa using h.2.2.2.2.2.2
theorem vectorComparison_valid {s r b f a w t:V} (h:VectorEnvironment s r b f a w t):IsFormula language (vectorComparison b f a w t) := by
  let P : RelationalPredicateBinary.SF (V:=V) 1 := ⟨_,by simpa using vectorSubstitutedPredicate_valid h⟩
  let Q : RelationalPredicateBinary.SF (V:=V) 1 := ⟨_,by simpa using valuePredicate_valid (original_environment h)⟩
  have he := pairwise_val P Q
  change (pairwise P Q isoPredicate).val=vectorComparison b f a w t at he
  rw [←he]
  exact (pairwise P Q isoPredicate).isSemiformula
theorem vectorCode_valid {s r b f a w t:V} (h:VectorEnvironment s r b f a w t):IsFormula language (vectorCode s r b f a w t) :=
  IsSemiformula.imp.mpr ⟨vectorInput_valid h,vectorComparison_valid h⟩
#print axioms vectorInput_valid
#print axioms vectorSubstitutedPredicate_valid
#print axioms vectorComparison_valid
end PA196.Arithmetic.Transport.NumericPAeqValueVectorRealization


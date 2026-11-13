module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueVectorRealizationSyntax
public import M6PA.Calibration.NumericPAeqSupportedValueCoherenceShape
public import M6PA.Calibration.NumericPAeqTermSupportedVectorSubst
@[expose] public section
namespace M6.PA.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence NumericPAeqValueVectorRealization
open NumericPAeqSupportedValueTotality NumericPAeqSupportedValueCoherence
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
def SupportedVectorEnvironment (s r b f a w t:V):Prop :=
  IsSemitermVec language r 0 b ∧ IsSemitermVec language (len f) 0 f ∧
  IsSemitermVec language s 0 a ∧ IsSemiterm Presentation.language s t ∧
  IsSemitermVec Presentation.language s r w ∧ FreeSupported (len f) t ∧ ∀i<s,FreeSupported (len f) (nth w i)
theorem original_environment {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t):SupportedValueEnvironment s a f t :=
  ⟨h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2.2.1⟩
theorem entry_environment {s r b f a w t i:V} (h:SupportedVectorEnvironment s r b f a w t) (hi:i<s):SupportedValueEnvironment r b f (nth w i) :=
  ⟨h.1,h.2.1,h.2.2.2.2.1.nth hi,h.2.2.2.2.2.2 i hi⟩
theorem substituted_environment {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t):
    SupportedValueEnvironment r b f (termSubst Presentation.language w t) :=
  ⟨h.1,h.2.1,h.2.2.2.2.1.termSubst h.2.2.2.1,
    freeSupported_subst h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩
theorem vectorEnvironment_child {s r b f a w t v:V} (h:SupportedVectorEnvironment s r b f a w t)
    (hv:IsSemiterm Presentation.language s v) (hs:FreeSupported (len f) v):SupportedVectorEnvironment s r b f a w v :=
  ⟨h.1,h.2.1,h.2.2.1,hv,h.2.2.2.2.1,hs,h.2.2.2.2.2.2⟩
theorem vectorEnvironment_at {s r b f a w k fn ts i:V}
    (h:SupportedVectorEnvironment s r b f a w (qqFunc k fn ts)) (hi:i<k):
    SupportedVectorEnvironment s r b f a w (nth ts i) := by
  have hv := IsSemiterm.func.mp h.2.2.2.1
  exact vectorEnvironment_child h (hv.2.nth hi) ((freeSupported_func hv.1 hv.2.isUTerm).mp h.2.2.2.2.2.1 i hi)
theorem entry_valid {s r b f a w t i:V} (h:SupportedVectorEnvironment s r b f a w t) (hi:i<s):
    IsFormula language (NumericPAeqValueRealizationGuard.entry b f w a i) := by
  apply valueSyntax_supported_isSemiformula
  refine ⟨?_,h.2.2.2.2.1.nth hi,?_⟩
  · simpa [ParametersValid] using And.intro h.1 (And.intro h.2.1 (h.2.2.1.nth hi))
  · simpa using h.2.2.2.2.2.2 i hi
theorem vectorInput_valid {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t):IsFormula language (vectorInput s r b f a w) := by
  apply IsSemiformula.and.mpr
  refine ⟨?_,IsSemiformula.and.mpr ⟨NumericPAeqSupportedValueTotality.inputDomain_valid (original_environment h),?_⟩⟩
  · exact NumericPAeqSupportedValueTotality.inputDomain_valid (substituted_environment h)
  · exact NumericPAeqValueRealizationGuard.guard_isSemiformula b f w a s 0 (fun i hi=>entry_valid h hi)
theorem vectorComparison_valid {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t):IsFormula language (vectorComparison b f a w t) := by
  let P : RelationalPredicateBinary.SF (V:=V) 1 := ⟨_,by simpa using NumericPAeqSupportedValueCoherence.valuePredicate_valid (substituted_environment h)⟩
  let Q : RelationalPredicateBinary.SF (V:=V) 1 := ⟨_,by simpa using NumericPAeqSupportedValueCoherence.valuePredicate_valid (original_environment h)⟩
  have he := pairwise_val P Q
  change (pairwise P Q isoPredicate).val=vectorComparison b f a w t at he
  rw [←he]; exact (pairwise P Q isoPredicate).isSemiformula
theorem vectorCode_valid {s r b f a w t:V} (h:SupportedVectorEnvironment s r b f a w t):IsFormula language (vectorCode s r b f a w t) :=
  IsSemiformula.imp.mpr ⟨vectorInput_valid h,vectorComparison_valid h⟩
#print axioms substituted_environment
#print axioms vectorEnvironment_at
#print axioms entry_valid
#print axioms vectorCode_valid
end M6.PA.NumericPAeqSupportedVectorRealization

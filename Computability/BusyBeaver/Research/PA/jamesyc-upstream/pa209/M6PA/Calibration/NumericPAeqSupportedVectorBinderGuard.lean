module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedVectorBinderSyntax
public import M6PA.Calibration.NumericPAeqValueRealizationGuardCollection
@[expose] public section
namespace M6.PA.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueRealizationGuard RelationalSource.Numeric
open ActualCheckerBlueprint ActualCertificateEquivalence ActualCertificateConstructors.Dominated
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem vector_qVec_entries_valid {s r b f a w t x:V}
    (h:SupportedVectorEnvironment s r b f a w t) (hx:IsSemiterm language 0 x):
    ∀i<s+1,IsFormula language (entry (x∷b) f (qVec Presentation.language w) (x∷a) i) := by
  intro i hi
  rcases zero_or_succ i with rfl|⟨j,rfl⟩
  · rw [vector_qVec_entry_zero]; exact variableValue_isSemiformula hx hx
  · have hj : j<s := by simpa using hi
    rw [vector_qVec_entry_succ h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2 hx hj]
    exact entry_valid h hj
theorem vector_qVec_guard_native {s r b f a w t x:V}
    (h:SupportedVectorEnvironment s r b f a w t) (hx:IsSemiterm language 0 x) (param:V)
    (self:Certificate (wim (translate param (domainCode x)) (translate param (variableValue x x)))):
    ∃code,verifyValue code=wim
      (wa (translate param (guard b f w a s)) (translate param (domainCode x)))
      (translate param (guard (x∷b) f (qVec Presentation.language w) (x∷a) (s+1)))+1 := by
  apply guard_collection_certificate _ param _ _ _ _ (s+1) 0 (vector_qVec_entries_valid h hx)
  intro i hi
  let H := wa (translate param (guard b f w a s)) (translate param (domainCode x))
  let base : Context [H] H := .assumption (by simp)
  rcases zero_or_succ i with rfl|⟨j,rfl⟩
  · rw [vector_qVec_entry_zero]
    let out := (base.andRight.mp (.closed self)).deduction.empty
    exact ⟨out.code,out.accepted⟩
  · have hj : j<s := by simpa using hi
    rw [vector_qVec_entry_succ h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2 hx hj]
    obtain ⟨code,hcode⟩ := guard_projection_certificate param b f w a s 0 j hj (fun k hk=>entry_valid h hk)
    let out := (base.andLeft.mp (.closed (⟨code,hcode⟩ : Certificate _))).deduction.empty
    exact ⟨out.code,out.accepted⟩
#print axioms vector_qVec_entries_valid
#print axioms vector_qVec_guard_native
end M6.PA.NumericPAeqSupportedVectorRealization

module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueRealizationGuardCollection
public import PA196.Arithmetic.Transport.NumericPAeqValueVectorRealizationSyntax
public import PA196.Arithmetic.Transport.NumericPAeqValueSelfVariableCertificate
public import Foundation.FirstOrder.Arithmetic.Collection.Basic
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqCanonicalVectorInput
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueVectorRealization NumericPAeqValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem entry_eq {m B i:V} (hi:i<m):
    NumericPAeqValueRealizationGuard.entry 0 B (fvarVec m) B i=variableValue (nth B i) (nth B i) := by
  simp only [NumericPAeqValueRealizationGuard.entry,nth_fvarVec m i hi,valueSyntax_fvar,parameters_result,parameters_free]
theorem entries_valid {m B:V} (hb:IsSemitermVec language m 0 B):
    ∀i<m,IsFormula language (NumericPAeqValueRealizationGuard.entry 0 B (fvarVec m) B i) := by
  intro i hi; rw [entry_eq hi]; exact variableValue_isSemiformula (hb.nth hi) (hb.nth hi)
theorem input_valid {m B:V} (hb:IsSemitermVec language m 0 B):
    IsFormula language (vectorInput m 0 0 B B (fvarVec m)) := by
  have hB := NumericPAeqValueDomainGuard.guard_vector_isSemiformula hb
  have hG := NumericPAeqValueRealizationGuard.guard_isSemiformula 0 B (fvarVec m) B m 0 (entries_valid hb)
  simpa [vectorInput,inputDomain,NumericPAeqValueDomainGuard.guard_zero,hb.lh,
    IsSemiformula.and] using And.intro (And.intro (show IsFormula language (qqVerum:V) by simp) hB) (And.intro (And.intro hB hB) hG)
local instance domain_definable : 𝚺ᴬ₁-Function₁ (domainCode : V→V) :=
  (templateOne_defined domainTemplate).to_definable
local instance variable_definable : 𝚺ᴬ₁-Function₂ (variableValue : V→V→V) := variableValue_defined.to_definable
attribute [local irreducible] domainCode variableValue imp
theorem self_codes_bounded (m B:V):
    ∃d:V,∀i<m,imp language (domainCode (nth B i)) (variableValue (nth B i) (nth B i))≤d := by
  have hR : 𝚺ᴬ₁.DefinableRel (fun i d:V=>d=imp language (domainCode (nth B i)) (variableValue (nth B i) (nth B i))) := by
    unfold imp
    definability
  obtain ⟨d,hd⟩ := IBroadSigma.collection (s:=0) hR m (fun i _=>⟨_,rfl⟩)
  refine ⟨d,?_⟩
  intro i hi
  obtain ⟨v,hv,rfl⟩ := hd i hi
  exact hv.le
#print axioms entry_eq
#print axioms entries_valid
#print axioms input_valid
#print axioms self_codes_bounded
end PA196.Arithmetic.Transport.NumericPAeqCanonicalVectorInput


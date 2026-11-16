module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorBinderInput
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorBinderEnvironment
public import PA196.Arithmetic.Transport.NumericPAeqValueSelfVariableCertificate
public import PA196.Arithmetic.Transport.NumericPAeqValueCertificateComposition
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization RelationalSource.Numeric
open PA196.Arithmetic.Checker ActualCertificateEquivalence PA196.Arithmetic.Certificates.Dominated
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem vector_qVec_input_requested_certificate {s r b f a w t x:V}
    (h:SupportedVectorEnvironment s r b f a w t) (hx:IsSemiterm language 0 x)
    (native lo z:V) (hc:FormulaCovered 0 native lo z
      (imp language (qqAnd (vectorInput s r b f a w) (domainCode x))
        (vectorInput (s+1) (r+1) (x∷b) f (x∷a) (qVec Presentation.language w)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp language (qqAnd (vectorInput s r b f a w) (domainCode x))
        (vectorInput (s+1) (r+1) (x∷b) f (x∷a) (qVec Presentation.language w)))+1 := by
  let A := qqAnd (vectorInput s r b f a w) (domainCode x)
  let B := vectorInput (s+1) (r+1) (x∷b) f (x∷a) (qVec Presentation.language w)
  let S := imp language (domainCode x) (variableValue x x)
  have hG := vectorInput_valid h
  have hD := domainCode_isSemiformula hx
  have hA : IsFormula language A := IsSemiformula.and.mpr ⟨hG,hD⟩
  have lifted := vectorEnvironment_qVec h hx (show IsSemiterm Presentation.language (s+1) (qqBvar 0) by simp) (freeSupported_bvar (len f) 0)
  have hB : IsFormula language B := vectorInput_valid lifted
  have hV := variableValue_isSemiformula hx hx
  let d := max S (imp language A B)
  have he := padded_proofEnvironment d native lo z hc.1.1
  have hS : FormulaCovered 0 (padEnvironment native d) lo (z+lo+d) S :=
    he.coverage (IsSemiformula.imp.mpr ⟨hD,hV⟩) (le_max_left _ _)
  let param := parameters 0 (padEnvironment native d) lo (z+lo+d)
  obtain ⟨self,hself⟩ := selfVariable_requested_certificate x _ _ _ hx hS
  obtain ⟨forward,_,hforward,_⟩ := translate_imp_certificates param (domainCode x) (variableValue x x) hD.isUFormula hV.isUFormula
  let selfArrow := (⟨self,hself⟩ : Certificate (translate param S)).mp ⟨forward,hforward⟩
  obtain ⟨code,hcode⟩ := vector_qVec_input_native h hx param selfArrow
  have ha : translate param A=wa (translate param (vectorInput s r b f a w)) (translate param (domainCode x)) := by
    simp only [A,translate_and _ _ _ hG.isUFormula hD.isUFormula,translationAnd_eq]
  obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param A B hA.isUFormula hB.isUFormula
  let arrow : Certificate (wim (translate param A) (translate param B)) := ⟨code,by simpa only [ha] using hcode⟩
  let out := arrow.mp ⟨back,hback⟩
  exact padded_proof_certificate_readback (imp language A B) native lo z d out.code hc out.accepted
#print axioms vector_qVec_input_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization


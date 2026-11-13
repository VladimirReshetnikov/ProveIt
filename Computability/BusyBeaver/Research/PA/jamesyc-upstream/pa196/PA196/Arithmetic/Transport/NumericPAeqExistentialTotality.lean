module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqExistentialOpening
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueTotality
public import PA196.Arithmetic.Transport.NumericPAeqValueCertificateComposition
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryEmptyRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqInductionInterpretation NumericPAeqValueCoherence NumericPAeqValueTotality RelationalPredicateBinary
open RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem truthPair_requested_certificate (p native lo z:V) (hp:IsFormula language p)
    (hc:FormulaCovered 0 native lo z (imp language p (qqAnd qqVerum p))):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (imp language p (qqAnd qqVerum p))+1 := by
  let P:SF (V:=V) 0 :=⟨p,hp⟩
  have d:ND.Proof (T:=(∅:Theory language).internalize V) ∅ (P 🡒 (⊤ ⋏ P)) :=by
    apply ND.impIntro
    exact ND.andIntro (TDerivation.verum (by simp)) (ND.assumption P (by simp))
  exact empty_requested_certificate _ d native lo z hc
theorem existence_requested_certificate {f u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hu:IsSemiterm Presentation.language 0 u) (hs:NumericPAeqTerm.FreeSupported (len f) u)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (imp language (freeDomain f) (qqExs (valuePredicate 0 f u)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (imp language (freeDomain f) (qqExs (valuePredicate 0 f u)))+1 := by
  have henv:NumericPAeqSupportedValueTotality.SupportedValueEnvironment 0 0 f u :=⟨by simp,hf,hu,hs⟩
  have hG:=freeDomain_valid hf
  have hI:=NumericPAeqSupportedValueTotality.inputDomain_valid henv
  have hO:=NumericPAeqSupportedValueTotality.valueTotality_isSemiformula (b:=0) (s:=0) (n:=0) (by simp) hf hu hs
  have he :valueTotalityCode 0 f u=qqExs (valuePredicate 0 f u) :=by
    simp [valueTotalityCode,valuePredicate,NumericPAeqTerm.shiftTerms_zero_arity hf,NumericPAeqTerm.shiftTerms_zero_arity (show IsSemitermVec language (0:V) 0 0 by simp)]
  rw [←he] at hc ⊢
  apply source_implication_compose (freeDomain f) (inputDomain 0 0 f) (valueTotalityCode 0 f u) native lo z hG hI hO hc
  · intro g l z hc
    simpa [inputDomain,freeDomain] using truthPair_requested_certificate (freeDomain f) g l z hG (by simpa [inputDomain,freeDomain] using hc)
  · exact NumericPAeqSupportedValueTotality.guarded_value_totality_certificate henv
#print axioms truthPair_requested_certificate
#print axioms existence_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation


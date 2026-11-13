module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqExistentialUniformCertificate
public import PA196.Arithmetic.Transport.NumericPAeqExistentialInstanceTemplateCertificate
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceShape
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaRealization NumericPAeqInductionInterpretation NumericPAeqValueCoherence NumericPAeqValueTotality
open RelationalSource.Numeric PA196.Arithmetic.Checker RelationalPredicateBinary
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def existentialFormula (f p:V):V :=formulaSyntax (NumericPAeqFormula.parameters 0 f) (qqExs p)
theorem existentialFormula_eq {f p:V} (hp:IsSemiformula Presentation.language 1 p):
    existentialFormula f p=guardedExsCode (property f p) :=by
  rw [existentialFormula,formulaSyntax_exs _ _ hp.isUFormula];rfl
theorem existentialFormula_valid {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):IsFormula language (existentialFormula f p) :=by
  rw [existentialFormula_eq hp]
  apply IsSemiformula.exs.mpr
  have hd:IsSemiformula language (1:V) (⌜NumericPAeqTerm.domainTemplate⌝:V) :=by simpa using Semiformula.quote_isSemiformula (V:=V) NumericPAeqTerm.domainTemplate
  simpa using IsSemiformula.and.mpr ⟨hd,property_valid hf hp hs⟩
theorem elimination_requested_certificate {f p u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hu:IsSemiterm Presentation.language 0 u)
    (hs:FreeSupported (len f) p) (hus:NumericPAeqTerm.FreeSupported (len f) u)
    (native lo z:V) (hc:FormulaCovered 0 native lo z
      (imp language (qqAnd (freeDomain f) (qqExs (valuePredicate 0 f u)))
        (imp language (instanceFormula f p u) (existentialFormula f p)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp language (qqAnd (freeDomain f) (qqExs (valuePredicate 0 f u)))
        (imp language (instanceFormula f p u) (existentialFormula f p)))+1 :=by
  have henv:NumericPAeqSupportedValueTotality.SupportedValueEnvironment 0 0 f u :=⟨by simp,hf,hu,hus⟩
  obtain ⟨Q,hQ⟩ :=NumericPAeqSupportedValueCoherence.valuePredicate_payload henv
  let D:V :=(RelationalPredicateBinary.domain (V:=V)).val
  have hD:IsSemiformula language 1 D :=by simpa [D] using (RelationalPredicateBinary.domain (V:=V)).isSemiformula
  have hQv:IsSemiformula language 1 Q.val :=by simpa using Q.isSemiformula
  have hF:=freeDomain_valid hf
  have hB:=instanceFormula_valid hf hp hu hs hus
  have hP:=property_valid hf hp hs
  have hv:=NumericPAeqExistentialInstanceTemplate.instanceCode_valid hF hB hD hQv hP
  have heC:existentialFormula f p=qqExs (qqAnd D (property f p)) :=by
    rw [existentialFormula_eq hp];rfl
  have heU:qqAll (uniformMatrix f p u)=NumericPAeqExistentialInstanceTemplate.uniformCode (freeDomain f) (instanceFormula f p u) D Q.val (property f p) :=by
    simp only [uniformMatrix,hQ,NumericPAeqExistentialInstanceTemplate.uniformCode,NumericPAeqExistentialInstanceTemplate.uniformMatrixCode,D]
  rw [hQ,heC] at hc ⊢
  apply source_certificate_mp (NumericPAeqExistentialInstanceTemplate.uniformCode (freeDomain f) (instanceFormula f p u) D Q.val (property f p)) _ native lo z
    (IsSemiformula.imp.mp hv).1 (IsSemiformula.imp.mp hv).2 hc
  · intro g l z hc
    rw [←heU] at hc ⊢
    exact uniform_requested_certificate hf hp hu hs hus g l z hc
  · intro g l z hc
    exact NumericPAeqExistentialInstanceTemplate.instance_requested_certificate _ _ _ _ _ g l z hF hB hD hQv hP hc
#print axioms existentialFormula_valid
#print axioms elimination_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation


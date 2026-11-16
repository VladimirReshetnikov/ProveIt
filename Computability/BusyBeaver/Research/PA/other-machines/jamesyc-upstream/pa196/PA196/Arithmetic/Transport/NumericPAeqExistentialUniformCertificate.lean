module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqExistentialUniformSyntax
public import PA196.Arithmetic.Transport.FoundationRelationalSequentRequestedUniversal
public import PA196.Arithmetic.Transport.NumericPAeqSourceCertificateMP
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormulaRealization NumericPAeqInductionInterpretation NumericPAeqValueCoherence NumericPAeqFormulaLogical NumericPAeqValueTotality
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem uniform_requested_certificate {f p u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hu:IsSemiterm Presentation.language 0 u)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hus:NumericPAeqTerm.FreeSupported (len f) u)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (qqAll (uniformMatrix f p u))):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (qqAll (uniformMatrix f p u))+1 := by
  apply requested_universal_certificate _ native lo z (uniformMatrix_valid hf hp hu hs hus) hc
  intro g l z hc
  rw [uniformMatrix_free hf hp hu hs hus] at hc ⊢
  let fs :=targetShiftTerms f
  have hf' :IsSemitermVec language (len fs) 0 fs :=by simpa [fs,targetShiftTerms_length hf] using targetShiftTerms_valid hf
  have hs' :NumericPAeqFormula.FreeSupported (len fs) p :=by simpa [fs,targetShiftTerms_length hf] using hs
  have hus' :NumericPAeqTerm.FreeSupported (len fs) u :=by simpa [fs,targetShiftTerms_length hf] using hus
  let x:V :=qqFvar 0
  have hx :IsSemiterm language 0 x :=by simp [x]
  have henv :=singleton_environment ⟨hf',hp,hu,hs',hus',hx⟩
  let F :=freeDomain fs
  let D :=NumericPAeqTerm.valueSyntax (NumericPAeqTerm.parameters 0 fs x) u
  let C :=formulaComparison 0 fs (x∷0) (u∷0) p
  have hF :IsFormula language F :=freeDomain_valid hf'
  have hD :IsFormula language D :=NumericPAeqTerm.valueSyntax_supported_isSemiformula
    ⟨by simp [NumericPAeqTerm.ParametersValid,hf',hx],hu,by simpa using hus'⟩
  have hC :IsFormula language C :=formulaComparison_valid henv
  apply source_certificate_mp (imp language (qqAnd F D) C) (imp language F (imp language D C)) g l z
    (IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hF,hD⟩,hC⟩)
    (IsSemiformula.imp.mpr ⟨hF,IsSemiformula.imp.mpr ⟨hD,hC⟩⟩) hc
  · exact singleton_source_formula_certificate ⟨hf',hp,hu,hs',hus',hx⟩
  · intro g l z hc
    exact curry_requested_certificate F D C g l z hF hD hC hc
#print axioms uniform_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqExistentialInterpretation


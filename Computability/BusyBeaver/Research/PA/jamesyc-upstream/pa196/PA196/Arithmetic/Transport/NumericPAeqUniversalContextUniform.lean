module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqUniversalContextMatrix
public import PA196.Arithmetic.Transport.NumericPAeqUniversalContextInput
public import PA196.Arithmetic.Transport.FoundationRelationalSequentRequestedUniversal
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqUniversalContext
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqInductionInterpretation NumericPAeqValueTotality NumericPAeqFormulaLogical
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem context_uniform_requested_certificate {f p S:V}
    (hf:IsSemitermVec language (len f) 0 f) (hp:IsSemiformula Presentation.language 1 p)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hS:IsFormula language S)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (qqAll (contextMatrix f p S)))
    (child:∀g l z,FormulaCovered 0 g l z (imp language
      (freeDomain (qqFvar 0∷targetShiftTerms f))
      (qqOr (free language (property f p)) (shift language S)))→
      ∃code,verifyValue code=translate (parameters 0 g l z) (imp language
        (freeDomain (qqFvar 0∷targetShiftTerms f))
        (qqOr (free language (property f p)) (shift language S)))+1):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (qqAll (contextMatrix f p S))+1 :=by
  apply requested_universal_certificate _ native lo z (contextMatrix_valid hf hp hs hS) hc
  intro g l z hc
  rw [contextMatrix_free hf hp hs hS] at hc ⊢
  let fs:=targetShiftTerms f
  let x:V:=qqFvar 0
  let H:=freeDomain fs
  let D:=NumericPAeqTerm.domainCode x
  let C:=qqOr (free language (property f p)) (shift language S)
  have hfs:IsSemitermVec language (len fs) 0 fs:=by
    simpa [fs,targetShiftTerms_length hf] using targetShiftTerms_valid hf
  have hx:IsSemiterm language 0 x:=by simp [x]
  have hnew:IsSemitermVec language (len (x∷fs)) 0 (x∷fs):=by simpa using hfs.adjoin hx
  have hH:=freeDomain_valid hfs
  have hD:=NumericPAeqTerm.domainCode_isSemiformula hx
  have hC:IsFormula language C:=IsSemiformula.or.mpr ⟨(property_valid hf hp hs).free,hS.shift⟩
  have hHD:=IsSemiformula.and.mpr ⟨hH,hD⟩
  apply source_certificate_mp (imp language (qqAnd H D) C) (imp language H (imp language D C)) g l z
    (IsSemiformula.imp.mpr ⟨hHD,hC⟩)
    (IsSemiformula.imp.mpr ⟨hH,IsSemiformula.imp.mpr ⟨hD,hC⟩⟩) hc
  · intro g l z hc
    apply source_implication_compose (qqAnd H D) (freeDomain (x∷fs)) C g l z
      hHD (freeDomain_valid hnew) hC hc
    · exact freeDomain_prepend_requested_certificate hfs hx
    · exact child
  · intro g l z hc
    exact curry_requested_certificate H D C g l z hH hD hC hc
#print axioms context_uniform_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqUniversalContext


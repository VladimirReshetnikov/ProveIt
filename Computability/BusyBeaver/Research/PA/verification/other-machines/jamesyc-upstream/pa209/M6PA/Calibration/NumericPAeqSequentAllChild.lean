module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentEigenShift
public import M6PA.Calibration.NumericPAeqSequentDerivationInvariant
public import M6PA.Calibration.NumericPAeqValueCertificateComposition
@[expose] public section
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqUniversalContextOpening NumericPAeqInductionInterpretation
open ActualCertificateConstructors ActualCertificateConstructors.Dominated ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource.Numeric (translate nativeOr orLeft orRight orEliminate FormulaCovered padded_proofEnvironment
  padEnvironment translate_imp_certificates translate_or translationOr_eq padded_proof_certificate_readback)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem all_child_requested {f s p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hs:SupportedSet (parameters 0 f) s) (hp:IsSemiformula Presentation.language 1 p)
    (hps:FreeSupported (len f) p)
    (child:RequestedCertificate (eigenEnvironment f) (insert (free Presentation.language p) (setShift Presentation.language s)))
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (imp language (freeDomain (eigenEnvironment f))
      (qqOr (formulaSyntax (parameters 0 (eigenEnvironment f)) (free Presentation.language p))
        (shift language (sequentCode (parameters 0 f) s))))):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (freeDomain (eigenEnvironment f))
        (qqOr (formulaSyntax (parameters 0 (eigenEnvironment f)) (free Presentation.language p))
          (shift language (sequentCode (parameters 0 f) s))))+1 := by
  let e := eigenEnvironment f
  let t := setShift Presentation.language s
  let q := free Presentation.language p
  let A := formulaSyntax (parameters 0 e) q
  let S := sequentCode (parameters 0 f) s
  have he := eigenEnvironment_valid hf
  have ht := hs.eigenShift hf
  have hq := source_free_covered hf hp hps
  have hA := formulaSyntax_supported_isSemiformula hq
  have hS := sequent_valid _ _ 0 0 hs
  let d := guardedCode e (insert q t)
  have env := padded_proofEnvironment d native lo z hc.1.1
  have hcov := env.coverage (guardedCode_valid he (ht.insert hq)) (le_refl d)
  let param := RelationalSource.Numeric.parameters 0 (padEnvironment native d) lo (z+lo+d)
  obtain ⟨code,hcode⟩ := child _ _ _ hcov
  obtain ⟨arrow,harrow⟩ := guardedCode_to_native param e (insert q t) code he (ht.insert hq) hcode
  obtain ⟨ins,hins⟩ := guarded_insert_disjunction param (parameters 0 e) t q (translate param (freeDomain e)) arrow ht hq harrow
  obtain ⟨sh,hsh⟩ := eigenShift_forward_certificate param f s hf hs
  let right := implicationCompose (⟨sh,hsh⟩:Certificate (wim (translate param (sequentCode (parameters 0 e) t)) (translate param (shift language S))))
    (orRight (translate param A) (translate param (shift language S)))
  let mapped := orEliminate (orLeft (translate param A) (translate param (shift language S))) right
  let result := implicationCompose (⟨ins,hins⟩:Certificate (wim (translate param (freeDomain e))
    (nativeOr (translate param A) (translate param (sequentCode (parameters 0 e) t))))) mapped
  have hor : translate param (qqOr A (shift language S))=nativeOr (translate param A) (translate param (shift language S)) := by
    rw [translate_or _ _ _ hA.isUFormula hS.shift.isUFormula,translationOr_eq]
  let arrow' : Certificate (wim (translate param (freeDomain e)) (translate param (qqOr A (shift language S)))) :=
    ⟨result.code,by simpa only [hor] using result.accepted⟩
  obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param (freeDomain e) (qqOr A (shift language S))
    (freeDomain_valid he).isUFormula (IsSemiformula.or.mpr ⟨hA,hS.shift⟩).isUFormula
  let out := arrow'.mp ⟨back,hback⟩
  exact padded_proof_certificate_readback _ native lo z d out.code hc out.accepted
#print axioms all_child_requested
end M6.PA.NumericPAeqFormula.Sequent


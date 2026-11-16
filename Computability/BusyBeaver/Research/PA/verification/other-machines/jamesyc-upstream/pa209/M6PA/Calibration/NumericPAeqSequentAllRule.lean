module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentAllChild
public import M6PA.Calibration.NumericPAeqUniversalSourceContext
@[expose] public section
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqUniversalContext NumericPAeqUniversalContextOpening NumericPAeqInductionInterpretation
open ActualCertificateConstructors ActualCertificateConstructors.Dominated ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource.Numeric (translate nativeOr orEliminate translate_imp_certificates translate_or translationOr_eq)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem all_rule_requested {f s p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hs:SupportedSet (parameters 0 f) s) (hm:qqAll p∈s)
    (child:RequestedCertificate (eigenEnvironment f) (insert (free Presentation.language p) (setShift Presentation.language s))):
    RequestedCertificate f s := by
  have hAll := hs _ hm
  have hp : IsSemiformula Presentation.language 1 p := by simpa using IsSemiformula.all.mp hAll.2.1
  have hps : FreeSupported (len f) p := (freeSupported_all hp.isUFormula).mp (by simpa using hAll.2.2)
  have hS := sequent_valid _ _ 0 0 hs
  have hA := formulaSyntax_supported_isSemiformula hAll
  intro native lo z hc
  apply NumericPAeqValueTotality.source_implication_compose (freeDomain f)
    (qqOr (universalFormula f p) (sequentCode (parameters 0 f) s)) (sequentCode (parameters 0 f) s)
    native lo z (freeDomain_valid hf) (IsSemiformula.or.mpr ⟨hA,hS⟩) hS hc
  · intro g l z hc
    exact universal_source_context_requested_certificate hf hp hps hS g l z hc
      (all_child_requested hf hs hp hps child)
  · intro g l z _
    let param := RelationalSource.Numeric.parameters 0 g l z
    obtain ⟨member,hmember⟩ := member_certificate param (parameters 0 f) s (qqAll p) hs hm
    let both := orEliminate (⟨member,hmember⟩:Certificate (wim (translate param (universalFormula f p))
      (translate param (sequentCode (parameters 0 f) s)))) (identity (translate param (sequentCode (parameters 0 f) s)))
    have hor : translate param (qqOr (universalFormula f p) (sequentCode (parameters 0 f) s))=
        nativeOr (translate param (universalFormula f p)) (translate param (sequentCode (parameters 0 f) s)) := by
      unfold universalFormula
      rw [translate_or _ _ _ hA.isUFormula hS.isUFormula,translationOr_eq]
    let arrow : Certificate (wim (translate param (qqOr (universalFormula f p) (sequentCode (parameters 0 f) s)))
      (translate param (sequentCode (parameters 0 f) s))) := ⟨both.code,by simpa only [hor] using both.accepted⟩
    obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param _ _ (IsSemiformula.or.mpr ⟨hA,hS⟩).isUFormula hS.isUFormula
    let out := arrow.mp ⟨back,hback⟩
    exact ⟨out.code,out.accepted⟩
#print axioms all_rule_requested
end M6.PA.NumericPAeqFormula.Sequent


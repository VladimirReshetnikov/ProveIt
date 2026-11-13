module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentDerivationInvariant
public import M6PA.Calibration.FoundationRelationalSequentPaddingReadback
@[expose] public section

/-! Requested native labels are preserved while two intermediate closed
source arrows are covered. The local rule must explicitly retain the domain
antecedent; it is not supplied by this lifting theorem. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqInductionInterpretation
open ActualCheckerBlueprint ActualCertificateConstructors ActualCertificateEquivalence
open ActualCertificateConstructors.Dominated
open RelationalSource.Numeric (translate padEnvironment padded_proofEnvironment padded_proof_certificate_readback)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem requested_binary_lift {f s t u : V}
    (hf : IsSemitermVec language (len f) 0 f)
    (hs : SupportedSet (parameters 0 f) s)
    (ht : SupportedSet (parameters 0 f) t)
    (hu : SupportedSet (parameters 0 f) u)
    (left : RequestedCertificate f t) (right : RequestedCertificate f u)
    (rule : ∀ param a b : V,
      verifyValue a=wim (translate param (freeDomain f)) (translate param (sequentCode (parameters 0 f) t))+1 →
      verifyValue b=wim (translate param (freeDomain f)) (translate param (sequentCode (parameters 0 f) u))+1 →
      ∃ out, verifyValue out=wim (translate param (freeDomain f)) (translate param (sequentCode (parameters 0 f) s))+1) :
    RequestedCertificate f s := by
  intro native lo z hc
  let d := max (guardedCode f t) (guardedCode f u)
  have env := padded_proofEnvironment d native lo z hc.1.1
  let param := RelationalSource.Numeric.parameters 0 (padEnvironment native d) lo (z+lo+d)
  obtain ⟨a,ha⟩ := left _ _ _ (env.coverage (guardedCode_valid hf ht) (le_max_left _ _))
  obtain ⟨b,hb⟩ := right _ _ _ (env.coverage (guardedCode_valid hf hu) (le_max_right _ _))
  obtain ⟨aa,haa⟩ := guardedCode_to_native param f t a hf ht ha
  obtain ⟨bb,hbb⟩ := guardedCode_to_native param f u b hf hu hb
  obtain ⟨out,hout⟩ := rule param aa bb haa hbb
  obtain ⟨closed,hclosed⟩ := guardedCode_from_native param f s out hf hs hout
  exact padded_proof_certificate_readback _ native lo z d closed hc hclosed

#print axioms requested_binary_lift
end M6.PA.NumericPAeqFormula.Sequent


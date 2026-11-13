module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSequentRequestedPropositional
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqFormula
open M6.PA.NumericPAeqFormula.Sequent

namespace PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqInductionInterpretation
open PA196.Arithmetic.Checker PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence
open RelationalSource.Numeric (translate padded_proofEnvironment padEnvironment padded_proof_certificate_readback)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem identity_rule_requested {f s p : V} (hf : IsSemitermVec language (len f) 0 f)
    (hs : SupportedSet (parameters 0 f) s) (hp : p∈s) (hn : neg Presentation.language p∈s) :
    RequestedCertificate f s := by
  intro native lo z hc
  let param := RelationalSource.Numeric.parameters 0 native lo z
  obtain ⟨code,hcode⟩ := guarded_identity_certificate param (parameters 0 f) s p (translate param (freeDomain f)) hs hp hn
  exact guardedCode_from_native param f s code hf hs hcode

theorem verum_rule_requested {f s : V} (hf : IsSemitermVec language (len f) 0 f)
    (hs : SupportedSet (parameters 0 f) s) (hp : qqVerum∈s) : RequestedCertificate f s := by
  intro native lo z hc
  let param := RelationalSource.Numeric.parameters 0 native lo z
  obtain ⟨code,hcode⟩ := guarded_verum_certificate param (parameters 0 f) s (translate param (freeDomain f)) hs hp
  exact guardedCode_from_native param f s code hf hs hcode

theorem axiom_rule_requested {f s p : V} (hf : IsSemitermVec language (len f) 0 f)
    (hs : SupportedSet (parameters 0 f) s) (hp : p∈s)
    (ha : p∈Presentation.ordinaryPAeq.Δ₁Class) : RequestedCertificate f s := by
  intro native lo z hc
  let d := formulaSyntax (parameters 0 f) p
  have env := padded_proofEnvironment d native lo z hc.1.1
  let param := RelationalSource.Numeric.parameters 0 (padEnvironment native d) lo (z+lo+d)
  obtain ⟨code,hcode⟩ := ordinary_axiom_requested_certificate ha hf _ _ _
    (env.coverage (formulaSyntax_supported_isSemiformula (hs p hp)) (le_refl d))
  obtain ⟨arrow,harrow⟩ := member_certificate param (parameters 0 f) s p hs hp
  let proof := (⟨code,hcode⟩ : Certificate (translate param d)).mp ⟨arrow,harrow⟩
  let guarded := (Context.closed (Γ:=[translate param (freeDomain f)]) proof).deduction.empty
  obtain ⟨out,hout⟩ := guardedCode_from_native param f s guarded.code hf hs guarded.accepted
  exact padded_proof_certificate_readback _ native lo z d out hc hout

#print axioms identity_rule_requested
#print axioms verum_rule_requested
#print axioms axiom_rule_requested
end PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent


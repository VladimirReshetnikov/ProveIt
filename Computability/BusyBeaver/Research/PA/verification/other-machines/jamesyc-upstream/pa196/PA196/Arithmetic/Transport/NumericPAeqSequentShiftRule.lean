module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSequentShiftRuleSyntax
public import PA196.Arithmetic.Transport.NumericPAeqValueCertificateComposition
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
open NumericPAeqInductionInterpretation
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence PA196.Arithmetic.Checker
open RelationalSource.Numeric (translate padded_proofEnvironment padEnvironment padded_proof_certificate_readback)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem shift_rule_requested {f s x:V} (hf:IsSemitermVec language (len f) 0 f)
    (hx:IsSemiterm language 0 x) (hs:SupportedSet (parameters 0 f) s)
    (child:RequestedCertificate f s):RequestedCertificate (x∷f) (setShift Presentation.language s) := by
  have hxf : IsSemitermVec language (len (x∷f)) 0 (x∷f) := by simpa using hf.adjoin hx
  have hset := hs.prependShift hf hx
  intro native lo z hc
  let d := guardedCode f s
  have env := padded_proofEnvironment d native lo z hc.1.1
  let param := RelationalSource.Numeric.parameters 0 (padEnvironment native d) lo (z+lo+d)
  obtain ⟨cc,hcc⟩ := child _ _ _ (env.coverage (guardedCode_valid hf hs) (le_refl d))
  obtain ⟨cn,hcn⟩ := guardedCode_to_native param f s cc hf hs hcc
  obtain ⟨tail,htail⟩ := freeDomain_tail_certificate param f x hf hx
  obtain ⟨fold,hfold⟩ := prepend_shift_forward_certificate param f s x hf hx hs
  let first := implicationCompose (⟨tail,htail⟩:Certificate (wim (translate param (freeDomain (x∷f))) (translate param (freeDomain f))))
    (⟨cn,hcn⟩:Certificate (wim (translate param (freeDomain f)) (translate param (sequentCode (parameters 0 f) s))))
  let result := implicationCompose first (⟨fold,hfold⟩:Certificate (wim (translate param (sequentCode (parameters 0 f) s))
    (translate param (sequentCode (parameters 0 (x∷f)) (setShift Presentation.language s)))))
  obtain ⟨out,hout⟩ := guardedCode_from_native param (x∷f) (setShift Presentation.language s) result.code hxf hset result.accepted
  exact padded_proof_certificate_readback _ native lo z d out hc hout
#print axioms shift_rule_requested
end PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent


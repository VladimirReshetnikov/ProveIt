module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSequentDerivationInvariant
public import PA196.Arithmetic.Transport.NumericPAeqExistentialNativeRule
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
open NumericPAeqExistentialInterpretation NumericPAeqInductionInterpretation
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence PA196.Arithmetic.Checker
open RelationalSource.Numeric (translate nativeOr resolveDisjunction padded_proofEnvironment padEnvironment padded_proof_certificate_readback)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem exs_rule_requested {f s p u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hs:SupportedSet (parameters 0 f) s) (hm:qqExs p∈s)
    (hu:IsSemiterm Presentation.language 0 u) (hus:NumericPAeqTerm.FreeSupported (len f) u)
    (child:RequestedCertificate f (insert (substs1 Presentation.language u p) s)):
    RequestedCertificate f s := by
  have hEx := hs _ hm
  have hp : IsSemiformula Presentation.language 1 p := by simpa using IsSemiformula.exs.mp hEx.2.1
  have hps : FreeSupported (len f) p := (freeSupported_exs hp.isUFormula).mp (by simpa using hEx.2.2)
  have hinst : SupportedFormulaCovered 0 0 (parameters 0 f) (substs1 Presentation.language u p) := by
    apply supported_coverage_subst hEx.1 hp (show IsSemitermVec Presentation.language 1 0 (u∷0) by simpa using (show IsSemitermVec Presentation.language (0:V) 0 0 by simp).adjoin hu)
    · simpa using hps
    · intro i hi
      have hi0 : i=0 := by simpa using hi
      subst i; simpa using hus
  have hset := hs.insert hinst
  intro native lo z hc
  let d := max (guardedCode f (insert (substs1 Presentation.language u p) s)) (existentialRuleCode f p u)
  have env := padded_proofEnvironment d native lo z hc.1.1
  let param := RelationalSource.Numeric.parameters 0 (padEnvironment native d) lo (z+lo+d)
  obtain ⟨cc,hcc⟩ := child _ _ _ (env.coverage (guardedCode_valid hf hset) (le_max_left _ _))
  obtain ⟨cn,hcn⟩ := guardedCode_to_native param f _ cc hf hset hcc
  obtain ⟨ci,hci⟩ := guarded_insert_disjunction param (parameters 0 f) s (substs1 Presentation.language u p)
    (translate param (freeDomain f)) cn hs hinst hcn
  obtain ⟨rule,hrule⟩ := existential_native_rule_certificate hf hp hu hps hus _ _ _
    (env.coverage (existentialRuleCode_valid hf hp hu hps hus) (le_max_right _ _))
  obtain ⟨member,hmember⟩ := member_certificate param (parameters 0 f) s (qqExs p) hs hm
  let G := translate param (freeDomain f)
  let A := translate param (instanceFormula f p u)
  let S := translate param (sequentCode (parameters 0 f) s)
  let base : Context [G] G := .assumption (by simp)
  let disj : Context [G] (nativeOr A S) := base.mp (.closed (⟨ci,hci⟩:Certificate _))
  let ns : Context [wn S,G] (wn S) := .assumption (by simp)
  let av := resolveDisjunction (disj.up (wn S)) ns
  let ex := (base.up (wn S) |>.andIntro av).mp (.closed (⟨rule,hrule⟩:Certificate _))
  let sv := ex.mp (.closed (⟨member,hmember⟩:Certificate _))
  let out := (Context.mp sv ns).deduction.dne.deduction.empty
  obtain ⟨result,hresult⟩ := guardedCode_from_native param f s out.code hf hs out.accepted
  exact padded_proof_certificate_readback (guardedCode f s) native lo z d result hc hresult
#print axioms exs_rule_requested
end PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent


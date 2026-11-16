module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBottomDomainCertificate
public import M6PA.Calibration.NumericPAeqSequentBottomReadback
public import M6PA.Calibration.NumericPAeqRepeatedEnvironment
public import M6PA.Calibration.FoundationRelationalSequentEnvironmentExistence
@[expose] public section
namespace M6.PA.NumericPAeqBottomDomain
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqInductionInterpretation NumericPAeqValueTotality NumericPAeqRepeatedEnvironment
open RelationalSource.Numeric ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
/-- Only the guarded bottom certificate remains conditional; every domain-discharge
operation is paid, including repetition, closed quantification and inhabitation. -/
theorem repeated_guard_bottom_requested (k:V)
    (child:NumericPAeqFormula.Sequent.RequestedCertificate (environment (qqFvar 0) k) {(qqFalsum:V)})
    (native lo z:V) (hc:FormulaCovered 0 native lo z (qqFalsum:V)):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (qqFalsum:V)+1:=by
  have hx:IsSemiterm L 0 (qqFvar (0:V)):=by simp
  have hf:IsSemitermVec L (len (environment (qqFvar 0) k)) 0 (environment (qqFvar 0) k):=by
    simpa using environment_valid hx k
  apply bottom_of_domain_refutation native lo z hc
  intro g l z hc
  apply source_implication_compose (NumericPAeqTerm.domainCode (qqFvar 0))
    (freeDomain (environment (qqFvar 0) k)) qqFalsum g l z
    (NumericPAeqTerm.domainCode_isSemiformula hx) (freeDomain_valid hf) (by simp) hc
  · intro g l z hc
    exact domain_requested_certificate (qqFvar 0) k g l z hx hc
  · exact NumericPAeqFormula.Sequent.bottom_guarded_readback hf child

theorem native_bottom_of_repeated_guard (k:V)
    (child:NumericPAeqFormula.Sequent.RequestedCertificate (environment (qqFvar 0) k) {(qqFalsum:V)}):
    ∃code:V,verifyValue code=2:=by
  obtain ⟨native,lo,z,henv⟩:=proofEnvironment_exists (qqFalsum:V)
  obtain ⟨code,hcode⟩:=repeated_guard_bottom_requested k child native lo z
    (henv.coverage (by simp) (le_refl _))
  refine ⟨code,?_⟩
  simpa only [translate_falsum,show (1:V)+1=2 by norm_num] using hcode
#print axioms repeated_guard_bottom_requested
#print axioms native_bottom_of_repeated_guard
end M6.PA.NumericPAeqBottomDomain


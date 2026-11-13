module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLKBounded
public import PA196.Arithmetic.Transport.FoundationRelationalSequentDerivation
public import PA196.Arithmetic.Transport.FoundationRelationalSequentEnvironmentExistence
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateTemplate

/-! A fixed host template LK proof supplies an actual native certificate.
The native environment is existentially supplied by the checked numeric proof
compiler. This does not construct the ordinal-induction template. -/
namespace PA196.Arithmetic.Transport.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
private theorem empty_axiom_supplier :
    RelationalSource.Numeric.AxiomCertificateSupplier (V:=V) (∅ : Theory L) := by
  intro p f lo z hp
  change False at hp
  exact hp.elim

theorem template_lk_certificate {Γ : LK.Sequent sourceLanguage}
    (d : LK.Derivation Γ) {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hb : (proofFreeBound d : V) ≤ len f) :
    ∃ g lo z code : V,
      verifyValue code = RelationalSource.Numeric.sequentCode
        (RelationalSource.Numeric.parameters 0 g lo z) (sequentValue Γ P f) + 1 := by
  obtain ⟨w,hw⟩ := template_lk_sound_of_bound (T:=(∅ : Theory L)) d hP hf hb
  obtain ⟨g,lo,z,hg⟩ := RelationalSource.Numeric.proofEnvironment_exists w
  obtain ⟨code,hcode⟩ := RelationalSource.Numeric.derivation_certificate_of_axiom_supplier
    empty_axiom_supplier w g lo z hw.2 hg
  refine ⟨g,lo,z,code,?_⟩
  simpa only [hw.1] using hcode
#print axioms template_lk_certificate
end PA196.Arithmetic.Transport.RelationalPredicateTemplate


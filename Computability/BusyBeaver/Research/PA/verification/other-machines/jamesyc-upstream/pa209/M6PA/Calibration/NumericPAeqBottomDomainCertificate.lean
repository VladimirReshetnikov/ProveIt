module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBottomDomainClosed
@[expose] public section
namespace M6.PA.NumericPAeqBottomDomain
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric ActualCheckerBlueprint NumericPAeqValueTotality
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
/-- Conditional domain discharge; the closed domain-refutation supplier is explicit. -/
theorem bottom_of_domain_refutation (native lo z:V) (hc:FormulaCovered 0 native lo z (qqFalsum:V))
    (child:∀g l z,FormulaCovered 0 g l z (imp L (NumericPAeqTerm.domainCode (qqFvar (0:V))) qqFalsum)→
      ∃code,verifyValue code=translate (parameters 0 g l z) (imp L (NumericPAeqTerm.domainCode (qqFvar (0:V))) qqFalsum)+1):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (qqFalsum:V)+1:=by
  let Z:V:=(⌜ForwardRelational.zeroInhabited⌝:V)
  have hZ:IsFormula L Z:=by simp [Z]
  have hbot:IsFormula L (qqFalsum:V):=by simp
  apply source_certificate_mp Z qqFalsum native lo z hZ hbot hc
  · exact RelationalClosedCertificate.zero_certificate
  · intro g l z hc
    apply source_certificate_mp (domainRefutationCode (V:=V)) (imp L Z qqFalsum) g l z
      domainRefutation_valid (IsSemiformula.imp.mpr ⟨hZ,hbot⟩) hc
    · intro g l z hc
      exact domainRefutation_requested_certificate g l z hc child
    · exact domain_contradiction_requested_certificate
#print axioms bottom_of_domain_refutation
end M6.PA.NumericPAeqBottomDomain


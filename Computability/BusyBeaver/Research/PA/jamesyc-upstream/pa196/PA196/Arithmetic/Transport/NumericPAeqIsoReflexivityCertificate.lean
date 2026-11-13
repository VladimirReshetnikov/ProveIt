module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqIsoReflexivityProof
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryRequested
public import PA196.Arithmetic.Transport.RelationalClosedCertificateCoherenceSupply
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem isoReflexivity_requested_certificate (x g lo z : V)
    (hx : IsSemiterm L 0 x)
    (hc : FormulaCovered 0 g lo z
      (imp L (NumericPAeqTerm.domainCode x) (NumericPAeqValueIsoGuard.isoCode x x))) :
    ∃ code, verifyValue code = translate (parameters 0 g lo z)
      (imp L (NumericPAeqTerm.domainCode x) (NumericPAeqValueIsoGuard.isoCode x x)) + 1 := by
  let a : ST (V:=V) 0 := ⟨x, by simpa using hx⟩
  have he := isoReflexivity_instance_val a
  change (unary domain a 🡒 binary isoPredicate a a).val =
    imp L (NumericPAeqTerm.domainCode x) (NumericPAeqValueIsoGuard.isoCode x x) at he
  rw [←he] at hc ⊢
  apply singleton_requested_certificate isoReflexivityTyped
    (unary domain a 🡒 binary isoPredicate a a) (isoReflexivityProof a) g lo z hc
  intro g lo z h
  rw [isoReflexivityTyped_quote] at h ⊢
  exact RelationalClosedCertificate.isoReflexivity_certificate g lo z h
#print axioms isoReflexivity_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence

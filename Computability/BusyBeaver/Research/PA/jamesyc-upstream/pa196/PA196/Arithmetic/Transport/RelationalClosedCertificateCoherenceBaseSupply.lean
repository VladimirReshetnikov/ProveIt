module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalClosedCertificateCoherenceZeroSeed
public import PA196.Arithmetic.Transport.RelationalClosedCertificateCoherenceSuccessorSeed
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalClosedCertificate

namespace PA196.Arithmetic.Transport.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem zeroIso_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜zeroIsoClosed⌝ : V)) :
    ∃cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜zeroIsoClosed⌝ : V)+1 :=
  relocated_certificate zeroIsoClosed zeroIso_closed zeroIsoReserve zeroIsoReserve_code zeroIsoNativeProof f lo z h

theorem successorIso_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜successorIsoClosed⌝ : V)) :
    ∃cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜successorIsoClosed⌝ : V)+1 :=
  relocated_certificate successorIsoClosed successorIso_closed successorIsoReserve successorIsoReserve_code
    successorIsoNativeProof f lo z h
#print axioms zeroIso_certificate
#print axioms successorIso_certificate
end PA196.Arithmetic.Transport.RelationalClosedCertificate


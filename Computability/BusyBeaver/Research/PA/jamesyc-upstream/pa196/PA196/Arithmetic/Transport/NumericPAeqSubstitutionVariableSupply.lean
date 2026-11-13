module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSubstitutionVariableSeed
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

theorem isoRightTransport_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜isoRightTransportClosed⌝ : V)) :
    ∃cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜isoRightTransportClosed⌝ : V)+1 :=
  relocated_certificate isoRightTransportClosed isoRightTransport_closed isoRightTransportReserve isoRightTransportReserve_code
    isoRightTransportNativeProof f lo z h
#print axioms isoRightTransport_certificate
end PA196.Arithmetic.Transport.RelationalClosedCertificate

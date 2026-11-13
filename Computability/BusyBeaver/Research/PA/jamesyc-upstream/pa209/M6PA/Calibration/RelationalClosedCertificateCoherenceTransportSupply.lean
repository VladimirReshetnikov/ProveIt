module
public import M6PA.Theory
public import M6PA.Calibration.RelationalClosedCertificateCoherenceTransportSeed
@[expose] public section
namespace M6.PA.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem isoTransport_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜isoTransportClosed⌝ : V)) :
    ∃cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜isoTransportClosed⌝ : V)+1 :=
  relocated_certificate isoTransportClosed isoTransport_closed isoTransportReserve isoTransportReserve_code
    isoTransportNativeProof f lo z h
#print axioms isoTransport_certificate
end M6.PA.RelationalClosedCertificate

module
public import M6PA.Theory
public import M6PA.Calibration.RelationalClosedCertificateCoherenceSeeds
@[expose] public section
namespace M6.PA.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND PairGraph
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem isoReflexivity_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜orderIsoReflexivityStatement⌝ : V)) :
    ∃cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜orderIsoReflexivityStatement⌝ : V)+1 :=
  relocated_certificate orderIsoReflexivityStatement isoReflexivity_closed (coherenceReserve orderIsoReflexivityStatement)
    (coherenceReserve_code _) isoReflexivityNativeProof f lo z h
#print axioms isoReflexivity_certificate

theorem isoSymmetry_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜isoSymmetryClosed⌝ : V)) :
    ∃cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜isoSymmetryClosed⌝ : V)+1 :=
  relocated_certificate isoSymmetryClosed isoSymmetry_closed (coherenceReserve isoSymmetryClosed)
    (coherenceReserve_code _) isoSymmetryNativeProof f lo z h
#print axioms isoSymmetry_certificate

theorem isoTransitivity_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜isoTransitivityClosed⌝ : V)) :
    ∃cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜isoTransitivityClosed⌝ : V)+1 :=
  relocated_certificate isoTransitivityClosed isoTransitivity_closed (coherenceReserve isoTransitivityClosed)
    (coherenceReserve_code _) isoTransitivityNativeProof f lo z h
#print axioms isoTransitivity_certificate

theorem addCoherence_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜addCoherenceStatement⌝ : V)) :
    ∃cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜addCoherenceStatement⌝ : V)+1 :=
  relocated_certificate addCoherenceStatement addCoherence_closed (coherenceReserve addCoherenceStatement)
    (coherenceReserve_code _) addCoherenceNativeProof f lo z h
#print axioms addCoherence_certificate

theorem mulCoherence_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜mulCoherenceStatement⌝ : V)) :
    ∃cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜mulCoherenceStatement⌝ : V)+1 :=
  relocated_certificate mulCoherenceStatement mulCoherence_closed (coherenceReserve mulCoherenceStatement)
    (coherenceReserve_code _) mulCoherenceNativeProof f lo z h
#print axioms mulCoherence_certificate
end M6.PA.RelationalClosedCertificate

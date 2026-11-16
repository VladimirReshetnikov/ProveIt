module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalClosedCertificateSeeds
public import PA196.Arithmetic.Transport.RelationalClosedCertificatePrimitives
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic


/-! Four genuine primitive totality certificate suppliers, with no unpaid
host proof premise. This is not a recursive source-term totality compiler. -/
namespace PA196.Arithmetic.Transport.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker ForwardRelational PairGraph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem zero_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜zeroInhabited⌝ : V)) :
    ∃ cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜zeroInhabited⌝ : V)+1 :=
  relocated_certificate zeroInhabited zero_closed (primitiveReserve zeroInhabited)
    (primitiveReserve_code_bound _) zeroNativeProof f lo z h

theorem successor_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜successorClosed⌝ : V)) :
    ∃ cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜successorClosed⌝ : V)+1 :=
  relocated_certificate successorClosed successor_closed (primitiveReserve successorClosed)
    (primitiveReserve_code_bound _) successorNativeProof f lo z h

theorem addition_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜addClosedResult⌝ : V)) :
    ∃ cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜addClosedResult⌝ : V)+1 :=
  relocated_certificate addClosedResult addition_closed (primitiveReserve addClosedResult)
    (primitiveReserve_code_bound _) additionNativeProof f lo z h

theorem multiplication_certificate (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜mulUniversalOutput⌝ : V)) :
    ∃ cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜mulUniversalOutput⌝ : V)+1 :=
  relocated_certificate mulUniversalOutput multiplication_closed (primitiveReserve mulUniversalOutput)
    (primitiveReserve_code_bound _) multiplicationNativeProof f lo z h

#print axioms zero_certificate
#print axioms successor_certificate
#print axioms addition_certificate
#print axioms multiplication_certificate
end PA196.Arithmetic.Transport.RelationalClosedCertificate


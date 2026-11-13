module
public import PA196.Arithmetic.Transport.NumericPAeqRefutationTransport
public import M6PA.Calibration.FoundationPAeqCodeOriginalProofTransport
@[expose] public section
open M6.PA
namespace PA196.Arithmetic.Transport.FoundationNativeRefutationTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

/-- Internal source-presentation conversion followed by the PA196 numeric
interpretation. The proof code may be nonstandard. -/
theorem original_provable_refutation_transport (h:Provable theory (qqFalsum:V)) :
    ∃code:V, verifyValue code=2 :=
  NumericPAeqRefutationTransport.ordinary_provable_refutation_transport
    (FoundationPAeqCode.ordinaryPAeq_refutation_transport h)

theorem original_refutation_transport (d:V) (h:Proof theory d (qqFalsum:V)) :
    ∃code:V, verifyValue code=2 := original_provable_refutation_transport ⟨d,h⟩

#print axioms original_provable_refutation_transport
#print axioms original_refutation_transport
end PA196.Arithmetic.Transport.FoundationNativeRefutationTransport

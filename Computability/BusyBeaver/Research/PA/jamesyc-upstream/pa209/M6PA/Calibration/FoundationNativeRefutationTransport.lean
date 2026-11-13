module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqRefutationTransport
public import M6PA.Calibration.FoundationPAeqCodeOriginalProofTransport
@[expose] public section
namespace M6.PA.FoundationNativeRefutationTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
/-- Composition of the genuine original arithmetic presentation adapter and
ordinaryPAeq interpretation. No host-standardness or unpaid supplier remains. -/
theorem original_provable_refutation_transport (h:Provable theory (qqFalsum:V)):
    ∃code:V,verifyValue code=2:=
  NumericPAeqRefutationTransport.ordinary_provable_refutation_transport
    (FoundationPAeqCode.ordinaryPAeq_refutation_transport h)
theorem original_refutation_transport (d:V) (h:Proof theory d (qqFalsum:V)):
    ∃code:V,verifyValue code=2:=original_provable_refutation_transport ⟨d,h⟩
#print axioms original_provable_refutation_transport
#print axioms original_refutation_transport
end M6.PA.FoundationNativeRefutationTransport


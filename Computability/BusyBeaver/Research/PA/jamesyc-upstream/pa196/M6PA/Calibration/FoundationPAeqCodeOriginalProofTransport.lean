module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeOriginalInductionSupplier
public import M6PA.Calibration.FoundationPAeqCodeSupplierBoundary
@[expose] public section
/-! Discharge the original arbitrary-model induction branch. The exact source
closure count is retained; target canonical axioms use their own proved support
count, related by numeric surplus-vector agreement and actual proof opening. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem originalInductionSupplier_models :
    V↓[ℒₒᵣ] ⊧ originalInductionSupplierSentence :=
  originalInductionSupplier_iff.mpr fun _ hc=>original_induction_axiom_supplier hc

theorem ordinaryPAeq_axiomSupplier_models :
    V↓[ℒₒᵣ] ⊧ axiomSupplierSentence Presentation.ordinaryPAeq :=
  axiomSupplier_iff_original_induction.mpr originalInductionSupplier_models

theorem ordinaryPAeq_derivation_transport {d s : V} (hd : DerivationOf theory d s) :
    Derivable Presentation.ordinaryPAeq (sequentCode s) :=
  derivation_transport_of_original_induction originalInductionSupplier_models hd

theorem ordinaryPAeq_refutation_transport
    (hp : Provable theory (qqFalsum : V)) :
    Provable Presentation.ordinaryPAeq (qqFalsum : V) :=
  refutation_transport_of_original_induction originalInductionSupplier_models hp

theorem pa_proves_originalInductionSupplier : theory ⊢ originalInductionSupplierSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  exact originalInductionSupplier_models (V:=V)

#print axioms originalInductionSupplier_models
#print axioms ordinaryPAeq_axiomSupplier_models
#print axioms ordinaryPAeq_derivation_transport
#print axioms ordinaryPAeq_refutation_transport
#print axioms pa_proves_originalInductionSupplier
end M6.PA.FoundationPAeqCode


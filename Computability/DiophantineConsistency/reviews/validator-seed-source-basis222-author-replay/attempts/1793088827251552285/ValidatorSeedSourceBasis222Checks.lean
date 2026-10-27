import ZFCinPA.ValidatorSeedSourceBasis222
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSeedSourceBasis222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open ValidatorSeedSourceBasis222 ValidatorFullSeedTheory222 ValidatorSourceFullSeed222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (K : Semiformula V ℒₛₑₜ 2) :
    Proof seedTheory (openSeedProofCode K.val) (fullSeedBody K).val := openSeed_isProof K
example (K : Semiformula V ℒₛₑₜ 2) :
    (openSeedProof K).val=openSeedProofCode K.val := rfl
#print axioms closedSeed_recognized
#print axioms openSeed_isProof
#print axioms openSeedProof
end LeanProofs.ZFCinPA.ValidatorSeedSourceBasis222Checks

import ReverseCarrier
import TraceCenterPositiveV2

/-! The existing reverse-carrier witness also has strictly positive center. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace73ReverseCenter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_carrier_center (b mu H Kpos t rho kappa u tau f y : V)
    (hK : Kpos=H*kappa) (htau : 0<tau) (hy : 0<y) (hf : kappa<f) :
    ∃ n : V, 0<n ∧ 0<n-u*u*(b*t) ∧
      n+kappa=tau*f*y+u*u*(b*t)+t+rho ∧
      ((ι b:DiffRing V)*ι mu*ι mu)*
          (ι H*(ι n-ι u*ι u*(ι b*ι t))+ι Kpos)-
        ι H*((ι mu*ι mu)*(ι b*ι t)+ι b*((ι mu*ι mu)*ι rho)) =
      (ι b*ι mu*ι mu*ι H)*(ι tau*ι f*ι y) := by
  obtain ⟨n,hn,hbalance,hcarrier⟩ :=
    TenPositiveReverseCarrier.positive_carrier b mu H Kpos t rho kappa u tau f y hK htau hy hf
  exact ⟨n,hn,TraceCenterPositive.center_positive b t rho kappa tau f y u n htau hy hf hbalance,hbalance,hcarrier⟩

#print axioms Trace73ReverseCenter.positive_carrier_center
end Trace73ReverseCenter

import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ArithmeticPellRecurrence

/-! Positive reverse carrier coordinate with explicit quotient data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveReverseCarrier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_carrier (b mu H Kpos t rho kappa u tau f y : V)
    (hK : Kpos=H*kappa) (htau : 0<tau) (hy : 0<y) (hf : kappa<f) :
    ∃ n : V, 0<n ∧ n+kappa=tau*f*y+u*u*(b*t)+t+rho ∧
      ((ι b:DiffRing V)*ι mu*ι mu)*
          (ι H*(ι n-ι u*ι u*(ι b*ι t))+ι Kpos)-
        ι H*((ι mu*ι mu)*(ι b*ι t)+ι b*((ι mu*ι mu)*ι rho)) =
      (ι b*ι mu*ι mu*ι H)*(ι tau*ι f*ι y) := by
  let total:=tau*f*y+u*u*(b*t)+t+rho
  have hfy : f≤tau*f*y := by
    calc
      f≤tau*f := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp htau)
      _≤tau*f*y := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hy)
  have hrest : tau*f*y≤total := by
    calc
      tau*f*y≤tau*f*y+u*u*(b*t) := by simp
      _≤tau*f*y+u*u*(b*t)+t := by simp
      _≤total := by dsimp [total]; simp
  have hlarge : kappa<total := lt_of_lt_of_le hf (le_trans hfy hrest)
  let n:=total-kappa
  have hn : 0<n := tsub_pos_iff_lt.mpr hlarge
  have hbalance : n+kappa=total := tsub_add_cancel_of_le (le_of_lt hlarge)
  change n+kappa=tau*f*y+u*u*(b*t)+t+rho at hbalance
  have he := congrArg (ι : V →+* DiffRing V) hbalance
  simp only [map_add,map_mul] at he
  change (ι n:DiffRing V)+ι kappa=ι tau*ι f*ι y+ι u*ι u*(ι b*ι t)+ι t+ι rho at he
  have hKR := congrArg (ι : V →+* DiffRing V) hK
  simp only [map_mul] at hKR
  refine ⟨n,hn,hbalance,?_⟩
  rw [hKR]
  calc
    ((ι b:DiffRing V)*ι mu*ι mu)*
        (ι H*(ι n-ι u*ι u*(ι b*ι t))+ι H*ι kappa)-
      ι H*((ι mu*ι mu)*(ι b*ι t)+ι b*((ι mu*ι mu)*ι rho)) =
      (ι b*ι mu*ι mu*ι H)*((ι n+ι kappa)-ι u*ι u*(ι b*ι t)-ι t-ι rho) := by ring
    _=(ι b*ι mu*ι mu*ι H)*(ι tau*ι f*ι y) := by rw [he]; ring

#print axioms TenPositiveReverseCarrier.positive_carrier
end TenPositiveReverseCarrier

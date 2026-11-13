import FreeMainDivisibility

/-! Unchecked draft: model-scale bridge for the 72 carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainCarrierScale
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeMainDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem of_carrier (q s X Y U H b h D N : V)
    (hq : 0 < q) (hU0 : 0 < U)
    (hY : Y = q*q*q*s) (hU : U = Y*Y)
    (hH : H = 3+4*(X*Y+Y))
    (hD : D = U*b+H*h) (hsq : D*D=U*U*N) : q ∣ h := by
  have hd : U ∣ D := scale_dvd_carrier U D N hU0 hsq
  have hmod : D % U = 0 := mod_eq_zero_iff_dvd.mpr hd
  rw [hD, show U*b+H*h = H*h+U*b by ring, mod_add_mul' _ _ hU0] at hmod
  have hUh : U ∣ H*h := mod_eq_zero_iff_dvd.mp hmod
  have hq3 : q*q*q ∣ U := ⟨q*q*q*s*s, by rw [hU,hY]; ring⟩
  have hq3pos : 0 < q*q*q := mul_pos (mul_pos hq hq) hq
  have hqH : q*q*q ∣ H*h := dvd_trans hq3 hUh
  have hmod3 : (H*h) % (q*q*q) = 0 := mod_eq_zero_iff_dvd.mpr hqH
  have he : H*h = 3*h + (q*q*q)*(4*(X+1)*s*h) := by rw [hH,hY]; ring
  rw [he, mod_add_mul' _ _ hq3pos] at hmod3
  exact dvd_of_cube_dvd_three q h (mod_eq_zero_iff_dvd.mp hmod3)

#print axioms FreeMainCarrierScale.of_carrier
end FreeMainCarrierScale

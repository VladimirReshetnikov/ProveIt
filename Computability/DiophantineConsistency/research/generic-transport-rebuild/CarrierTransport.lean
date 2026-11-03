import TransportOrder
import DiophantineConsistency.ArithmeticGcdNormalization
import DiophantineConsistency.ModelDifferenceRing

/-! Denominator-cleared carrier equation implies nonnegative transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveCarrierTransport
open TenPositiveTransportOrder
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem nonnegative_of_carrier (h H m L B k e z n Z : K)
    (hh : 0<h) (hH : 0<H) (hm : 0<m) (hL : 0≤L) (hk : 0≤k) (hn : 0<n)
    (hz : 2*z<L) (he : 2*e<L*m) (hdiscrete : B<0 → B≤-1)
    (hZ : Z=h*m*H*z)
    (hcarrier : Z=h*m*(H*(n-L*B)+k)-H*(m*B+h*e)) : 0≤B := by
  by_contra hnB
  have hB : B≤-1 := hdiscrete (lt_of_not_ge hnB)
  have hp : 0<h*m*H := mul_pos (mul_pos hh hm) hH
  have hq : 0<h*H := mul_pos hh hH
  have hw : 0<m*H := mul_pos hm hH
  have hn' : 0<(h*m*H)*n := mul_pos hp hn
  have hk' : 0≤(h*m)*k := mul_nonneg (le_of_lt (mul_pos hh hm)) hk
  have heq : (h*m*H)*n+(h*m)*k=
      (h*m*H)*z+(m*H)*B+(h*m*H)*L*B+(h*H)*e := by
    rw [hZ] at hcarrier
    nlinarith only [hcarrier]
  exact negative_transport_impossible ((h*m*H)*n) ((h*m)*k) (h*m*H) (h*H) m L z e B (m*H)
    hn' hk' hp hq hL hw (by ring) hz he hB heq

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing

/-- Model difference rings have the required discreteness automatically. -/
theorem model_nonnegative_of_carrier {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (h H m L B k e z n Z : DiffRing V)
    (hh : 0<h) (hH : 0<H) (hm : 0<m) (hL : 0≤L) (hk : 0≤k) (hn : 0<n)
    (hz : 2*z<L) (he : 2*e<L*m)
    (hZ : Z=h*m*H*z)
    (hcarrier : Z=h*m*(H*(n-L*B)+k)-H*(m*B+h*e)) : 0≤B := by
  apply nonnegative_of_carrier h H m L B k e z n Z hh hH hm hL hk hn hz he _ hZ hcarrier
  intro hB
  have hp : 0< -B := neg_pos.mpr hB
  have h := one_le_of_pos (fun a ha => pos_iff_one_le.mp ha) hp
  linarith

#print axioms TenPositiveCarrierTransport.nonnegative_of_carrier
#print axioms TenPositiveCarrierTransport.model_nonnegative_of_carrier
end TenPositiveCarrierTransport

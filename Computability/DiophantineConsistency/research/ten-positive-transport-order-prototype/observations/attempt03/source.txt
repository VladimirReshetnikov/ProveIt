import Direct80RankEquality
import Mathlib.Tactic.Linarith

/-! Ordered-ring core of the negative-transport contradiction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveTransportOrder
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Clearing denominators, a negative integral transport value is impossible.
The signed quantities z and e need only satisfy one-sided bounds. -/
theorem negative_transport_impossible (N K0 P Q m L z e B W : K)
    (hN : 0<N) (hK : 0≤K0) (hP : 0<P) (hQ : 0<Q)
    (hL : 0≤L) (hW : 0<W) (hscale : P=Q*m)
    (hz : 2*z<L) (he : 2*e<L*m) (hB : B≤-1)
    (heq : N+K0=P*z+W*B+P*L*B+Q*e) : False := by
  have hz' : 2*(P*z)<P*L := by
    have h := mul_lt_mul_of_pos_left hz hP
    nlinarith only [h]
  have he' : 2*(Q*e)<P*L := by
    have h := mul_lt_mul_of_pos_left he hQ
    rw [hscale]
    nlinarith only [h]
  have hBL : P*L*B≤-(P*L) := by
    have hh := mul_le_mul_of_nonneg_left hB (mul_nonneg (le_of_lt hP) hL)
    nlinarith only [hh]
  have hBW : W*B≤0 := by
    have hh := mul_le_mul_of_nonneg_left hB (le_of_lt hW)
    nlinarith only [hh,hW]
  linarith

#print axioms TenPositiveTransportOrder.negative_transport_impossible
end TenPositiveTransportOrder

import DiophantineConsistency.ModelDifferenceRing

/-! Size constraint forced by the negative-transport first-root branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88NegativeTransportBound
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A first Pell root is at most `(P+1)k` when `ell=Pk`. -/
theorem first_root_upper (P k tau : R)
    (hP : 0≤P) (hk : 1≤k) (htau : 0≤tau)
    (hnorm : tau*tau=1+(P*k)*((P*k)+k)) :
    tau≤(P+1)*k := by
  have hk0 : 0≤k := by linarith
  have hks : 1≤k*k := by nlinarith [sq_nonneg (k-1)]
  have hs : 1≤(P+1)*(k*k) := by
    have := mul_le_mul_of_nonneg_right (show (1:R)≤P+1 by linarith) (show 0≤k*k by positivity)
    nlinarith
  have hsq : tau*tau≤((P+1)*k)*((P+1)*k) := by nlinarith
  by_contra hn
  have hlt : (P+1)*k<tau := lt_of_not_ge hn
  have hpos : 0<(P+1)*k := by positivity
  have hmul := mul_pos (sub_pos.mpr hlt) (show 0<tau+(P+1)*k by linarith)
  nlinarith

/-- In a discretely ordered ring, the negative transport magnitude is
at most `P` if the positive first-root branch holds. -/
theorem negative_transport_le (P k tau b rho U : R)
    (hdisc : ∀ x : R, 0<x → 1≤x)
    (hP : 0≤P) (hk : 1≤k) (htau : 0≤tau)
    (hb : 0<b) (hrho : 0<rho) (hU : 0<U)
    (hnorm : tau*tau=1+(P*k)*((P*k)+k))
    (hfirst : b*rho+(b*k+1)*U=b*tau) : U≤P := by
  have hroot := first_root_upper P k tau hP hk htau hnorm
  by_contra hn
  have hlt : P<U := lt_of_not_ge hn
  have hstep : P+1≤U := by
    have := hdisc (U-P) (sub_pos.mpr hlt)
    linarith
  have hcoef : 0≤b*k+1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hstep hcoef
  have hmul := mul_le_mul_of_nonneg_left hroot hb.le
  have hbr : 0<b*rho := mul_pos hb hrho
  nlinarith

#print axioms Absorb88NegativeTransportBound.first_root_upper
#print axioms Absorb88NegativeTransportBound.negative_transport_le
end Absorb88NegativeTransportBound

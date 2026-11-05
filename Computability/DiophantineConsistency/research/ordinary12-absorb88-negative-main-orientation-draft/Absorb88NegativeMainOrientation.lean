import DiophantineConsistency.ModelDifferenceRing

/-! Draft: orient the main root from explicit signed-rank and size bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88NegativeMainOrientation
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem main_positive (X Y E P Q W a H eta k d rank : R)
    (hX : 0≤X) (hY : 0≤Y) (hE : 0<E) (hW : 0<W)
    (ha : 0<a) (hH : 0<H) (heta : 0≤eta) (hd : 0≤d)
    (hgap : 0≤W*Y-7-W) (hk : 8*E≤k) (hH7 : H≤7*a)
    (hqp : Q*P=W*E) (hrank : -(Q*P)≤rank) :
    0<W*(X+a*(eta+Y*k))+H*(W*d-k+rank+1) := by
  have hk0 : 0≤k := le_trans (by positivity : 0≤8*E) hk
  have hqp0 : 0≤Q*P := by rw [hqp]; positivity
  have h1 : 0≤W*X := mul_nonneg hW.le hX
  have h2 : 0≤W*a*eta := mul_nonneg (mul_nonneg hW.le ha.le) heta
  have h3 : 0≤H*W*d := mul_nonneg (mul_nonneg hH.le hW.le) hd
  have h4 : 0≤H*(rank+Q*P) := mul_nonneg hH.le (by linarith)
  have h5 : 0≤(7*a-H)*(k+Q*P) := mul_nonneg (by linarith) (by linarith)
  have h6 : 0≤a*(W*Y-7-W)*k := mul_nonneg (mul_nonneg ha.le hgap) hk0
  have h7 : 0≤a*W*(k-8*E) := mul_nonneg (mul_nonneg ha.le hW.le) (by linarith)
  have h8 : 0<a*W*E := mul_pos (mul_pos ha hW) hE
  have hid : W*(X+a*(eta+Y*k))+H*(W*d-k+rank+1) =
      W*X+W*a*eta+H*W*d+H*(rank+Q*P)+H+
        (7*a-H)*(k+Q*P)+a*(W*Y-7-W)*k+
        a*W*(k-8*E)+a*W*E := by
    rw [hqp]
    ring
  rw [hid]
  linarith

#print axioms Absorb88NegativeMainOrientation.main_positive
end Absorb88NegativeMainOrientation

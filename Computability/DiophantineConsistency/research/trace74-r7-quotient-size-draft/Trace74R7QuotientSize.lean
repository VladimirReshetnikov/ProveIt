import Trace74R7QuotientObstruction

/-! UNCHECKED DRAFT: deriving the bounded quotient from an explicit size
condition. No graph, Pell, rank or guard conclusion is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74R7QuotientSize
open Trace74R7QuotientObstruction
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem impossible (q x y : R)
    (hdisc : ∀ z : R, 0<z → 1≤z)
    (hq : 32≤q) (hy : q^3≤y)
    (hx : 65532*(q-1)*y<x)
    (hd : (4*y*(x+1)-1) ∣ (q-1)*(4*y-1)*(516*y-1)*(127*y-32)) : False := by
  have hqpos : 0<q := by linarith
  have hqone : 1≤q := by linarith
  have hq2 : 1≤q*q := by nlinarith
  have hq2cube : q^2≤q^3 := by
    have hm := mul_le_mul_of_nonneg_left hqone (sq_nonneg q)
    nlinarith [hm]
  have hyone : 1≤y := by nlinarith [hq2cube]
  have hypos : 0<y := by linarith
  have hh : 0<q-1 := by linarith
  have h32 : 32*(q-1)<y := by
    have hqq : 0≤q*(q-32) := mul_nonneg (le_of_lt hqpos) (by linarith)
    nlinarith [hq2cube,hqq]
  have hxpos : 0<x := lt_trans (by positivity : 0<65532*(q-1)*y) hx
  have hxy : 0<x*y := mul_pos hxpos hypos
  have hH : 0<4*y*(x+1)-1 := by nlinarith [hxy]
  have ha : 0<4*y-1 := by linarith
  have hb : 0<516*y-1 := by linarith
  have hc : 0<127*y-32 := by linarith
  have hprod : 0<(q-1)*(4*y-1)*(516*y-1)*(127*y-32) := by positivity
  have hprod_bound : (q-1)*(4*y-1)*(516*y-1)*(127*y-32)<262128*(q-1)*y^3 := by
    have h2 : 4*y-1<4*y := by linarith
    have h3 : 516*y-1<516*y := by linarith
    have h4 : 127*y-32<127*y := by linarith
    have hh1 : (q-1)*(4*y-1)<(q-1)*(4*y) := mul_lt_mul_of_pos_left h2 hh
    have hh2 : (q-1)*(4*y-1)*(516*y-1)<(q-1)*(4*y)*(516*y) :=
      mul_lt_mul hh1 (le_of_lt h3) hb (by positivity)
    have hh3 : (q-1)*(4*y-1)*(516*y-1)*(127*y-32)<(q-1)*(4*y)*(516*y)*(127*y) :=
      mul_lt_mul hh2 (le_of_lt h4) hc (by positivity)
    convert hh3 using 1; ring
  have hHsize : 262128*(q-1)*y^3 < (4*y*(x+1)-1)*y := by
    have hm := mul_lt_mul_of_pos_left hx (show 0<4*y^2 by positivity)
    have hp : 0<y*(4*y-1) := mul_pos hypos ha
    nlinarith [hm,hp]
  obtain ⟨j,hj⟩ := hd
  have hjpos : 0<j := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hH) (le_of_not_gt hn)
    rw [←hj] at hm
    exact (not_le_of_gt hprod) hm
  have hjlt : j<y := by
    have hm : (4*y*(x+1)-1)*j < (4*y*(x+1)-1)*y := by
      rw [←hj]
      exact lt_trans hprod_bound hHsize
    exact lt_of_mul_lt_mul_left hm (le_of_lt hH)
  exact impossible_of_bounded_quotient (q-1) x y j hdisc hh hypos hjpos hjlt h32 hj

#print axioms Trace74R7QuotientSize.impossible
end Trace74R7QuotientSize

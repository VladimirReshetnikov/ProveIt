import Trace74UniformBoundedQuotient

/-! Uniform bound on the reduced projection quotient. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74UniformQuotientSize
open Trace74UniformBoundedQuotient
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A reduced projection is impossible when its quotient is forced below Y
and `L*h<Y`. The lower bound on X is explicit. -/
theorem impossible (h X Y L : R)
    (hdisc : ∀ t : R, 0<t → 1≤t)
    (hh : 0<h) (hY : 1≤Y) (hL : 1≤L) (hLh : L*h<Y)
    (hX : 8*h*(4*L)^2*Y<X)
    (hd : (4*Y*(X+1)-1) ∣
      h*(4*Y-1)*(4*(4*L+1)*Y-1)*((4*L-1)*Y-L)) : False := by
  let K := 4*L
  have hk : 4≤K := by dsimp [K]; nlinarith
  have hy : 0<Y := by linarith
  have hl : 0<L := by linarith
  have hx : 0<X := lt_of_lt_of_le (by positivity : 0<8*h*(4*L)^2*Y) hX.le
  have ha : 0<4*Y-1 := by linarith
  have hb : 0<4*(K+1)*Y-1 := by
    have hp := mul_nonneg (show (0:R)≤K+1 by linarith) (show (0:R)≤Y-1 by linarith)
    nlinarith
  have hc : 0<(K-1)*Y-L := by
    have hp := mul_nonneg (show (0:R)≤K-1 by linarith) (show (0:R)≤Y-1 by linarith)
    dsimp [K] at hp ⊢
    nlinarith
  have hprod : 0<h*(4*Y-1)*(4*(K+1)*Y-1)*((K-1)*Y-L) := by positivity
  have haub : 4*Y-1<4*Y := by linarith
  have hbub : 4*(K+1)*Y-1<8*K*Y := by
    have hp := mul_nonneg (show (0:R)≤K-1 by linarith) (le_of_lt hy)
    nlinarith
  have hcub : (K-1)*Y-L<K*Y := by nlinarith
  have hbound : h*(4*Y-1)*(4*(K+1)*Y-1)*((K-1)*Y-L)<32*h*K^2*Y^3 := by
    have h1 : h*(4*Y-1)<h*(4*Y) := mul_lt_mul_of_pos_left haub hh
    have h2 : h*(4*Y-1)*(4*(K+1)*Y-1)<h*(4*Y)*(8*K*Y) :=
      mul_lt_mul h1 hbub.le hb (by positivity)
    have h3 := mul_lt_mul h2 hcub.le hc (by positivity : 0≤h*(4*Y)*(8*K*Y))
    calc
      _<h*(4*Y)*(8*K*Y)*(K*Y) := h3
      _=32*h*K^2*Y^3 := by ring
  have hH : 0<4*Y*(X+1)-1 := by nlinarith [mul_pos hy hx]
  have hsize : 32*h*K^2*Y^3<(4*Y*(X+1)-1)*Y := by
    have hm := mul_lt_mul_of_pos_left hX (show 0<4*Y^2 by positivity)
    have hp : 0<Y*(4*Y-1) := mul_pos hy ha
    dsimp [K] at hm ⊢
    nlinarith [hm,hp]
  obtain ⟨j,hj⟩ := hd
  have hjpos : 0<j := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hH.le (le_of_not_gt hn)
    have heq : h*(4*Y-1)*(4*(K+1)*Y-1)*((K-1)*Y-L)=(4*Y*(X+1)-1)*j := by
      simpa only [K] using hj
    rw [←heq] at hm
    exact (not_le_of_gt hprod) hm
  have hjlt : j<Y := by
    have hm : (4*Y*(X+1)-1)*j<(4*Y*(X+1)-1)*Y := by
      rw [←hj]
      exact lt_trans (by simpa only [K] using hbound) hsize
    exact lt_of_mul_lt_mul_left hm hH.le
  exact impossible_of_bounded_quotient h X Y L j hdisc hh hy hl hjpos hjlt hLh hj

#print axioms Trace74UniformQuotientSize.impossible
end Trace74UniformQuotientSize

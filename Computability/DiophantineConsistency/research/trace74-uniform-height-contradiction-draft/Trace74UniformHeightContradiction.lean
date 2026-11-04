import Trace74Projection

/-! Exploratory ordered-ring height bounds for the uniform projection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74UniformHeightContradiction

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Pure ordered-ring size bounds; the exponential height hypothesis is explicit. -/
theorem product_bounds (h X Y K L : R)
    (hh : 0<h) (hY : 1≤Y) (hL : 1≤L) (hK : K=4*L)
    (hX : 8*h*K^2*Y^2<X) :
    0<h*(4*Y-1)*(4*(K+1)*Y-1)*((K-1)*Y-L) ∧
    h*(4*Y-1)*(4*(K+1)*Y-1)*((K-1)*Y-L)<4*Y*(X+1)-1 := by
  have hk : 4≤K := by nlinarith [hK]
  have hy : 0<Y := by linarith
  have hl : 0<L := by linarith
  have ha : 0<4*Y-1 := by linarith
  have hb : 0<4*(K+1)*Y-1 := by
    have hp := mul_nonneg (show (0:R)≤K+1 by linarith) (show (0:R)≤Y-1 by linarith)
    nlinarith
  have hc : 0<(K-1)*Y-L := by
    have hp := mul_nonneg (show (0:R)≤K-1 by linarith) (show (0:R)≤Y-1 by linarith)
    nlinarith [hK]
  have hapos : 0<4*Y := by positivity
  have hbpos : 0<8*K*Y := by positivity
  have hcpos : 0<K*Y := by positivity
  have haub : 4*Y-1<4*Y := by linarith
  have hbub : 4*(K+1)*Y-1<8*K*Y := by
    have hp := mul_nonneg (show (0:R)≤K-1 by linarith) (le_of_lt hy)
    nlinarith
  have hcub : (K-1)*Y-L<K*Y := by nlinarith
  have hbound : h*(4*Y-1)*(4*(K+1)*Y-1)*((K-1)*Y-L)<
      h*(4*Y)*(8*K*Y)*(K*Y) := by
    have h1 : h*(4*Y-1)<h*(4*Y) := mul_lt_mul_of_pos_left haub hh
    have h2 : h*(4*Y-1)*(4*(K+1)*Y-1)<h*(4*Y)*(8*K*Y) :=
      mul_lt_mul h1 hbub.le hb (by positivity)
    exact mul_lt_mul h2 hcub.le hc (by positivity)
  have hgrowth : 32*h*K^2*Y^3<4*Y*X := by
    have hp := mul_lt_mul_of_pos_left hX (show 0<4*Y by positivity)
    nlinarith
  have hH : 4*Y*X<4*Y*(X+1)-1 := by linarith
  constructor
  · positivity
  · calc
      h*(4*Y-1)*(4*(K+1)*Y-1)*((K-1)*Y-L)
          < h*(4*Y)*(8*K*Y)*(K*Y) := hbound
      _ = 32*h*K^2*Y^3 := by ring
      _ < 4*Y*X := hgrowth
      _ < 4*Y*(X+1)-1 := hH

/-- A positive proper multiple cannot fit below its divisor in a discretely ordered ring. -/
theorem projection_impossible (h X Y K L : R)
    (hdisc : ∀ t : R, 0<t → 1≤t)
    (hh : 0<h) (hY : 1≤Y) (hL : 1≤L) (hK : K=4*L)
    (hX : 8*h*K^2*Y^2<X)
    (hd : (4*Y*(X+1)-1) ∣
      h*(4*Y-1)*(4*(K+1)*Y-1)*((K-1)*Y-L)) : False := by
  obtain ⟨hspos, hslt⟩ := product_bounds h X Y K L hh hY hL hK hX
  have hH : 0<4*Y*(X+1)-1 := lt_trans hspos hslt
  obtain ⟨t,ht⟩ := hd
  have htpos : 0<t := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hH.le (le_of_not_gt hn)
    nlinarith [ht]
  have hm := mul_le_mul_of_nonneg_left (hdisc t htpos) hH.le
  nlinarith [ht]

#print axioms Trace74UniformHeightContradiction.product_bounds
#print axioms Trace74UniformHeightContradiction.projection_impossible
end Trace74UniformHeightContradiction

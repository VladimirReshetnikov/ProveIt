import Trace74FirstThreeLower
import Trace74N3UpperBound

/-! Source draft: join the two ordered-ring endpoints and rule out a small
    positive multiple in a discrete ordered ring. No graph binding is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74N3ScalarDiscrete
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
open Trace74FirstThreeLower

theorem interval (X Y : R) (hX : 32≤X) (hY : 1≤Y)
    (hlo : k X Y*Y<c X Y) (hhi : c X Y<k X Y*(Y+1)) :
    X^2+4*X+4<2*Y ∧ 2*Y<X^2+4*X+8 := by
  have hX0 : 0≤X := le_trans (by norm_num : (0:R)≤32) hX
  have hleft : X^2+4*X+4<2*Y := by
    by_contra hn
    have hW : 0≤X^2+4*X+4-2*Y := sub_nonneg.mpr (le_of_not_gt hn)
    have he : 2*Y+(X^2+4*X+4-2*Y)=X^2+4*X+4 := by ring
    have hh := lower_contradiction X Y (X^2+4*X+4-2*Y) hX0 hY hW he
    exact (not_lt_of_ge (le_of_lt hhi)) hh
  have hk : k X Y=32*X^2*Y^4+32*X*Y^2+6 := by dsimp [k]; ring
  have hright : 2*Y<X^2+4*X+8 := by
    have hgap : (32*X^2*Y^4+32*X*Y^2+6)*Y <
        16*(Y*(X+1)+1)^4-12*(Y*(X+1)+1)^2+1 := by
      simpa only [hk,c] using hlo
    simpa only [pow_two] using Trace74N3UpperBound.upper_of_polynomials X Y hX hgap
  exact ⟨hleft,hright⟩

theorem no_scalar_solution (q X Y w s : R)
    (hdisc : ∀ z : R, 0<z → 1≤z) (hq : 32≤q) (hX : 32≤X) (hY : 1≤Y)
    (hXq : X=q*w) (hYq : Y=q^3*s)
    (hlo : k X Y*Y<c X Y) (hhi : c X Y<k X Y*(Y+1)) : False := by
  obtain ⟨hleft,hright⟩ := interval X Y hX hY hlo hhi
  let Z : R := 2*Y-X^2-4*X
  let T : R := 2*q^2*s-q*w^2-4*w
  have hZ : Z=q*T := by dsimp [Z,T]; rw [hXq,hYq]; ring
  have hqpos : 0<q := lt_of_lt_of_le (by norm_num : (0:R)<32) hq
  have hZpos : 0<Z := by dsimp [Z]; linarith
  have hZq : Z<q := by dsimp [Z]; linarith
  have hTpos : 0<T := by
    by_contra hn
    have hh : q*T≤0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hqpos) (le_of_not_gt hn)
    rw [←hZ] at hh
    exact (not_le_of_gt hZpos) hh
  have hqZ : q≤Z := by
    have hh := mul_le_mul_of_nonneg_left (hdisc T hTpos) (le_of_lt hqpos)
    simpa only [mul_one,←hZ] using hh
  exact (not_le_of_gt hZq) hqZ

#print axioms interval
#print axioms no_scalar_solution
end Trace74N3ScalarDiscrete

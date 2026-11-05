import IndependentYBounds

/-! Unchecked draft: the compact-window half bound without an early index congruence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainRankHalf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rank_half (q X Y R c g : DiffRing V)
    (hq : 0≤q) (hX : q≤X) (hY : q*q*q≤Y)
    (hwin : R+1 < q*(q*q*q)) (hc : 3≤c) (hg : 0≤g)
    (hpell : g*g = 1+(((X*Y+Y)+2)*((X*Y+Y)+2)-1)*(c*c)) :
    2*R<c := by
  have hX0 : 0≤X := le_trans hq hX
  have hq3 : 0≤q*q*q := mul_nonneg (mul_nonneg hq hq) hq
  have hY0 : 0≤Y := le_trans hq3 hY
  let a := X*Y+Y
  have ha : 0≤a := add_nonneg (mul_nonneg hX0 hY0) hY0
  have hn : 2≤a+2 := by linarith
  have hc_bound := IndependentYBounds.pell_c_bound (a+2) c g hn hc hg hpell
  have hq4 : q*(q*q*q)≤X*Y := mul_le_mul hX hY hq3 hX0
  have hR : R<X*Y := lt_of_lt_of_le (lt_trans (lt_add_one R) hwin) hq4
  have h1 : 2*R<2*(X*Y) := mul_lt_mul_of_pos_left hR (by norm_num)
  have h2 : 2*(X*Y)≤2*(a+2) := by
    apply mul_le_mul_of_nonneg_left (show X*Y≤a+2 by dsimp [a]; linarith) (by norm_num)
  exact lt_of_lt_of_le h1 (le_trans h2 hc_bound)

#print axioms FreeMainRankHalf.rank_half
end FreeMainRankHalf

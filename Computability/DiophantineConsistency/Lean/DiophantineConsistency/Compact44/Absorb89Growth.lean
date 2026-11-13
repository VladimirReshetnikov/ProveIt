import DiophantineConsistency.Compact44.Absorb89First
import DiophantineConsistency.Compact44.DirectMainPellGrowth

/-! Conditional first-index growth for the speculative graph parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb89Growth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem three_s_of_square (s Y Q k : V) (hsY : s≤Y) (hY3 : 3≤Y)
    (hYQ : Y≤Q) (hQk : Q*Q≤k) : 3*s≤k := by
  calc
    3*s≤3*Y := mul_le_mul_of_nonneg_left hsY (by simp)
    _=Y*3 := by ring
    _≤Y*Y := mul_le_mul_of_nonneg_left hY3 (by simp)
    _≤Q*Q := mul_le_mul hYQ hYQ (by simp) (by simp)
    _≤k := hQk

theorem growth_of_index (p : Fin 4 → ℕ) (v : Fin 12 → V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) (hn : 3≤n)
    (hcoord :
      let q : V := 1+v 0*(p 0:V)
      let X : V := q*v 5
      let Y : V := (q*(q*q))*v 6
      let Q : V := (X*Y)*Y
      2*ycoord n (2*(Q-1)+1)=v 8+v 9) :
    3*v 6≤v 8+v 9 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let Q : V := (X*Y)*Y
  let k : V := v 8+v 9
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hb1 : 1≤b := pos_iff_one_le.mp hb0
  have hq2 : 2≤q := by
    dsimp [q]
    calc
      (2:V)=1+1 := by norm_num
      _≤1+b := by simpa only [add_comm] using add_le_add_left hb1 1
  have hq : 0<q := lt_of_lt_of_le (by simp : (0:V)<2) hq2
  have hq1 : 1≤q := le_trans (by norm_num : (1:V)≤2) hq2
  have hs : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hq2sq : 4≤q*q := by
    have h := mul_le_mul hq2 hq2 (by simp : (0:V)≤2) (by simp : (0:V)≤q)
    norm_num at h ⊢
    exact h
  have hq3 : 8≤q*(q*q) := by
    have h := mul_le_mul hq2 hq2sq (by simp : (0:V)≤4) (by simp : (0:V)≤q)
    norm_num at h ⊢
    exact h
  have hY8 : 8≤Y := le_trans hq3 (le_mul_of_one_le_right (by simp) hs)
  have hY3 : 3≤Y := le_trans (by norm_num : (3:V)≤8) hY8
  have hY : 0<Y := lt_of_lt_of_le (by simp : (0:V)<8) hY8
  have hY1 : 1≤Y := pos_iff_one_le.mp hY
  have hX : 0<X := mul_pos hq (hv 5)
  have hX1 : 1≤X := pos_iff_one_le.mp hX
  have hqcube : 1≤q*(q*q) := by
    have h := mul_le_mul hq1 (mul_le_mul hq1 hq1 (by simp) (by simp)) (by simp) (by simp)
    simpa only [one_mul] using h
  have hsY : v 6≤Y := by
    dsimp [Y]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hqcube (show (0:V)≤v 6 by simp)
  have hYQ : Y≤Q := by
    calc
      Y≤Y*Y := le_mul_of_one_le_right (by simp) hY1
      _≤X*(Y*Y) := le_mul_of_one_le_left (by simp) hX1
      _=Q := by dsimp [Q]; ring
  have hQ : 0<Q := mul_pos (mul_pos hX hY) hY
  have hk : Q*Q≤k := DirectMainPellGrowth.square_bound Q n k hQ hn hcoord
  exact three_s_of_square (v 6) Y Q k hsY hY3 hYQ hk

#print axioms Absorb89Growth.three_s_of_square
#print axioms Absorb89Growth.growth_of_index
end Absorb89Growth

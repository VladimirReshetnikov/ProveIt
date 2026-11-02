import DiophantineConsistency.AdaptiveAQ16Zeros
import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ16Positive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The positive part of the signed main value strictly exceeds its negative part. -/
theorem positive_part_dominates (U X Y k eta gamma q R : V)
    (hU : 8 ≤ U) (hY : 0 < Y) (hk : 0 < k) :
    let a := X*Y+Y
    let c := eta+Y*k
    let H := 3+4*a
    H*k < U*(X+a*c)+H*(U*gamma+X*Y*q+R+1) := by
  let a := X*Y+Y
  let c := eta+Y*k
  let H := 3+4*a
  have hy : (1:V) ≤ Y := pos_iff_one_le.mp hY
  have ha : 1 ≤ a := le_trans hy (by dsimp only [a]; simp)
  have hUY : 8 ≤ U*Y := le_trans hU (le_mul_of_one_le_right (by simp) hy)
  have hUa : 8*a ≤ U*a*Y := by
    have h := mul_le_mul_of_nonneg_right hUY (Arithmetic.zero_le a)
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  have h4a : (4:V) ≤ 4*a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha (by simp : (0:V)≤4)
  have hlt : (3:V) < 4*a := lt_of_lt_of_le (by norm_num : (3:V)<4) h4a
  have hH : H < 8*a := calc
    H = 4*a+3 := by dsimp only [H]; ring
    _ < 4*a+4*a := by simpa only [add_comm] using add_lt_add_left hlt (4*a)
    _ = 8*a := by ring
  have hH' : H < U*a*Y := lt_of_lt_of_le hH hUa
  have hk' : H*k < (U*a*Y)*k := mul_lt_mul_of_pos_right hH' hk
  have hc : Y*k ≤ c := by dsimp only [c]; simp
  have hc' : (U*a)*(Y*k) ≤ (U*a)*c := mul_le_mul_of_nonneg_left hc (by simp)
  calc
    H*k < (U*a*Y)*k := hk'
    _ = (U*a)*(Y*k) := by ring
    _ ≤ (U*a)*c := hc'
    _ ≤ U*(X+a*c) := by
      calc
        (U*a)*c = U*(a*c) := by ring
        _ ≤ U*(X+a*c) := mul_le_mul_of_nonneg_left (by simp) (by simp)
    _ ≤ U*(X+a*c)+H*(U*gamma+X*Y*q+R+1) := by simp

theorem scale_at_least_eight (J Y : V) (b : ℕ)
    (hJ : 0 < J) (hY : 0 < Y) (hb : 2 ≤ b) :
    8 ≤ Y*((1+J*(b:V))*(1+J*(b:V))) := by
  have hb' : (2:V) ≤ (b:V) := by exact_mod_cast hb
  have hJ' : (1:V) ≤ J := pos_iff_one_le.mp hJ
  have hY' : (1:V) ≤ Y := pos_iff_one_le.mp hY
  have hprod : (2:V) ≤ J*(b:V) := by
    simpa only [one_mul] using mul_le_mul hJ' hb' (by simp : (0:V)≤2) (by simp : (0:V)≤J)
  have hq : (3:V) ≤ 1+J*(b:V) := by
    calc
      (3:V) = 1+2 := by norm_num
      _ ≤ 1+J*(b:V) := add_le_add_right hprod 1
  have hq2 : (9:V) ≤ (1+J*(b:V))*(1+J*(b:V)) := by
    simpa only [show (3:V)*3=9 by norm_num] using mul_le_mul hq hq (by simp) (by simp)
  have hU : (9:V) ≤ Y*((1+J*(b:V))*(1+J*(b:V))) := by
    simpa only [one_mul] using mul_le_mul hY' hq2 (by simp : (0:V)≤9) (by simp : (0:V)≤Y)
  exact le_trans (by norm_num) hU
#print axioms positive_part_dominates
#print axioms scale_at_least_eight
end DiophantineConsistency.AdaptiveAQ16Positive

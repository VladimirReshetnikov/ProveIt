import Trace74Width3PellHeightModel
import Trace74PellGapBinding

/-! Height estimate for the same-tuple first-8/main-11 Pell branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74N8R11HeightModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74PellGapBinding Trace74Width3PellHeightModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem power_five (y : V) : power y 5=y*y*y*y*y := by
  have h2 : power y 2=y*y := by rw [show (2:V)=1+1 by norm_num,power_succ,power_one]
  have h4 : power y 4=y*y*y*y := by
    rw [show (4:V)=2+2 by norm_num,power_add,h2]
    ring
  rw [show (5:V)=4+1 by norm_num,power_succ,h4]
  ring

/-- From the width-three Pell height estimate, derive the weaker linear
height needed for the bounded quotient, at the fixed main index eleven. -/
theorem linear_height (q Y h X : V) (hq : (1073741824:V)≤q)
    (hy : q*q*q≤Y) (hh : h<q)
    (hsmall : power Y 5<32*X*X*X) :
    33554432*h*Y<X := by
  have hqpos : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hq3pos : 0<q*q*q := by positivity
  have hYpos : 0<Y := lt_of_lt_of_le hq3pos hy
  have hq3big : (1208925819614629174706176:V)<q*q*q := by
    have hs : (1152921504606846976:V)≤q*q := by
      have hm := mul_le_mul hq hq (by simp : (0:V)≤(1073741824:V)) (by simp : (0:V)≤q)
      norm_num at hm
      exact hm
    have hm := mul_le_mul hs hq (by simp : (0:V)≤(1073741824:V)) (by simp : (0:V)≤q*q)
    exact lt_of_lt_of_le (by norm_num) hm
  have hh2 : h*h≤q*q := mul_le_mul hh.le hh.le (by simp) (by simp)
  have hh3 : h*h*h≤q*q*q := mul_le_mul hh2 hh.le (by simp) (by simp)
  have hy2 : (q*q*q)*(q*q*q)≤Y*Y := mul_le_mul hy hy (by simp) (by simp)
  have hcoeff : (1208925819614629174706176:V)*(h*h*h)<Y*Y := calc
    _≤1208925819614629174706176*(q*q*q) := mul_le_mul_of_nonneg_left hh3 (by simp)
    _<(q*q*q)*(q*q*q) := mul_lt_mul_of_pos_right hq3big hq3pos
    _≤Y*Y := hy2
  have hy3pos : 0<Y*Y*Y := by positivity
  have hm := mul_lt_mul_of_pos_right hcoeff hy3pos
  have hsmall' : Y*Y*Y*Y*Y<32*X*X*X := by rwa [←power_five Y]
  let W := 33554432*h*Y
  have hcube32 : 32*(W*W*W)<32*(X*X*X) := calc
    _=(1208925819614629174706176:V)*(h*h*h)*(Y*Y*Y) := by dsimp [W]; ring
    _<(Y*Y)*(Y*Y*Y) := hm
    _=Y*Y*Y*Y*Y := by ring
    _<32*(X*X*X) := by simpa only [mul_assoc] using hsmall'
  have hcube : W*W*W<X*X*X :=
    (mul_lt_mul_iff_of_pos_left (by norm_num : (0:V)<32)).mp hcube32
  by_contra hn
  have hle : X≤W := le_of_not_gt hn
  have hsq : X*X≤W*W := mul_le_mul hle hle (by simp) (by simp)
  have hcub : X*X*X≤W*W*W := mul_le_mul hsq hle (by simp) (by simp)
  exact (not_lt_of_ge hcub) hcube

/-- Same-tuple first-8/main-11 ordinates imply the required height. No graph
zero, projection, or guard hypothesis is assumed by this theorem. -/
theorem tuple_height (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hq : (1073741824:V)≤q p v) (hv : ∀j,0<v j)
    (hfirst : 2*ycoord 8 (2*(firstParam p v-1)+1)=k v)
    (hmain : c p v=ycoord 11 (A p v-1)) :
    33554432*(b p v)*(Y p v)<X p v := by
  have hqpos : 0<q p v := lt_of_lt_of_le (by norm_num) hq
  have hY : (q p v)*(q p v)*(q p v)≤Y p v := by
    have hm := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6))
      (show (0:V)≤q p v*q p v*q p v by simp)
    simpa only [mul_one,Y,mul_assoc] using hm
  have hY1 : (1:V)≤Y p v := pos_iff_one_le.mp (lt_of_lt_of_le (by positivity) hY)
  have hX2 : (2:V)≤X p v := calc
    (2:V)≤q p v := le_trans (by norm_num) hq
    _≤v 5*q p v := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pos_iff_one_le.mp (hv 5)) (show (0:V)≤q p v by simp)
    _=X p v := rfl
  have hgap := tuple_pell_gap p v 8 11 (hv 8) hfirst hmain
  have hsmall : power (Y p v) 5<32*(X p v)*(X p v)*(X p v) := by
    have hgap' : (2*Y p v)*ycoord (((4:V)+3)+1) (2*(X p v*Y p v*Y p v-1)+1)<
        ycoord ((10:V)+1) (Y p v*(X p v+1)-1) := by
      simpa only [show ((4:V)+3)+1=8 by norm_num,show (10:V)+1=11 by norm_num] using hgap
    have hm := pell_gap_height (X p v) (Y p v) (4:V) (10:V) hX2 hY1 (by norm_num) hgap'
    simpa only [show (4:V)+1=5 by norm_num] using hm
  have hh : b p v<q p v := by
    change b p v<b p v+1
    exact lt_add_of_pos_right _ (by norm_num)
  exact linear_height (q p v) (Y p v) (b p v) (X p v) hq hY hh hsmall

#print axioms Trace74N8R11HeightModel.linear_height
#print axioms Trace74N8R11HeightModel.tuple_height
end Trace74N8R11HeightModel

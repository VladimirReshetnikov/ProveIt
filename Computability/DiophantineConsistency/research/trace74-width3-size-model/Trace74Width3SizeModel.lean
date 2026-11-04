import Trace74NearDiagonalSizeModel

/-! Width-three lower power estimate at arbitrary internal indices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74Width3SizeModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem power_two_fifteen : power (2:V) 15=32768 := by
  have h2 : power (2:V) 2=4 := by
    rw [show (2:V)=1+1 by norm_num,power_succ,power_one]
    norm_num
  have h4 : power (2:V) 4=16 := by
    rw [show (4:V)=2+2 by norm_num,power_add,h2]
    norm_num
  have h8 : power (2:V) 8=256 := by
    rw [show (8:V)=4+4 by norm_num,power_add,h4]
    norm_num
  rw [show (15:V)=(8+4+2)+1 by norm_num,power_add,power_add,power_add,h8,h4,h2,power_one]
  norm_num

/-- For the graph application take `d=n-12`; then `d+3=n-9` and
`r≤d+15` follows from `r≤n+3`. -/
theorem lower_power_bound (q Y h K d r : V)
    (hq : 1073741824≤q) (hY : q*q*q≤Y) (hh : h<q)
    (hr : r≤d+15) (hK : K=power 2 r) :
    16384*h*h*h*K*K*K*K*K*K<power Y (d+3) := by
  let P := power (2:V) d
  let B : V := 32768*P
  let Z : V := 34359738368*h
  have hp : 0<P := power_pos 2 d (by norm_num)
  have hq1 : 1≤q := le_trans (by norm_num) hq
  have hqp : 0<q := lt_of_lt_of_le (by norm_num) hq1
  have hq2large : (34359738368:V)≤q*q := by
    have hm := mul_le_mul hq hq (by simp : (0:V)≤(1073741824:V)) (by simp : (0:V)≤q)
    exact le_trans (by norm_num) hm
  have hq64 : (64:V)≤q*q*q := by
    have hq4 : (4:V)≤q := le_trans (by norm_num) hq
    have hs : (16:V)≤q*q := by
      have hm := mul_le_mul hq4 hq4 (by simp : (0:V)≤(4:V)) (by simp : (0:V)≤q)
      norm_num at hm
      exact hm
    have hm := mul_le_mul hs hq4 (by simp : (0:V)≤(4:V)) (by simp : (0:V)≤q*q)
    norm_num at hm
    exact hm
  have hy64 : (64:V)≤Y := le_trans hq64 hY
  have hypos : 0<Y := lt_of_lt_of_le (by norm_num) hy64
  have hp6 : power (64:V) d=P*P*P*P*P*P := by
    dsimp [P]
    rw [show (64:V)=2*2*2*2*2*2 by norm_num]
    repeat' rw [power_mul_base]
  have hyP : P*P*P*P*P*P≤power Y d := by
    rw [←hp6]
    exact power_mono_base 64 Y d hy64
  have hKle : K≤B := by
    rw [hK]
    calc
      power 2 r≤power 2 (d+15) := power_mono_exponent 2 r (d+15) (by norm_num) hr
      _=B := by rw [power_add,power_two_fifteen]; dsimp [P,B]; ring
  have hKsq : K*K≤B*B := mul_le_mul hKle hKle (by simp) (by simp)
  have hKcube : K*K*K≤B*B*B := mul_le_mul hKsq hKle (by simp) (by simp)
  have hKsix : K*K*K*K*K*K≤B*B*B*B*B*B := by
    have hm := mul_le_mul hKcube hKcube (by simp) (by simp)
    simpa only [mul_assoc] using hm
  have hZY : Z<Y := calc
    Z=34359738368*h := rfl
    _<34359738368*q := mul_lt_mul_of_pos_left hh (by norm_num)
    _≤(q*q)*q := mul_le_mul_of_nonneg_right hq2large (by simp)
    _≤Y := hY
  have hZsq : Z*Z≤Y*Y := mul_le_mul hZY.le hZY.le (by simp) (by simp)
  have hZcube : Z*Z*Z<Y*Y*Y := calc
    Z*Z*Z≤(Y*Y)*Z := mul_le_mul_of_nonneg_right hZsq (by simp)
    _<(Y*Y)*Y := mul_lt_mul_of_pos_left hZY (mul_pos hypos hypos)
  have hcoeff : (20282409603651670423947251286016:V)*(h*h*h)<Y*Y*Y := calc
    _≤(34359738368*34359738368*34359738368)*(h*h*h) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by simp)
    _=Z*Z*Z := by dsimp [Z]; ring
    _<Y*Y*Y := hZcube
  have hp6pos : 0<P*P*P*P*P*P := by positivity
  calc
    16384*h*h*h*K*K*K*K*K*K≤16384*(h*h*h)*(B*B*B*B*B*B) := by
      have hm := mul_le_mul_of_nonneg_left hKsix (show (0:V)≤16384*(h*h*h) by simp)
      simpa only [mul_assoc] using hm
    _=(20282409603651670423947251286016:V)*(h*h*h)*(P*P*P*P*P*P) := by dsimp [B]; ring
    _<(Y*Y*Y)*(P*P*P*P*P*P) := mul_lt_mul_of_pos_right hcoeff hp6pos
    _≤(Y*Y*Y)*power Y d := mul_le_mul_of_nonneg_left hyP (by simp)
    _=power Y (d+3) := by
      rw [power_add,show (3:V)=1+1+1 by norm_num,power_succ,power_succ,power_one]
      ring

#print axioms Trace74Width3SizeModel.lower_power_bound
end Trace74Width3SizeModel

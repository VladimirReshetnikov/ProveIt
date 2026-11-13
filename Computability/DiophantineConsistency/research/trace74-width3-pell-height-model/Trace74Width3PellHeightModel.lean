import Trace74NearDiagonalPellModel

/-! Width-three variable-index Pell height estimate in models of IΣ₁. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74Width3PellHeightModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticPellRecurrence ModelDifferenceRing
open Trace74NearDiagonalPellModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem power_three' (x : V) : power x 3=x*x*x := by
  have h : (3:V)=1+1+1 := by norm_num
  rw [h,power_succ,power_succ,power_one]
  ring

private theorem power_six' (x : V) : power x 6=x*x*x*x*x*x := by
  have h : (6:V)=(3:V)+3 := by norm_num
  rw [h,power_add,power_three']
  ring

/-- With original lower Pell index `j+4` and upper index `s+1`,
the explicit width-three index bound and strict power gap imply the
model-indexed height estimate. -/
theorem power_gap_height (X Y j s : V) (hX : 2≤X) (hY : 1≤Y)
    (hs : s≤j+6)
    (hgap : (2*Y)*power (X*(2*Y)*(2*Y)) (j+3)<
      power (2*X*(2*Y)) s) :
    power Y (j+1)<32*X*X*X := by
  let t := 2*Y
  have hX1 : 1≤X := le_trans (by norm_num) hX
  have ht : 1≤t := one_le_mul (by norm_num) hY
  have hb : 1≤2*X*t := one_le_mul (one_le_mul (by norm_num) hX1) ht
  have hgap' : t*power (X*t*t) (j+3)<power (2*X*t) (j+6) :=
    lt_of_lt_of_le hgap (power_mono_exponent (2*X*t) s (j+6) hb hs)
  have hp : 0<power X j := power_pos X j (lt_of_lt_of_le (by norm_num) hX)
  have hq : 0<power t j := power_pos t j (lt_of_lt_of_le (by norm_num) ht)
  have hr : 0<power (2:V) j := power_pos 2 j (by norm_num)
  have hx : 0<X := lt_of_lt_of_le (by norm_num) hX
  have htp : 0<t := lt_of_lt_of_le (by norm_num) ht
  let W := power X j * power t j * (t*t*t*t*t*t) * (X*X*X) * power (2:V) j
  have hw : 0<W := by dsimp [W]; positivity
  have hqeq : power t j=power (2:V) j*power Y j := by
    dsimp [t]
    exact power_mul_base 2 Y j
  rw [power_add,power_add,power_three',power_six'] at hgap'
  repeat' rw [power_mul_base] at hgap'
  have heq : power Y (j+1)=Y*power Y j := power_succ Y j
  have hfact : W*(2*power Y (j+1)) < W*(64*X*X*X) := by
    rw [heq]
    dsimp [W]
    rw [hqeq]
    dsimp [t] at hgap' ⊢
    ring_nf at hgap' ⊢
    exact hgap'
  have hsmall : 2*power Y (j+1)<64*X*X*X :=
    (mul_lt_mul_iff_of_pos_left hw).mp hfact
  apply (mul_lt_mul_iff_of_pos_left (by norm_num : (0:V)<2)).mp
  calc
    2*power Y (j+1)<64*X*X*X := hsmall
    _=2*(32*X*X*X) := by ring

/-- Width-three height estimate from the supplied strict Pell gap. -/
theorem pell_gap_height (X Y j s : V) (hX : 2≤X) (hY : 1≤Y)
    (hs : s≤j+6)
    (hgap : (2*Y)*ycoord ((j+3)+1) (2*(X*Y*Y-1)+1)<
      ycoord (s+1) (Y*(X+1)-1)) :
    power Y (j+1)<32*X*X*X :=
  power_gap_height X Y j s hX hY hs
    (trace74_strict_power_gap X Y (j+3) s hX hY hgap)

#print axioms Trace74Width3PellHeightModel.power_gap_height
#print axioms Trace74Width3PellHeightModel.pell_gap_height
end Trace74Width3PellHeightModel

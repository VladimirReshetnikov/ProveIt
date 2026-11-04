import Direct80ScaledGrowthMinus
import DiophantineConsistency.ArithmeticPellCongruences

/-! UNCHECKED DRAFT. A guard-free upper bound for the same two Pell indices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74IndexUpper
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem upper_of_ordinates (X Y n r k c eta zeta : V)
    (hX : 16≤X) (hY : 1≤Y) (hn : 2≤n)
    (hck : c=k*Y+eta) (hkez : k=eta+zeta) (hz : 0<zeta)
    (hc : c=ycoord r (Y*(X+1)-1))
    (hk : k=2*ycoord n (2*(X*Y*Y-1)+1)) : r<2*n := by
  let a : V := Y*(X+1)-1
  let B : V := 2*(X*Y*Y-1)+1
  let j : V := n-1
  have hn1 : 1≤n := le_trans (by norm_num : (1:V)≤2) hn
  have hj : j+1=n := tsub_add_cancel_of_le hn1
  have hjpos : 0<j := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    rw [hzero] at hj
    simp only [zero_add] at hj
    rw [←hj] at hn
    norm_num at hn
  have hX1 : 1≤X := le_trans (by norm_num : (1:V)≤16) hX
  have hQ : 1≤X*Y*Y := one_le_mul (one_le_mul hX1 hY) hY
  have hQe : X*Y*Y-1+1=X*Y*Y := tsub_add_cancel_of_le hQ
  have hB : B+2=2*X*Y*Y+1 := calc
    B+2=2*(X*Y*Y-1+1)+1 := by dsimp [B]; ring
    _=2*X*Y*Y+1 := by rw [hQe]; ring
  have hsep : 16*(2*(B+2))<(2*a+3)*(2*a+3) := by
    rw [hB]
    exact Direct80ScaledGrowthMinus.coefficient_gap_minus X Y hX hY
  have hlow := paired_comparison_strict a B hsep j hjpos
  have hlow' : ycoord n B<ycoord (2*j+1) a := calc
    ycoord n B ≤ Exp.exp (4*j)*ycoord n B := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_exp (4*j)) (show (0:V)≤ycoord n B by simp)
    _ < ycoord (2*j+1) a := by simpa only [hj] using hlow
  have heta : eta<k := by rw [hkez]; exact lt_add_of_pos_right eta hz
  have hclt : c<2*(Y+1)*ycoord n B := by
    rw [hck,hk]
    have hh := add_lt_add_of_le_of_lt (le_refl ((2*ycoord n B)*Y)) heta
    rw [hk] at hh
    calc
      (2*ycoord n B)*Y+eta < (2*ycoord n B)*Y+2*ycoord n B := hh
      _ = 2*(Y+1)*ycoord n B := by ring
  have hA1 : 1≤Y*(X+1) := one_le_mul hY (by simp)
  have ha : a+1=Y*(X+1) := tsub_add_cancel_of_le hA1
  have hcoeff : 2*(Y+1)≤a+2 := calc
    2*(Y+1)≤4*Y := by
      have hh := mul_le_mul_of_nonneg_left hY (by norm_num : (0:V)≤2)
      have hh' := add_le_add_left hh (2*Y)
      have hleft : 2*1+2*Y=2*(Y+1) := by ring
      have hright : 2*Y+2*Y=4*Y := by ring
      simpa only [hleft,hright] using hh'
    _≤Y*(X+1) := by
      have h4 : (4:V)≤X+1 := le_trans (by norm_num : (4:V)≤16) (le_trans hX (by simp))
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left h4 (show (0:V)≤Y by simp)
    _≤a+2 := by rw [show a+2=(a+1)+1 by ring,ha]
  have hstep : 2*(Y+1)*ycoord n B≤ycoord ((2*j+1)+1) a := calc
    2*(Y+1)*ycoord n B≤(a+2)*ycoord n B := mul_le_mul_of_nonneg_right hcoeff (by simp)
    _≤(a+2)*ycoord (2*j+1) a := mul_le_mul_of_nonneg_left (le_of_lt hlow') (by simp)
    _≤ycoord ((2*j+1)+1) a := by rw [y_succ]; simp
  have htime : (2*j+1)+1=2*n := by rw [←hj]; ring
  by_contra hnr
  have hle : 2*n≤r := le_of_not_gt hnr
  have hcontra : 2*(Y+1)*ycoord n B≤c := calc
    _≤ycoord ((2*j+1)+1) a := hstep
    _=ycoord (2*n) a := by rw [htime]
    _≤ycoord r a := (y_strictMono a).monotone hle
    _=c := hc.symm
  exact (not_le_of_gt hclt) hcontra

#print axioms Trace74IndexUpper.upper_of_ordinates
end Trace74IndexUpper

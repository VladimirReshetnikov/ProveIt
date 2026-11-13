import PellVariableGrowth
import DiophantineConsistency.ArithmeticHalfBinomialSandwich

/-! Lower Pell ratio sandwich from an explicit scaled coefficient gap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositivePellScaledSandwich
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency DiophantineConsistency.ModelDifferenceRing
open ArithmeticPellRecurrence ArithmeticPow ArithmeticHalfBinomialSandwich
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem lower_of_gap (X r a B : V) (hr : 1≤r)
    (hgap : 2*(B+2)*((X+1)*(X+1))<(2*a+3)*(2*a+3)*X) :
    2*ycoord (r+1) B*power (X+1) (2*r)<
      2*ycoord (2*r+1) a*power X r := by
  have hK : ycoord (r+1) B≤power (2*(B+2)) r := ycoord_le_power B r
  have hc : power ((2*a+3)*(2*a+3)) r≤ycoord (2*r+1) a := by
    rw [power_mul_base,←power_add,show 2*r+1=r+r+1 by ring]
    exact power_le_ycoord a (r+r)
  have hN : power (X+1) (2*r)=power ((X+1)*(X+1)) r := by
    rw [power_mul_base,←power_add,two_mul]
  have hr0 : 0<r := lt_of_lt_of_le (by simp) hr
  have hstrict := power_strict_base _ _ r hgap hr0
  rw [power_mul_base (2*(B+2)) ((X+1)*(X+1)) r,
    power_mul_base ((2*a+3)*(2*a+3)) X r] at hstrict
  calc
    2*ycoord (r+1) B*power (X+1) (2*r)≤2*power (2*(B+2)) r*power ((X+1)*(X+1)) r := by
      rw [hN]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by simp)) (by simp)
    _=2*(power (2*(B+2)) r*power ((X+1)*(X+1)) r) := by ring
    _<2*(power ((2*a+3)*(2*a+3)) r*power X r) := mul_lt_mul_of_pos_left hstrict (by simp)
    _≤2*(ycoord (2*r+1) a*power X r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (by simp)) (by simp)
    _=2*ycoord (2*r+1) a*power X r := by ring

theorem shifted_coefficient (X S : V) (hX : 1≤X) (hS : 1≤S) :
    2*(2*X*S*S+1)*((X+1)*(X+1)) < (2*(S*(X+1))+1)*(2*(S*(X+1))+1)*X := by
  apply ι_lt_ι.mp
  simp only [map_mul,map_add,map_one,map_ofNat]
  have hXR : (1:DiffRing V)≤ι X := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact hX
  have hSR : (1:DiffRing V)≤ι S := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact hS
  have h1 := mul_nonneg (sub_nonneg.mpr hSR)
    (mul_nonneg (show (0:DiffRing V)≤ι X by linarith) (show (0:DiffRing V)≤ι X+1 by linarith))
  have h2 := mul_nonneg (sub_nonneg.mpr hXR) (show (0:DiffRing V)≤ι X by linarith)
  nlinarith

#print axioms TenPositivePellScaledSandwich.lower_of_gap
#print axioms TenPositivePellScaledSandwich.shifted_coefficient
end TenPositivePellScaledSandwich

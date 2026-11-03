import PellScaledSandwich
import PellVariableGrowth
import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.ArithmeticPow
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ArithmeticHalfBinomialSandwich

/-! Upper Pell ratio sandwich from explicit coefficient and crude bounds. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositivePellScaledUpper
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open ArithmeticPellRecurrence ArithmeticPow ArithmeticHalfBinomialSandwich
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shifted_upper_coefficient (X S : V) (hX : 1≤X) (hS : 1≤S) :
    (2*(S*(X+1)+1))*(2*(S*(X+1)+1))*X*(S*(X+1))≤
      (4*X*S*S+1)*((X+1)*(X+1))*(S*(X+1)+3) := by
  apply ι_le_ι.mp
  simp only [map_mul,map_add,map_one,map_ofNat]
  have hXR : (1:DiffRing V)≤ι X := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact hX
  have hSR : (1:DiffRing V)≤ι S := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact hS
  have ha : (1:DiffRing V)≤ι S*(ι X+1) := by nlinarith
  have h1 := mul_nonneg (show (0:DiffRing V)≤ι X by linarith)
    (mul_nonneg (show (0:DiffRing V)≤ι S*(ι X+1) by linarith) (sub_nonneg.mpr ha))
  have h2 := mul_nonneg (mul_self_nonneg ((ι X:DiffRing V)+1))
    (show (0:DiffRing V)≤ι S*(ι X+1) by linarith)
  have h3 := mul_self_nonneg ((ι X:DiffRing V)+1)
  nlinarith

theorem upper_of_bounds (X r a B A0 : V) (hA : 0<A0)
    (hcoeff : (2*(a+2))*(2*(a+2))*X*A0≤(2*B+3)*((X+1)*(X+1))*(A0+3))
    (hpert : 2*r*3≤A0)
    (hcrude : 2*r*3*power (X+1) (2*r)<A0*power X r) :
    2*ycoord (2*r+1) a*power X r <
      2*ycoord (r+1) B*(power (X+1) (2*r)+power X r) := by
  let K := ycoord (r+1) B
  let C := ycoord (2*r+1) a
  let N := power (X+1) (2*r)
  let D := power X r
  have hKpos : 0<K := lt_of_lt_of_le (by simp : (0:V)<r+1) (time_le_y (r+1) B)
  have hDpos : 0<D := by
    have hD : 0<A0*D := lt_of_le_of_lt (by simp) hcrude
    exact pos_of_mul_pos_right hD (by simp)
  have hcup := ycoord_le_power a (2*r)
  have hKlow := power_le_ycoord B r
  have hcD : C*D≤power ((2*(a+2))*(2*(a+2))*X) r := by
    rw [power_mul_base,power_mul_base,←power_add,←two_mul]
    exact mul_le_mul_of_nonneg_right hcup (by simp)
  have hKN : power ((2*B+3)*((X+1)*(X+1))) r≤K*N := by
    rw [power_mul_base,power_mul_base (X+1) (X+1),←power_add,←two_mul]
    exact mul_le_mul_of_nonneg_right hKlow (by simp)
  have hraise := power_mono_base _ _ r hcoeff
  rw [power_mul_base _ A0,power_mul_base _ (A0+3)] at hraise
  have hpert' := perturbation A0 3 r hpert
  have hApow : 0<power A0 r := power_pos A0 r hA
  have hcancel : A0*power ((2*(a+2))*(2*(a+2))*X) r≤
      power ((2*B+3)*((X+1)*(X+1))) r*(A0+2*r*3) := by
    apply le_of_mul_le_mul_right _ hApow
    calc
      A0*power ((2*(a+2))*(2*(a+2))*X) r*power A0 r=
          A0*(power ((2*(a+2))*(2*(a+2))*X) r*power A0 r) := by ring
      _≤A0*(power ((2*B+3)*((X+1)*(X+1))) r*power (A0+3) r) :=
          mul_le_mul_of_nonneg_left hraise (by simp)
      _=power ((2*B+3)*((X+1)*(X+1))) r*(A0*power (A0+3) r) := by ring
      _≤power ((2*B+3)*((X+1)*(X+1))) r*((A0+2*r*3)*power A0 r) :=
          mul_le_mul_of_nonneg_left hpert' (by simp)
      _=power ((2*B+3)*((X+1)*(X+1))) r*(A0+2*r*3)*power A0 r := by ring
  have hmain : A0*(2*C*D)≤2*K*N*(A0+2*r*3) := calc
    A0*(2*C*D)=2*(A0*(C*D)) := by ring
    _≤2*(A0*power ((2*(a+2))*(2*(a+2))*X) r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcD (by simp)) (by simp)
    _≤2*(power ((2*B+3)*((X+1)*(X+1))) r*(A0+2*r*3)) :=
      mul_le_mul_of_nonneg_left hcancel (by simp)
    _≤2*(K*N*(A0+2*r*3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKN (by simp)) (by simp)
    _=2*K*N*(A0+2*r*3) := by ring
  have hfinal : A0*(2*C*D)<A0*(2*K*(N+D)) := calc
    A0*(2*C*D)≤2*K*N*(A0+2*r*3) := hmain
    _=A0*(2*K*N)+2*K*(2*r*3*N) := by ring
    _<A0*(2*K*N)+2*K*(A0*D) := add_lt_add_of_le_of_lt le_rfl
      (mul_lt_mul_of_pos_left hcrude (mul_pos (show (0:V)<2 by simp) hKpos))
    _=A0*(2*K*(N+D)) := by ring
  exact lt_of_mul_lt_mul_left hfinal (by simp)

#print axioms TenPositivePellScaledUpper.shifted_upper_coefficient
#print axioms TenPositivePellScaledUpper.upper_of_bounds
end TenPositivePellScaledUpper

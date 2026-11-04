import Trace74NearDiagonalPellModel

/-! Variable-width Pell power-gap cancellation in arbitrary IΣ₁ models. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74VariableWidthPellHeight
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticPellRecurrence ModelDifferenceRing
open Trace74NearDiagonalPellModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem p3 (x c : V) :
    power x (3*c)=power x c*power x c*power x c := by
  rw [show 3*c=c+c+c by ring,power_add,power_add]

private theorem p4 (x c : V) :
    power x (4*c)=power x c*power x c*power x c*power x c := by
  rw [show 4*c=c+c+c+c by ring,power_add,power_add,power_add]

/-- Set the lower ordinate index to `m+3c+1` and the upper one to `s+1`.
The hypothesis `s≤m+4c` is the window `r≤n+c`. -/
theorem power_gap_height (X Y m c s : V) (hX : 2≤X) (hY : 1≤Y)
    (hs : s≤m+4*c)
    (hgap : (2*Y)*power (X*(2*Y)*(2*Y)) (m+3*c)<
      power (2*X*(2*Y)) s) :
    2*power Y (m+2*c+1)<power 2 (2*c)*power X c := by
  let t : V := 2*Y
  let P : V := power X m
  let Q : V := power X c
  let D : V := power 2 m
  let E : V := power 2 c
  let F : V := power Y m
  let G : V := power Y c
  have hx : 0<X := lt_of_lt_of_le (by norm_num) hX
  have hy : 0<Y := lt_of_lt_of_le (by norm_num) hY
  have ht : 1≤t := one_le_mul (by norm_num) hY
  have hb : 1≤2*X*t := one_le_mul (one_le_mul (by norm_num) (le_trans (by norm_num) hX)) ht
  have hgap' : t*power (X*t*t) (m+3*c)<power (2*X*t) (m+4*c) :=
    lt_of_lt_of_le hgap (power_mono_exponent (2*X*t) s (m+4*c) hb hs)
  have htm : power t m=D*F := by dsimp [t,D,F]; exact power_mul_base 2 Y m
  have htc : power t c=E*G := by dsimp [t,E,G]; exact power_mul_base 2 Y c
  have hleft : power (X*t*t) (m+3*c)=
      (P*(Q*Q*Q))*((D*F)*(E*G*(E*G)*(E*G)))*((D*F)*(E*G*(E*G)*(E*G))) := by
    rw [power_mul_base,power_mul_base]
    simp only [power_add,p3,htm,htc,P,Q]
  have hright : power (2*X*t) (m+4*c)=
      (D*(E*E*E*E))*(P*(Q*Q*Q*Q))*((D*F)*(E*G*(E*G)*(E*G)*(E*G))) := by
    rw [power_mul_base,power_mul_base]
    simp only [power_add,p4,htm,htc,D,E,P,Q]
  rw [hleft,hright] at hgap'
  let W : V := P*(Q*Q*Q)*(D*D)*F*(E*E*E*E*E*E)*(G*G*G*G)
  have hw : 0<W := by
    dsimp [W,P,Q,D,E,F,G]
    have := power_pos X m hx
    have := power_pos X c hx
    have := power_pos (2:V) m (by norm_num)
    have := power_pos (2:V) c (by norm_num)
    have := power_pos Y m hy
    have := power_pos Y c hy
    positivity
  have hyexp : power Y (m+2*c+1)=F*(G*G)*Y := by
    rw [power_succ,power_add,show 2*c=c+c by ring,power_add]
    dsimp [F,G]
    ring
  have h2exp : power (2:V) (2*c)=E*E := by
    rw [show 2*c=c+c by ring,power_add]
  have hfact : W*(2*(F*(G*G)*Y))<W*((E*E)*Q) := by
    dsimp [W,t] at hgap' ⊢
    ring_nf at hgap' ⊢
    exact hgap'
  have hc := (mul_lt_mul_iff_of_pos_left hw).mp hfact
  simpa only [hyexp,h2exp] using hc

/-- The same variable-width conclusion from the strict Pell ordinate gap. -/
theorem pell_gap_height (X Y m c s : V) (hX : 2≤X) (hY : 1≤Y)
    (hs : s≤m+4*c)
    (hgap : (2*Y)*ycoord ((m+3*c)+1) (2*(X*Y*Y-1)+1)<
      ycoord (s+1) (Y*(X+1)-1)) :
    2*power Y (m+2*c+1)<power 2 (2*c)*power X c :=
  power_gap_height X Y m c s hX hY hs
    (trace74_strict_power_gap X Y (m+3*c) s hX hY hgap)

#print axioms Trace74VariableWidthPellHeight.power_gap_height
#print axioms Trace74VariableWidthPellHeight.pell_gap_height
end Trace74VariableWidthPellHeight

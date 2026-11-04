import Trace74VariableWidthPellHeight

/-! Subtraction-free variable-width model power comparison. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74VariableWidthSizeModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A represented model-power lower bound at arbitrary internal width.
The parameters `e+c=3*(m+1)` and `n=m+3c+1` avoid truncated subtraction. -/
theorem lower_power_bound (q Y h K B m c r e : V)
    (hq : power 2 B≤q) (hY : q*q*q≤Y) (hh : h≤q)
    (hK : K=power 2 r) (hr : r≤(m+3*c+1)+c)
    (he : e+c=3*(m+1))
    (hsize : 2*c*((m+3*c+1)+c)+5*c≤B*e) :
    power 2 (5*c)*power h c*power K (2*c)≤power Y (m+1) := by
  let n : V := m+3*c+1
  have hn : r≤n+c := hr
  have hsize' : 2*c*(n+c)+5*c≤B*e := hsize
  have hk : power K (2*c)≤power 2 ((n+c)*(2*c)) := calc
    power K (2*c)=power (power 2 r) (2*c) := by rw [hK]
    _=power 2 (r*(2*c)) := power_iterate 2 r (2*c)
    _≤power 2 ((n+c)*(2*c)) :=
      power_mono_exponent 2 (r*(2*c)) ((n+c)*(2*c)) (by norm_num)
        (mul_le_mul_of_nonneg_right hn (by simp))
  have hsmall : power 2 (5*c)*power K (2*c)≤power q e := calc
    power 2 (5*c)*power K (2*c)≤
        power 2 (5*c)*power 2 ((n+c)*(2*c)) :=
      mul_le_mul_of_nonneg_left hk (by simp)
    _=power 2 (5*c+(n+c)*(2*c)) := (power_add 2 (5*c) ((n+c)*(2*c))).symm
    _=power 2 (2*c*(n+c)+5*c) := by congr 1; ring
    _≤power 2 (B*e) := power_mono_exponent 2 _ _ (by norm_num) hsize'
    _=power (power 2 B) e := (power_iterate 2 B e).symm
    _≤power q e := power_mono_base (power 2 B) q e hq
  calc
    power 2 (5*c)*power h c*power K (2*c)=
        (power 2 (5*c)*power K (2*c))*power h c := by ring
    _≤power q e*power q c :=
      mul_le_mul hsmall (power_mono_base h q c hh) (by simp) (by simp)
    _=power q (e+c) := (power_add q e c).symm
    _=power q (3*(m+1)) := by rw [he]
    _=power (power q 3) (m+1) := (power_iterate q 3 (m+1)).symm
    _=power (q*q*q) (m+1) := by
      have hcube : power q 3=q*q*q := by
        rw [show (3:V)=1+1+1 by norm_num,power_succ,power_succ,power_one]
        ring
      rw [hcube]
    _≤power Y (m+1) := power_mono_base (q*q*q) Y (m+1) hY

#print axioms Trace74VariableWidthSizeModel.lower_power_bound
end Trace74VariableWidthSizeModel

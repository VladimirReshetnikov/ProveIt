import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Arithmetic estimates for the auxiliary-seed shift threshold. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThresholdArithmetic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The displayed seed estimates force the auxiliary multiplier beyond c³. -/
theorem auxiliary_T_exceeds_cube (c I f T u R : V)
    (hc : 0<c) (hI : 2*c*c≤I) (hf : f*f≤2*I*I) (hu : I^4≤u)
    (he : f*f*c*T=u+c+f*f*R) : c^3<T := by
  have hIpos : 0<I := lt_of_lt_of_le (mul_pos (mul_pos (by norm_num : (0:V)<2) hc) hc) hI
  have hI2pos : 0<I*I := mul_pos hIpos hIpos
  have hc4pos : 0<c^4 := pow_pos hc _
  have hI2 : (2*c*c)*(2*c*c)≤I*I := mul_le_mul hI hI (by simp) (by simp)
  have hlt : 2*c^4<I*I := calc
    2*c^4<2*c^4+2*c^4 := lt_add_of_pos_right _ (mul_pos (by norm_num) hc4pos)
    _=(2*c*c)*(2*c*c) := by ring
    _≤I*I := hI2
  have hlt' : 2*I*I*c^4<I^4 := calc
    2*I*I*c^4=(I*I)*(2*c^4) := by ring
    _<(I*I)*(I*I) := mul_lt_mul_of_pos_left hlt hI2pos
    _=I^4 := by ring
  by_contra hn
  have hT : T≤c^3 := le_of_not_gt hn
  have hupper : I^4≤2*I*I*c^4 := calc
    I^4≤u := hu
    _≤u+c+f*f*R := by simp
    _=f*f*c*T := he.symm
    _≤f*f*c*(c^3) := mul_le_mul_of_nonneg_left hT (by simp)
    _≤(2*I*I)*c*(c^3) := by gcongr
    _=2*I*I*c^4 := by ring
  exact (not_le_of_gt hlt') hupper

/-- Outer-coordinate bounds put the symmetry's T decrement below c³. -/
theorem shift_decrement_le_cube (b q Y c : V)
    (hq : 1≤q) (hb : b≤q) (hY : Y≤c) (hq3 : q^3≤c) :
    b*(Y*(q*q))*(q*q-1)≤c^3 := by
  have hq2 : q*q≤q^3 := calc
    q*q≤(q*q)*q := le_mul_of_one_le_right (by simp) hq
    _=q^3 := by ring
  have hq5 : q*(q*q)*(q*q)≤q^3*q^3 := calc
    q*(q*q)*(q*q)=q^3*(q*q) := by ring
    _≤q^3*q^3 := mul_le_mul_of_nonneg_left hq2 (by simp)
  calc
    b*(Y*(q*q))*(q*q-1)≤q*(c*(q*q))*(q*q) := by gcongr; simp_all
    _=c*(q*(q*q)*(q*q)) := by ring
    _≤c*(q^3*q^3) := mul_le_mul_of_nonneg_left hq5 (by simp)
    _≤c*(c*c) := by gcongr
    _=c^3 := by ring

/-- These explicit seed and outer estimates imply the shift threshold. -/
theorem auxiliary_T_exceeds_shift (b q Y c I f T u R : V)
    (hc : 0<c) (hq : 1≤q) (hb : b≤q) (hY : Y≤c) (hq3 : q^3≤c)
    (hI : 2*c*c≤I) (hf : f*f≤2*I*I) (hu : I^4≤u)
    (he : f*f*c*T=u+c+f*f*R) : b*(Y*(q*q))*(q*q-1)<T :=
  lt_of_le_of_lt (shift_decrement_le_cube b q Y c hq hb hY hq3)
    (auxiliary_T_exceeds_cube c I f T u R hc hI hf hu he)
end DiophantineConsistency.AdaptiveGap85ThresholdArithmetic

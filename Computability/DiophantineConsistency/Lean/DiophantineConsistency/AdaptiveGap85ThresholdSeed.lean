import DiophantineConsistency.ArithmeticPellResidueClasses

/-! Pell and strong-norm estimates for a large auxiliary multiplier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThresholdSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellResidueClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The positive strong seed implies the coefficient and quotient bounds. -/
theorem strong_seed_estimates (a c i f I : V) (hc : 0<c) (hi : 0<i) (hf : 0<f)
    (hI : I=delta a*i*c*c) (hnorm : I*I+delta a=delta a*(f*f)) :
    2*c*c≤I ∧ f*f≤2*I*I := by
  have hd : (2:V)≤delta a := by
    unfold delta
    calc
      (2:V)≤a+3 := le_trans (by norm_num : (2:V)≤3) (by simp)
      _≤(a+1)*(a+3) := le_mul_of_one_le_left (by simp) (by simp)
  have hi1 : 1≤i := pos_iff_one_le.mp hi
  have hbase : 2≤delta a*i := le_trans hd (le_mul_of_one_le_right (by simp) hi1)
  have hdc : 2*c*c≤I := by
    rw [hI]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbase (by simp)) (by simp)
  have hIpos : 0<I := lt_of_lt_of_le (mul_pos (mul_pos (by norm_num : (0:V)<2) hc) hc) hdc
  have hI1 : 1≤I*I := one_le_mul (pos_iff_one_le.mp hIpos) (pos_iff_one_le.mp hIpos)
  have hf1 : 1≤f*f := one_le_mul (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  let z : V := f*f-1
  have hz : z+1=f*f := tsub_add_cancel_of_le hf1
  have hIz : I*I=delta a*z := by
    apply add_right_cancel (b:=delta a)
    calc
      I*I+delta a=delta a*(f*f) := hnorm
      _=delta a*(z+1) := by rw [hz]
      _=delta a*z+delta a := by ring
  have hd1 : 1≤delta a := le_trans (by norm_num : (1:V)≤2) hd
  have hle : z≤I*I := by rw [hIz]; exact le_mul_of_one_le_left (by simp) hd1
  have hff : f*f≤2*I*I := calc
    f*f=z+1 := hz.symm
    _≤I*I+1 := add_le_add hle (le_refl 1)
    _≤I*I+I*I := by simpa only [add_comm] using add_le_add_left hI1 (I*I)
    _=2*I*I := by ring
  exact ⟨hdc,hff⟩

/-- An odd Pell abscissa at index at least five forces u≥I⁴. -/
theorem odd_quotient_growth (I R u : V) (hI : 2≤I) (hR : 5≤R)
    (hux : xcoord R (I-2)=I*u) : I^4≤u := by
  let b : V := I-2
  have hb : b+2=I := tsub_add_cancel_of_le hI
  have hIpos : 0<I := lt_of_lt_of_le (by norm_num : (0:V)<2) hI
  have hstep (t : V) : I*xcoord t b≤xcoord (t+1) b := by
    rw [x_succ,hb]
    simp
  have h1 : I≤xcoord 1 b := by simpa using hstep (0:V)
  have h2 : I^2≤xcoord 2 b := calc
    I^2=I*I := by ring
    _≤I*xcoord 1 b := mul_le_mul_of_nonneg_left h1 (by simp)
    _≤xcoord 2 b := by simpa only [one_add_one_eq_two] using hstep 1
  have h3 : I^3≤xcoord 3 b := calc
    I^3=I*(I^2) := by ring
    _≤I*xcoord 2 b := mul_le_mul_of_nonneg_left h2 (by simp)
    _≤xcoord 3 b := by simpa only [show (2:V)+1=3 by norm_num] using hstep 2
  have h4 : I^4≤xcoord 4 b := calc
    I^4=I*(I^3) := by ring
    _≤I*xcoord 3 b := mul_le_mul_of_nonneg_left h3 (by simp)
    _≤xcoord 4 b := by simpa only [show (3:V)+1=4 by norm_num] using hstep 3
  have h5 : I^5≤xcoord 5 b := calc
    I^5=I*(I^4) := by ring
    _≤I*xcoord 4 b := mul_le_mul_of_nonneg_left h4 (by simp)
    _≤xcoord 5 b := by simpa only [show (4:V)+1=5 by norm_num] using hstep 4
  have hle : I*(I^4)≤I*u := calc
    _=I^5 := by ring
    _≤xcoord 5 b := h5
    _≤xcoord R b := (x_strictMono b).monotone hR
    _=I*u := hux
  exact le_of_mul_le_mul_left hle hIpos
end DiophantineConsistency.AdaptiveGap85ThresholdSeed

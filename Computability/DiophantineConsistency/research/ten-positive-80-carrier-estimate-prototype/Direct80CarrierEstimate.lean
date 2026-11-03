import AdjacentBounds
import DiophantineConsistency.ArithmeticPellHalfIndex

/-! A conditional first carrier estimate from adjacent Pell and signed residue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80CarrierEstimate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellHalfIndex TenPositiveAdjacentBounds
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem adjacent_carrier_bound (B F c v y tau f : V)
    (hB : 0<B) (hBc : c<B) (hc : 1<c) (hv : 0<v) (ht : 0<tau) (hf : 0<f)
    (hnorm : (1+B)*(v*v)=1+B*(y*y))
    (hsign : SignMod F v c) (hcF : 2*c<F) (htfF : 8*tau*f≤F) :
    2*(tau*f*y)<v*v := by
  have hFpos : 0<F := lt_of_le_of_lt (by simp) hcF
  have hcpos : 0<c := lt_trans (by simp) hc
  have hvne : v≠c := by
    intro heq
    have hnormc : (1+B)*((1*c)*(1*c))=1*1+B*(y*y) := by simpa [heq] using hnorm
    have h := adjacent_order B 1 c y (by simp) hc hnormc
    have hcy : c<y := by simpa using h.1
    have hupper : B*y<(1+B)*c := by simpa using h.2
    have hc1 : c+1≤y := lt_iff_succ_le.mp hcy
    have hlt : B*c+B<B*c+c := calc
      B*c+B=B*(c+1) := by ring
      _≤B*y := mul_le_mul_of_nonneg_left hc1 (by simp)
      _<(1+B)*c := hupper
      _=B*c+c := by ring
    have hBc' : B<c := (add_lt_add_iff_left (B*c)).mp hlt
    exact (not_lt_of_ge (le_of_lt hBc)) hBc'
  have hFv : F≤2*v := by
    by_contra hn
    have hsmall : 2*v<F := lt_of_not_ge hn
    exact hvne (sign_eq_of_half hv hcpos hsmall hcF hsign)
  have htf : 1≤tau*f := pos_iff_one_le.mp (mul_pos ht hf)
  have h8 : (8:V)≤F := calc
    8=8*1 := by ring
    _≤8*(tau*f) := mul_le_mul_of_nonneg_left htf (by simp)
    _=8*tau*f := by ring
    _≤F := htfF
  have hvlarge : 1<v := by
    by_contra hn
    have hvle : v≤1 := le_of_not_gt hn
    have htwo : 2*v≤2 := by simpa using mul_le_mul_of_nonneg_left hvle (show (0:V)≤2 by simp)
    have hbad : (8:V)≤2 := le_trans h8 (le_trans hFv htwo)
    norm_num at hbad
  have hnorm' : (1+B)*((1*v)*(1*v))=1*1+B*(y*y) := by simpa using hnorm
  have hupper : B*y<(1+B)*v := by simpa using (adjacent_order B 1 v y (by simp) hvlarge hnorm').2
  have hB1 : 1≤B := pos_iff_one_le.mp hB
  have hQB : 1+B≤2*B := by
    calc
      1+B≤B+B := _root_.add_le_add hB1 (le_refl B)
      _=2*B := by ring
  have hylt : y<2*v := (mul_lt_mul_iff_of_pos_left hB).mp (calc
    B*y<(1+B)*v := hupper
    _≤(2*B)*v := mul_le_mul_of_nonneg_right hQB (by simp)
    _=B*(2*v) := by ring)
  have hfour : 4*tau*f≤v := (mul_le_mul_iff_of_pos_left (by norm_num : (0:V)<2)).mp (calc
    2*(4*tau*f)=8*tau*f := by ring
    _≤F := htfF
    _≤2*v := hFv)
  calc
    2*(tau*f*y)<(2*(tau*f))*(2*v) := by
      simpa only [mul_assoc] using mul_lt_mul_of_pos_left hylt (mul_pos (by simp) (mul_pos ht hf))
    _=(4*tau*f)*v := by ring
    _≤v*v := mul_le_mul_of_nonneg_right hfour (by simp)

#print axioms Direct80CarrierEstimate.adjacent_carrier_bound
end Direct80CarrierEstimate

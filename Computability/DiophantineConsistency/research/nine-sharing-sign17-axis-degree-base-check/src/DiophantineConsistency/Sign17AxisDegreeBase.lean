import DiophantineConsistency.Sign17UnivariateDegreeProbe

/-! SOURCE-ONLY: base univariate factors for the sign17 diagonal axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisDegreeBase
open Sign17UnivariateDegree

abbrev shift : P := Polynomial.X + 1
abbrev affine (z : ℤ) : P := Polynomial.C z * shift + 1

theorem shift_degree : shift.natDegree = 1 := by
  have h : (1 : P).natDegree < (Polynomial.X : P).natDegree := by simp
  simpa [shift] using dominant_add (Polynomial.X : P) 1 h

theorem shift_ne_zero : shift ≠ 0 := by
  intro h
  have h' := shift_degree
  rw [h] at h'
  simp at h'

theorem affine_degree (z : ℤ) (hz : z ≠ 0) : (affine z).natDegree = 1 := by
  have hm : (Polynomial.C z * shift).natDegree = 1 := by
    rw [product_degree _ _ (Polynomial.C_ne_zero.mpr hz) shift_ne_zero]
    simp [shift_degree]
  have h : (1 : P).natDegree < (Polynomial.C z * shift).natDegree := by
    rw [hm]
    simp
  simpa [affine, hm] using dominant_add (Polynomial.C z * shift) 1 h

end DiophantineConsistency.Sign17AxisDegreeBase
#print axioms DiophantineConsistency.Sign17AxisDegreeBase.shift_degree
#print axioms DiophantineConsistency.Sign17AxisDegreeBase.shift_ne_zero
#print axioms DiophantineConsistency.Sign17AxisDegreeBase.affine_degree

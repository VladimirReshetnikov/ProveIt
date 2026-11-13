import DiophantineConsistency.Sign17AxisDegreeRoot

/-! SOURCE-ONLY: root and scale degrees on the explicit axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisDegreeScale
open Sign17UnivariateDegree Sign17AxisDegreeBase Sign17AxisDegreeRoot

abbrev low (z : ℤ) : P := Polynomial.X * affine z + Polynomial.C z * shift
abbrev middle (z : ℤ) : P := shift * (Polynomial.C 4 * (e z + y z) + 3)
abbrev root (z : ℤ) : P := (low z + dominant z) + middle z
abbrev scale (z : ℤ) : P := (shift * root z) * (root z + 2)

theorem low_degree (z : ℤ) (hz : z ≠ 0) : (low z).natDegree = 2 := by
  have ha : (Polynomial.X * affine z).natDegree = 2 := by
    simpa using degree_product (Polynomial.X : P) (affine z) 1 1
      Polynomial.natDegree_X (affine_degree z hz) (by decide) (by decide)
  have hb : (Polynomial.C z * shift).natDegree = 1 := by
    rw [product_degree _ _ (Polynomial.C_ne_zero.mpr hz) shift_ne_zero]
    simp [shift_degree]
  exact degree_sum _ _ 2 1 ha hb (by decide)

theorem middle_degree (z : ℤ) (hz : z ≠ 0) : (middle z).natDegree = 7 := by
  have h : (e z + y z).natDegree = 6 :=
    degree_sum (e z) (y z) 6 4 (e_degree z hz) (y_degree z hz) (by decide)
  have hm : (Polynomial.C (4 : ℤ) * (e z + y z)).natDegree = 6 := by
    rw [product_degree _ _ (Polynomial.C_ne_zero.mpr (by decide))
      (ne_zero_of_positive_degree _ _ h (by decide)), h]
    simp
  have hs : (Polynomial.C (4 : ℤ) * (e z + y z) + 3).natDegree = 6 := by
    exact degree_sum _ _ 6 0 hm (by simp) (by decide)
  change (shift * (Polynomial.C 4 * (e z + y z) + 3)).natDegree = 7
  simpa using degree_product shift _ 1 6 shift_degree hs (by decide) (by decide)

theorem root_degree (z : ℤ) (hz : z ≠ 0) : (root z).natDegree = 11 := by
  have h : (low z + dominant z).natDegree = 11 := by
    rw [add_comm]
    exact degree_sum _ _ 11 2 (dominant_degree z hz) (low_degree z hz) (by decide)
  exact degree_sum _ _ 11 7 h (middle_degree z hz) (by decide)

theorem scale_degree (z : ℤ) (hz : z ≠ 0) : (scale z).natDegree = 23 := by
  have hr : (root z + 2).natDegree = 11 :=
    degree_sum _ _ 11 0 (root_degree z hz) (by simp) (by decide)
  have hs : (shift * root z).natDegree = 12 := by
    simpa using degree_product shift (root z) 1 11 shift_degree
      (root_degree z hz) (by decide) (by decide)
  change ((shift * root z) * (root z + 2)).natDegree = 23
  simpa using degree_product (shift * root z) (root z + 2) 12 11 hs hr
    (by decide) (by decide)

end DiophantineConsistency.Sign17AxisDegreeScale
#print axioms DiophantineConsistency.Sign17AxisDegreeScale.low_degree
#print axioms DiophantineConsistency.Sign17AxisDegreeScale.middle_degree
#print axioms DiophantineConsistency.Sign17AxisDegreeScale.root_degree
#print axioms DiophantineConsistency.Sign17AxisDegreeScale.scale_degree

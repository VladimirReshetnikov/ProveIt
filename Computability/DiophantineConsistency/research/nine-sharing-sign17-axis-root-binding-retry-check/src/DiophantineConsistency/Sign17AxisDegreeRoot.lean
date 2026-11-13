import DiophantineConsistency.Sign17AxisDegreeBase

/-! SOURCE-ONLY: compositional axis-degree ingredients; binding is separate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisDegreeRoot
open Sign17UnivariateDegree Sign17AxisDegreeBase

theorem ne_zero_of_positive_degree (p : P) (n : ℕ)
    (h : p.natDegree = n) (hn : 0 < n) : p ≠ 0 := by
  intro hp
  rw [hp] at h
  simp at h
  omega

theorem degree_product (p q : P) (m n : ℕ) (hp : p.natDegree = m)
    (hq : q.natDegree = n) (hm : 0 < m) (hn : 0 < n) :
    (p * q).natDegree = m + n := by
  rw [product_degree _ _ (ne_zero_of_positive_degree _ _ hp hm)
    (ne_zero_of_positive_degree _ _ hq hn), hp, hq]

theorem degree_sum (p q : P) (m n : ℕ) (hp : p.natDegree = m)
    (hq : q.natDegree = n) (h : n < m) : (p + q).natDegree = m := by
  have h' : q.natDegree < p.natDegree := by omega
  calc
    (p + q).natDegree = p.natDegree := dominant_add p q h'
    _ = m := hp

abbrev twice : P := Polynomial.C 2 * shift
abbrev cube (z : ℤ) : P := (affine z * affine z) * affine z
abbrev y (z : ℤ) : P := shift * cube z
abbrev e (z : ℤ) : P := (shift * affine z) * y z
abbrev u (z : ℤ) : P := (twice * y z) + shift
abbrev dominant (z : ℤ) : P := (e z + y z) * u z

theorem twice_degree : twice.natDegree = 1 := by
  change (Polynomial.C (2 : ℤ) * shift).natDegree = 1
  rw [product_degree _ _ (Polynomial.C_ne_zero.mpr (by decide)) shift_ne_zero]
  simp [shift_degree]

theorem cube_degree (z : ℤ) (hz : z ≠ 0) : (cube z).natDegree = 3 := by
  have a := affine_degree z hz
  have h : (affine z * affine z).natDegree = 2 := by
    simpa using degree_product (affine z) (affine z) 1 1 a a (by decide) (by decide)
  simpa [cube] using degree_product (affine z * affine z) (affine z) 2 1 h a (by decide) (by decide)

theorem y_degree (z : ℤ) (hz : z ≠ 0) : (y z).natDegree = 4 := by
  simpa [y] using degree_product shift (cube z) 1 3 shift_degree
    (cube_degree z hz) (by decide) (by decide)

theorem e_degree (z : ℤ) (hz : z ≠ 0) : (e z).natDegree = 6 := by
  have h : (shift * affine z).natDegree = 2 := by
    simpa using degree_product shift (affine z) 1 1 shift_degree
      (affine_degree z hz) (by decide) (by decide)
  simpa [e] using degree_product (shift * affine z) (y z) 2 4 h
    (y_degree z hz) (by decide) (by decide)

theorem u_degree (z : ℤ) (hz : z ≠ 0) : (u z).natDegree = 5 := by
  have h : (twice * y z).natDegree = 5 := by
    simpa using degree_product twice (y z) 1 4 twice_degree
      (y_degree z hz) (by decide) (by decide)
  simpa [u] using degree_sum (twice * y z) shift 5 1 h shift_degree (by decide)

theorem dominant_degree (z : ℤ) (hz : z ≠ 0) : (dominant z).natDegree = 11 := by
  have h : (e z + y z).natDegree = 6 :=
    degree_sum (e z) (y z) 6 4 (e_degree z hz) (y_degree z hz) (by decide)
  simpa [dominant] using degree_product (e z + y z) (u z) 6 5 h
    (u_degree z hz) (by decide) (by decide)

end DiophantineConsistency.Sign17AxisDegreeRoot
#print axioms DiophantineConsistency.Sign17AxisDegreeRoot.twice_degree
#print axioms DiophantineConsistency.Sign17AxisDegreeRoot.y_degree
#print axioms DiophantineConsistency.Sign17AxisDegreeRoot.e_degree
#print axioms DiophantineConsistency.Sign17AxisDegreeRoot.u_degree
#print axioms DiophantineConsistency.Sign17AxisDegreeRoot.dominant_degree

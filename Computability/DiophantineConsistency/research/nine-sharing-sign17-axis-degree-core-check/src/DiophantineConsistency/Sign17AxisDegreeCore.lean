import DiophantineConsistency.Sign17DegreeCompose

/-! SOURCE-ONLY: first exact-degree ingredients on a univariate axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisDegree
open MvPolynomial

abbrev P := MvPolynomial (Fin 1) ℤ

theorem nonzero_of_degree_pos (p : P) (h : 0 < p.totalDegree) : p ≠ 0 := by
  intro hz
  rw [hz] at h
  simp at h

theorem product_degree (p q : P) (hp : 0 < p.totalDegree) (hq : 0 < q.totalDegree) :
    (p*q).totalDegree = p.totalDegree + q.totalDegree :=
  MvPolynomial.totalDegree_mul_of_isDomain (nonzero_of_degree_pos p hp) (nonzero_of_degree_pos q hq)

theorem dominant_add (p q : P) (h : q.totalDegree < p.totalDegree) :
    (p+q).totalDegree = p.totalDegree :=
  MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt h

def shift : P := X 0 + 1

def base (z : ℤ) : P := C z * shift + 1

theorem shift_degree : shift.totalDegree = 1 := by
  unfold shift
  rw [dominant_add (X 0) 1 (by simp [MvPolynomial.totalDegree_X])]
  simp [MvPolynomial.totalDegree_X]

theorem base_degree (z : ℤ) (hz : z ≠ 0) : (base z).totalDegree = 1 := by
  have hc : (C z : P) ≠ 0 := MvPolynomial.C_ne_zero.mpr hz
  have hs : shift ≠ 0 := nonzero_of_degree_pos shift (by rw [shift_degree]; decide)
  have hm : ((C z : P)*shift).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hc hs, MvPolynomial.totalDegree_C, shift_degree]
    simp
  unfold base
  rw [dominant_add ((C z : P)*shift) 1 (by rw [hm]; simp), hm]
end DiophantineConsistency.Sign17AxisDegree
#print axioms DiophantineConsistency.Sign17AxisDegree.product_degree
#print axioms DiophantineConsistency.Sign17AxisDegree.dominant_add
#print axioms DiophantineConsistency.Sign17AxisDegree.shift_degree
#print axioms DiophantineConsistency.Sign17AxisDegree.base_degree

import DiophantineConsistency.Sign17AxisOtherDegree

/-! SOURCE-ONLY: Na square dominates the other seven squares on the axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisNoncancel
open SharingSeed17Degree96 Sign17UnivariateDegree Sign17AxisRootBinding
  Sign17AxisDegreeRoot Sign17AxisNaDegree Sign17AxisOtherDegree

def otherSum (p : Fin 4 → ℤ) : P :=
  ((otherRows p).map fun e => e.evalRing axis * e.evalRing axis).sum

theorem list_sum_degree_le (xs : List P) (n : ℕ)
    (h : ∀ x ∈ xs, x.natDegree ≤ n) : xs.sum.natDegree ≤ n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x.natDegree ≤ n := h x (by simp)
    have ht : xs.sum.natDegree ≤ n := ih (by
      intro y hy
      exact h y (by simp [hy]))
    simpa using (Polynomial.natDegree_add_le_of_le hx ht)

theorem other_sum_degree_le (p : Fin 4 → ℤ) : (otherSum p).natDegree ≤ 92 := by
  apply list_sum_degree_le
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  have h := other_rows_axis_degree p e he
  have hm := (Polynomial.natDegree_mul_le (p := e.evalRing axis) (q := e.evalRing axis))
  omega

theorem na_square_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    ((row06 p).evalRing axis * (row06 p).evalRing axis).natDegree = 96 := by
  have h := row06_axis_degree p hz
  simpa using degree_product ((row06 p).evalRing axis) ((row06 p).evalRing axis)
    48 48 h h (by decide) (by decide)

theorem combined_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    (((row06 p).evalRing axis * (row06 p).evalRing axis) + otherSum p).natDegree = 96 := by
  have ha := na_square_degree p hz
  have hb := other_sum_degree_le p
  calc
    (((row06 p).evalRing axis * (row06 p).evalRing axis) + otherSum p).natDegree =
        ((row06 p).evalRing axis * (row06 p).evalRing axis).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega)
    _ = 96 := ha

end DiophantineConsistency.Sign17AxisNoncancel
#print axioms DiophantineConsistency.Sign17AxisNoncancel.other_sum_degree_le
#print axioms DiophantineConsistency.Sign17AxisNoncancel.na_square_degree
#print axioms DiophantineConsistency.Sign17AxisNoncancel.combined_degree

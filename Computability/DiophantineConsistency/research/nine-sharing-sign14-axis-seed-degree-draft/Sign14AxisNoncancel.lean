import DiophantineConsistency.Sign14AxisOtherDegree

/-! SOURCE-ONLY: Na square dominates the other seven squares on the axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisNoncancel
open SharingSeed14Degree124 Sign17UnivariateDegree Sign14AxisBinding
  Sign17AxisDegreeRoot Sign14AxisNaBinding Sign14AxisOtherDegree

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
    ((row03 p).evalRing axis * (row03 p).evalRing axis).natDegree = 124 := by
  have h := row03_axis_degree p hz
  simpa using degree_product ((row03 p).evalRing axis) ((row03 p).evalRing axis)
    62 62 h h (by decide) (by decide)

theorem combined_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    (((row03 p).evalRing axis * (row03 p).evalRing axis) + otherSum p).natDegree = 124 := by
  have ha := na_square_degree p hz
  have hb := other_sum_degree_le p
  calc
    (((row03 p).evalRing axis * (row03 p).evalRing axis) + otherSum p).natDegree =
        ((row03 p).evalRing axis * (row03 p).evalRing axis).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega)
    _ = 124 := ha

end DiophantineConsistency.Sign14AxisNoncancel
#print axioms DiophantineConsistency.Sign14AxisNoncancel.other_sum_degree_le
#print axioms DiophantineConsistency.Sign14AxisNoncancel.na_square_degree
#print axioms DiophantineConsistency.Sign14AxisNoncancel.combined_degree

import PA194ADTable
set_option autoImplicit false
namespace PA194ADTable

theorem ordinary_rows (i : Nat) (h₁ : i ≠ 219) (h₂ : i ≠ 221)
    (h₃ : i ≠ 249) :
    adRows.getD i (0,0,194) = PA194Rows.rows.getD i (0,0,194) := by
  rw [exact_table]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h₃),
    List.getElem?_set_ne (Ne.symm h₂), List.getElem?_set_ne (Ne.symm h₁)]

#print axioms ordinary_rows
end PA194ADTable

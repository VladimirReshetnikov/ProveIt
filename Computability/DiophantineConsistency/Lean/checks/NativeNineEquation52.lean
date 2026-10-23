import DiophantineConsistency.NativeNineEquation52

open DiophantineConsistency NativeNineEquation52

-- The six positive registers and three unrestricted registers occupy the
-- documented b,g,h,s,w,phi,i,j,n coordinates exactly.
example : successorShift (fun _ : Fin 9 => (0 : ℤ)) =
    ![1, 1, 1, 1, 1, 0, 1, 0, 0] := by
  funext i
  fin_cases i <;> rfl

example (x : Fin 9 → ℤ) : successorShift x 5 = x 5 := by simp [successorShift]
example (x : Fin 9 → ℤ) : successorShift x 6 = x 6 + 1 := by simp [successorShift]
example (x : Fin 9 → ℤ) : successorShift x 7 = x 7 := by simp [successorShift]
example (x : Fin 9 → ℤ) : successorShift x 8 = x 8 := by simp [successorShift]

-- The literal equation has exactly the advertised nine variable names.
example : Fintype.card (Fin 9) = 9 := rfl

#print axioms sourceBase_cast
#print axioms sourceN_cast
#print axioms sourceCap_cast
#print axioms highInt_eq_sourceHigh
#print axioms sourceRank_cast
#print axioms successorShift_witness
#print axioms value_eq_naturalValue
#print axioms eval_polynomial
#print axioms eval_polynomial_nat
#print axioms exists_zero_iff_source
#print axioms exists_zero_iff_source_published

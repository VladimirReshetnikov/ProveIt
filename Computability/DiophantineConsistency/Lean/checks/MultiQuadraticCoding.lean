import DiophantineConsistency.MultiQuadraticCoding

open DiophantineConsistency
open SidonPositions QuadraticCoding MultiQuadraticCoding

private def u (i : Fin 2) : ℤ := if i = 0 then 1 else 3
private def rows (j : Fin 2) (p : PairIndex 1) : ℤ :=
  if j = 0 then
    (if p.val.1 = 0 then (if p.val.2 = 0 then 5 else 7) else 11)
  else -1

example : target 1 0 = 8 := by decide
example : target 1 1 = 25 := by decide
example : targetBound 1 2 = 34 := by decide

/-- The two row values include a signed quadratic. -/
example : quadraticValue (rows 0) u = 125 := by decide
example : quadraticValue (rows 1) u = -13 := by decide

/-- Both coefficients are selected from the very same combined polynomial. -/
example : (encoded u ^ 2 * combined rows).coeff 8 = 250 := by
  have h := coeff_square_mul_combined rows u 0
  have hv : quadraticValue (rows 0) u = 125 := by decide
  norm_num [target, stride, coefficientPosition, hv] at h
  exact h

example : (encoded u ^ 2 * combined rows).coeff 25 = -26 := by
  have h := coeff_square_mul_combined rows u 1
  have hv : quadraticValue (rows 1) u = -13 := by decide
  norm_num [target, stride, coefficientPosition, hv] at h
  exact h

/-- The first row's entire product is zero just beyond its support interval. -/
example : (encoded u ^ 2 * complementary (rows 0) 8).coeff 17 = 0 := by
  apply coeff_row_eq_zero_of_outside (j := 0)
  right
  norm_num [target, stride, coefficientPosition]

/-- An empty row family constructs the zero complementary polynomial. -/
example (a : Fin 0 → PairIndex 1 → ℤ) : combined a = 0 := by simp [combined]

/-- With no variable coordinates, different constant rows still separate. -/
example (a : Fin 2 → PairIndex 0 → ℤ) (v : Fin 1 → ℤ) :
    (encoded v ^ 2 * combined a).coeff 1 = 2 * quadraticValue (a 1) v := by
  simpa [target, stride, coefficientPosition] using coeff_square_mul_combined a v 1

#print axioms coeff_row_eq_zero_of_outside
#print axioms coeff_square_mul_combined
#print axioms targetBound_eq

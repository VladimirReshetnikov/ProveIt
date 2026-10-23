import DiophantineConsistency.QuadraticCoding

open DiophantineConsistency
open SidonPositions QuadraticCoding

private def u (i : Fin 2) : ℤ := if i = 0 then 1 else 3
private def a (p : PairIndex 1) : ℤ :=
  if p.val.1 = 0 then (if p.val.2 = 0 then 5 else 7) else 11

/-- C=1+3X^4 has the expected diagonal and off-diagonal square coefficients. -/
example : (encoded u ^ 2).coeff 0 = 1 := by
  have h := coeff_encoded_square_diagonal u 0
  norm_num [u, weight, radix] at h
  exact h

example : (encoded u ^ 2).coeff 4 = 6 := by
  have h := coeff_encoded_square_offDiagonal u 0 1 (by decide)
  norm_num [u, weight, radix] at h
  exact h

example : (encoded u ^ 2).coeff 8 = 9 := by
  have h := coeff_encoded_square_diagonal u 1
  norm_num [u, weight, radix] at h
  exact h

/-- The supplied quadratic is 5*1²+7*1*3+11*3². -/
example : quadraticValue a u = 125 := by decide

/-- Its coefficient extraction is 10+42+198=250 at the cubic position eight. -/
example : (encoded u ^ 2 * complementary a 8).coeff 8 = 250 := by
  have h := coeff_square_mul_complementary_cubic a u
  have hv : quadraticValue a u = 125 := by decide
  norm_num [coefficientPosition, hv] at h
  exact h

/-- The degenerate constant-only dimension also satisfies the generic identity. -/
example (b : PairIndex 0 → ℤ) (v : Fin 1 → ℤ) :
    (encoded v ^ 2 * complementary b 0).coeff 0 = 2 * quadraticValue b v := by
  simpa [coefficientPosition] using coeff_square_mul_complementary_cubic b v

#print axioms coeff_encoded_square
#print axioms coeff_square_mul_complementary_cubic

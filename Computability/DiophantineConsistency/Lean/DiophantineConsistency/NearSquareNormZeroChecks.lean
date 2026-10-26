import DiophantineConsistency.NearSquareNormZero

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NearSquareNormZeroChecks
open NearSquareNormZero

example (A x y : ℤ) (hA : 2 ≤ A) (hy : y ≠ 0) :
    x ^ 2 - (A ^ 2 - 1) * y ^ 2 ≠ 0 := norm_ne_zero A x y hA hy

example (A x : ℤ) (hA : 2 ≤ A) :
    x ^ 2 - (A ^ 2 - 1) * (-1 : ℤ) ^ 2 ≠ 0 :=
  norm_ne_zero A x (-1) hA (by decide)

/-- Both excluded boundary cases really have a zero norm. -/
example (A : ℤ) : (0 : ℤ) ^ 2 - (A ^ 2 - 1) * 0 ^ 2 = 0 := by ring
example : (0 : ℤ) ^ 2 - (1 ^ 2 - 1) * 1 ^ 2 = 0 := by norm_num

#print axioms norm_ne_zero

end DiophantineConsistency.NearSquareNormZeroChecks

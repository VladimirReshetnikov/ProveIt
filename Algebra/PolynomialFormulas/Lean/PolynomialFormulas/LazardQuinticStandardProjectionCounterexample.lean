import PolynomialFormulas.LazardQuinticAlternateProjection

/-!
# Why Lazard's alternate projection is necessary

The paper's displayed Section-7 formula uses the standard projection matrix,
whose determinant contains `T² + U²`.  This factor can vanish over a field in
which `-1` is a square.  The two theorems below give the elementary formal
counterexample and show that Lazard's alternate matrix remains nonsingular on
the same data.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false

variable {K : Type*} [Field K] [CharZero K]

/-- If `ι² = -1`, the standard projection matrix at `(T,U)=(1,ι)` is
singular, regardless of the nonzero epsilon choice. -/
theorem standardProjectionMatrix_singular_of_sq_eq_neg_one
    (epsilon ι : K) (hι : ι ^ 2 = -1) :
    (standardProjectionMatrix epsilon 1 ι).det = 0 := by
  rw [standardProjectionMatrix_det, hι]
  ring

/-- On the same `(T,U)=(1,ι)` data, the alternate denominator is nonzero. -/
theorem alternateDenominator_one_ne_zero_of_sq_eq_neg_one
    (ι : K) (hι : ι ^ 2 = -1) :
    alternateDenominator 1 ι ≠ 0 := by
  intro hzero
  have htwo : ι = 2 := by
    unfold alternateDenominator at hzero
    linear_combination hzero - hι
  rw [htwo] at hι
  norm_num at hι

/-- Thus a nonzero epsilon makes the alternate matrix invertible even though
the standard matrix from the preceding theorem is singular. -/
theorem alternateProjectionMatrix_nonsingular_of_sq_eq_neg_one
    (epsilon ι : K) (hι : ι ^ 2 = -1) (hepsilon : epsilon ≠ 0) :
    (alternateProjectionMatrix epsilon 1 ι).det ≠ 0 :=
  alternateProjectionMatrix_det_ne_zero epsilon 1 ι hepsilon
    (alternateDenominator_one_ne_zero_of_sq_eq_neg_one ι hι)

end LeanProofs.PolynomialFormulas.LazardQuintic

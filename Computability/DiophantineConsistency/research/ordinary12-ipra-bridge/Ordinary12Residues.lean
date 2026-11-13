import Mathlib.Data.ZMod.Basic

namespace Ordinary12Residues

/-- No square is congruent to two modulo four. -/
theorem square_ne_two : ∀ z : ZMod 4, z * z ≠ 2 := by decide

/-- The square of any even residue vanishes modulo four. -/
theorem double_square_zero : ∀ z : ZMod 4, (2 * z) * (2 * z) = 0 := by decide

/-- Every integer factor of the form 1+s²−t²u avoids −1 when t is even. -/
theorem shifted_norm_ne_neg_one :
    ∀ s t u : ZMod 4, t * t = 0 → 1 + s * s - t * t * u ≠ -1 := by decide

/-- The actual q is even whenever beta and J are odd. -/
theorem odd_beta_odd_j_even_q :
    ∀ b j : ZMod 4, (b = 1 ∨ b = 3) → (j = 1 ∨ j = 3) →
      ∃ k : ZMod 4, 1 + b * j = 2 * k := by decide

/-- The ordinary merger's b_n is even, uniformly in all parameters. -/
theorem ordinary_bn_square_zero :
    ∀ Q n V : ZMod 4, (2 * (1-Q) * (n+V)) * (2 * (1-Q) * (n+V)) = 0 := by decide

/-- Thus the ordinary merger factor 1+N cannot be the negative unit. -/
theorem ordinary_factor_ne_neg_one :
    ∀ AN d bn Q : ZMod 4, bn * bn = 0 →
      1 + AN * AN - d * (bn * bn) * Q ≠ -1 := by decide

end Ordinary12Residues
#print axioms Ordinary12Residues.square_ne_two
#print axioms Ordinary12Residues.double_square_zero
#print axioms Ordinary12Residues.shifted_norm_ne_neg_one
#print axioms Ordinary12Residues.odd_beta_odd_j_even_q
#print axioms Ordinary12Residues.ordinary_bn_square_zero
#print axioms Ordinary12Residues.ordinary_factor_ne_neg_one

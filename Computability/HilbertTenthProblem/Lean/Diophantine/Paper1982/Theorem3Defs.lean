import Diophantine.Paper1982.Theorem2
import Diophantine.Paper1982.RatioPolynomialDefs

/-!
# The 28-witness polynomial system in Jones 1982, Theorem 3

The eight coding and packing equations are combined with the ten polynomial
ratio equations. The parameter `ν` determines the exponent `5^(ν+2)`;
setting `ν = 58` gives the article's `5^60`. Subtraction in the displayed
polynomials is interpreted over the integers.
-/

namespace Jones1982

/-- The first equation with positive slack already forces `xy < b`.
In particular, the converse of Theorem 3 does not assume `b` is a power
of two in order to establish the size bounds needed for Lemma 2.25. -/
theorem UEqs.b_gt_mul {ν x z u y b e g l m q t θ lam α : ℕ}
    (hα : 0 < α) (hU : UEqs ν x z u y b e g l m q t θ lam α) : x * y < b := by
  have hαZ : (0 : ℤ) < α := by exact_mod_cast hα
  have hprod : 0 < ((b : ℤ) - x * y) * q ^ 2 := by
    rw [← hU.U6]
    positivity
  have hdiff := pos_of_mul_pos_left hprod (sq_nonneg (q : ℤ))
  have hlt : (x : ℤ) * y < b := by linarith
  exact_mod_cast hlt

/-- The complete eighteen-equation system of Theorem 3, with exactly the
twenty-eight positive witnesses listed in the article. -/
structure Thm3 (ν : ℕ)
    (x z u y a b c d e f g h i j k l m n o p q r s t w α γ η θ lam τ φ : ℕ) : Prop
    extends UEqs ν x z u y b e g l m q t θ lam α,
      RatioPolynomial r n b a c d f h i j k o p s w γ η τ φ where
  E7 : n = q ^ 16
  E8 : (r : ℤ) = rPolynomial x z b e g l n q θ lam

end Jones1982

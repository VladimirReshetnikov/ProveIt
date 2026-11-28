import GRHArticle.SingularModuli.HeckeModularPrefixCertificate

/-!
# Streaming magnitude bounds for coefficient lists

A left fold avoids building a second long list during kernel reduction.
-/

namespace GRHArticle.SingularModuli.IntegerPolynomialExpression

private theorem foldl_add_natAbs (l : List ℤ) (s : ℕ) :
    l.foldl (fun a x ↦ a+x.natAbs) s = s+(l.map Int.natAbs).sum := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The usual coefficient magnitude bound, with a streaming sum at each leaf. -/
def magnitudeBoundFolded : IntegerPolynomialExpression → ℕ
  | .coefficients cs => cs.foldl (fun a x ↦ a+x.natAbs) 0
  | .add a b => a.magnitudeBoundFolded + b.magnitudeBoundFolded
  | .sub a b => a.magnitudeBoundFolded + b.magnitudeBoundFolded
  | .mul a b => a.magnitudeBoundFolded * b.magnitudeBoundFolded
  | .pow a n => a.magnitudeBoundFolded ^ n

theorem magnitudeBoundFolded_eq (e : IntegerPolynomialExpression) :
    e.magnitudeBoundFolded = e.magnitudeBound := by
  induction e <;> simp only [magnitudeBoundFolded, magnitudeBound, foldl_add_natAbs, zero_add, *]

end GRHArticle.SingularModuli.IntegerPolynomialExpression

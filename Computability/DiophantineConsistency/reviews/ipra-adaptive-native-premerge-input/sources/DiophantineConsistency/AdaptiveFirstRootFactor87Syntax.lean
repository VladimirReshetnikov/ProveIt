import DiophantineConsistency.NaturalExpressionSemiring
import DiophantineConsistency.AdaptiveFirstRootFactor87

/-! The local factorization at the actual integer-expression syntax, evaluated
as a natural signed pair in an arbitrary commutative semiring. -/
set_option autoImplicit false
namespace DiophantineConsistency.AdaptiveFirstRootFactor87Syntax
open DiophantineConsistency.AdaptiveFirstRootFactor87

variable {σ R : Type*} [CommSemiring R]

def splitEval (e : Expr σ) (v : σ → R) : SignedPair R :=
  (e.splitNatural.1.evalSemiring v, e.splitNatural.2.evalSemiring v)

theorem splitEval_add (p q : Expr σ) (v : σ → R) :
    splitEval (p + q) v = pairAdd (splitEval p v) (splitEval q v) := rfl

theorem splitEval_sub (p q : Expr σ) (v : σ → R) :
    splitEval (p - q) v = pairSub (splitEval p v) (splitEval q v) := rfl

theorem splitEval_mul (p q : Expr σ) (v : σ → R) :
    splitEval (p * q) v = pairMul (splitEval p v) (splitEval q v) := rfl

theorem splitEval_one (v : σ → R) : splitEval (1 : Expr σ) v = pairOne := by
  simp [splitEval, Expr.splitNatural, NatExpr.evalSemiring, pairOne]

def oldRoot (q3 qm k bt g y : Expr σ) : Expr σ :=
  let m := q3 * qm
  (m * g + y * qm) - bt * ((1 + k * qm) * q3)

def newRoot (q3 qm k bt g y : Expr σ) : Expr σ :=
  let m := q3 * qm
  (m * (g - k * bt) + y * qm) - bt * q3

/-- The actual integer syntax has exactly equal split-natural values, even when
its subexpressions denote formal signed values. -/
theorem split_root_identity (q3 qm k bt g y : Expr σ) (v : σ → R) :
    splitEval (oldRoot q3 qm k bt g y) v = splitEval (newRoot q3 qm k bt g y) v := by
  simp only [oldRoot, newRoot, splitEval_add, splitEval_sub, splitEval_mul, splitEval_one]
  exact signed_root_identity (splitEval q3 v) (splitEval qm v) (splitEval k v)
    (splitEval bt v) (splitEval g v) (splitEval y v)

/-- Replacing the root preserves any later computation and its zero test. -/
theorem contextual_zero_iff (context : SignedPair R → SignedPair R)
    (q3 qm k bt g y : Expr σ) (v : σ → R) :
    (context (splitEval (oldRoot q3 qm k bt g y) v)).1 =
        (context (splitEval (oldRoot q3 qm k bt g y) v)).2 ↔
      (context (splitEval (newRoot q3 qm k bt g y) v)).1 =
        (context (splitEval (newRoot q3 qm k bt g y) v)).2 := by
  rw [split_root_identity]

end DiophantineConsistency.AdaptiveFirstRootFactor87Syntax

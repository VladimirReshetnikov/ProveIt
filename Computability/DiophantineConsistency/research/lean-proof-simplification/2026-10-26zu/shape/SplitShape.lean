import DiophantineConsistency.NaturalExpression

/-!
The two raw natural trees have the same shape, including their operation
labels, after erasing all leaf labels. This is a property of raw splitting;
it need not survive separate calls to NatExpr.simplify.
-/
namespace DiophantineConsistency

namespace NatExpr

def shapeFold {σ : Type*} {A : Type*} (leaf : A)
    (add mul : A → A → A) : NatExpr σ → A
  | .constant _ | .var _ => leaf
  | .add p q => add (shapeFold leaf add mul p) (shapeFold leaf add mul q)
  | .mul p q => mul (shapeFold leaf add mul p) (shapeFold leaf add mul q)

def eraseLeaves {σ : Type*} (e : NatExpr σ) : NatExpr Empty :=
  shapeFold (.constant 0) .add .mul e

end NatExpr

namespace Expr

theorem splitNatural_shapeFold_eq {σ A : Type*} (leaf : A)
    (add mul : A → A → A) (e : Expr σ) :
    NatExpr.shapeFold leaf add mul e.splitNatural.1 =
      NatExpr.shapeFold leaf add mul e.splitNatural.2 := by
  induction e <;> simp_all [splitNatural, NatExpr.shapeFold]

theorem splitNatural_eraseLeaves_eq {σ : Type*} (e : Expr σ) :
    NatExpr.eraseLeaves e.splitNatural.1 = NatExpr.eraseLeaves e.splitNatural.2 := by
  simpa only [NatExpr.eraseLeaves] using
    (splitNatural_shapeFold_eq (A := NatExpr Empty) (NatExpr.constant 0)
      NatExpr.add NatExpr.mul e)

end Expr

#print axioms Expr.splitNatural_shapeFold_eq
#print axioms Expr.splitNatural_eraseLeaves_eq

end DiophantineConsistency

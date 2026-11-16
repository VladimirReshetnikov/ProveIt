module
public import PA196.Arithmetic.WordExpression
public import PA196.Commands.Coding
public import PA196.Commands.HeadSelectors
@[expose] public section

/-! Fixed expression trees constructing the paper's exact command words.
Variable parameters range over the ambient arithmetic model. -/
namespace PA196.Arithmetic.WordMacros
open WordExpression Commands

def pair (a b : WordExpression.Scalar) : WordExpression.Scalar :=
  .head (.pair .a .b) a b (.num 0) (.num 0)
def mpAtom (b : WordExpression.Scalar) : WordExpression.Scalar := pair (.num 1) (pair b (.num 0))
def axAtom (c x y : WordExpression.Scalar) : WordExpression.Scalar :=
  pair (.add c (.num 2)) (pair y (pair x (.num 0)))
def literal : List Nat → WordExpression.Expr
  | [] => .nil
  | a :: as => .cons (.num a) (literal as)
def singleton (a : WordExpression.Scalar) : WordExpression.Expr := .cons a .nil
def offset (u : WordExpression.Scalar) : WordExpression.Expr :=
  .ifEq u (.num 0) .nil (singleton (mpAtom u))
def head (j : Nat) (D H A : WordExpression.Scalar) : WordExpression.Expr :=
  .append (.append (literal (atoms discard))
    (.cons (axAtom A D H) (literal (atoms (List.replicate (j + 1) .shift)))))
    (literal (atoms (pops (8 - j))))
def rho8 (a b c u : WordExpression.Scalar) : WordExpression.Expr :=
  .append (.append (.append (literal (atoms discard)) (offset u))
    (.cons (axAtom b (.sub a u) c) (literal (atoms (List.replicate 8 .shift)))))
    (literal (atoms pop))
def gate (a b c : WordExpression.Scalar) : WordExpression.Expr :=
  .append (.append (literal (atoms discard)) (singleton (axAtom c b a)))
    (literal (atoms (pops 9)))
def gen (i : WordExpression.Scalar) : WordExpression.Expr :=
  .append (.append (.append (literal (atoms push)) (offset i)) (literal (atoms [.shift])))
    (.cons (axAtom i (.num 0) (.num 0)) (literal (atoms (List.replicate 9 .shift))))
def mp (b : WordExpression.Scalar) : WordExpression.Expr :=
  .append (.append (.cons (.num 0) (.cons (.num 0) (singleton (mpAtom b))))
    (.cons (axAtom b (.num 0) (.num 0)) (literal (atoms (List.replicate 9 .shift)))))
    (literal (atoms [.shift]))

end PA196.Arithmetic.WordMacros

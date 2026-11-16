import PA196.Commands.Store

/-! Extracted upstream syntax and a callback interpretation for prior table
entries. The checker-rule source only uses `.previous` as the first argument
of `.nth`; the standalone evaluator below is justified only for that rule.
`check_native_checker.py` verifies each extracted source fragment byte-for-byte
against the pinned upstream files. This is not the Foundation model evaluator. -/

namespace M6.PA.ActualArithmeticGraph
inductive Expr where
  | a | b | c | u
  | lit (n : Nat)
  | add (left right : Expr)
  | mul (left right : Expr)
  | pair (left right : Expr)

def evalNat : Expr → Nat → Nat → Nat → Nat → Nat
  | .a,a,_,_,_ => a
  | .b,_,b,_,_ => b
  | .c,_,_,c,_ => c
  | .u,_,_,_,u => u
  | .lit n,_,_,_,_ => n
  | .add x y,a,b,c,u => evalNat x a b c u + evalNat y a b c u
  | .mul x y,a,b,c,u => evalNat x a b c u * evalNat y a b c u
  | .pair x y,a,b,c,u => M6.Source.Cantor.pair (evalNat x a b c u) (evalNat y a b c u)
end M6.PA.ActualArithmeticGraph

namespace PA196.Arithmetic.HeadGraphs
open M6.PA.ActualArithmeticGraph
def im (x y : Expr) : Expr := .mul (.lit 4) (.pair x y)
def al (x y : Expr) : Expr := .add (im y x) (.lit 2)
def mem (x y : Expr) : Expr := .add (im x y) (.lit 1)
def eqn (x y : Expr) : Expr := .add (im x y) (.lit 3)
def neg (x : Expr) : Expr := im x (.lit 1)
def conj (x y : Expr) : Expr := neg (im x (neg y))
def ex (x y : Expr) : Expr := neg (al x (neg y))

def implicationExpr : Expr := im .a .b
def universalExpr : Expr := al .a .b
def head1Expr : Expr := im (ex .a (al .a .b)) .b
def head2Expr : Expr := im (al .a (al .b .c)) (al .b (al .a .c))
def head3Expr : Expr := im (mem .c .a) (im (eqn .c .b) (mem .b .a))
def head4Expr : Expr := im (eqn .c .a) (im (mem .b .c) (mem .b .a))
def head5Expr : Expr := ex .a (eqn .b .a)
def head6Expr : Expr := im (al .a .b) (im (al .a (im .b .c)) (al .a .c))
def rho8Expr : Expr := im (im (im .c .u) .a) (im (im .a .c) (im .b .c))
def eqVacExpr : Expr := im (eqn .a .b) (al .c (eqn .a .b))
def memVacExpr : Expr := im (mem .a .b) (al .c (mem .a .b))
def pointExpr : Expr := im .c (mem .c .b)
def separationExpr : Expr := al .b (conj (im (mem .a .b) pointExpr) (im (mem .c .b) .c))
def bundleExpr : Expr :=
  neg (im eqVacExpr (im memVacExpr (al .c (im separationExpr (neg pointExpr)))))
end PA196.Arithmetic.HeadGraphs

namespace PA196.Arithmetic.Scalar
inductive Expr where
  | previous | tag | payload
  | num (n : Nat)
  | add (x y : Expr)
  | sub (x y : Expr)
  | left (x : Expr)
  | right (x : Expr)
  | nth (xs i : Expr)
  | head (e : M6.PA.ActualArithmeticGraph.Expr) (a b c u : Expr)
  | ifEq (x y yes no : Expr)
  | ifLe (x y yes no : Expr)
/-- Evaluation specialized to checker rules, in which `.previous` is
only the table parameter of `.nth`. -/
def evalNat : Expr → (Nat → Nat) → Nat → Nat → Nat
  | .previous, _, _, _ => 0
  | .tag, _, tag, _ => tag
  | .payload, _, _, payload => payload
  | .num n, _, _, _ => n
  | .add x y, prev, tag, payload => evalNat x prev tag payload + evalNat y prev tag payload
  | .sub x y, prev, tag, payload => evalNat x prev tag payload - evalNat y prev tag payload
  | .left x, prev, tag, payload => (M6.Source.Cantor.decode (evalNat x prev tag payload)).1
  | .right x, prev, tag, payload => (M6.Source.Cantor.decode (evalNat x prev tag payload)).2
  | .nth _ i, prev, tag, payload => prev (evalNat i prev tag payload)
  | .head e a b c u, prev, tag, payload =>
      M6.PA.ActualArithmeticGraph.evalNat e (evalNat a prev tag payload)
        (evalNat b prev tag payload) (evalNat c prev tag payload) (evalNat u prev tag payload)
  | .ifEq x y yes no, prev, tag, payload =>
      if evalNat x prev tag payload = evalNat y prev tag payload
      then evalNat yes prev tag payload else evalNat no prev tag payload
  | .ifLe x y yes no, prev, tag, payload =>
      if evalNat x prev tag payload ≤ evalNat y prev tag payload
      then evalNat yes prev tag payload else evalNat no prev tag payload

end PA196.Arithmetic.Scalar

namespace PA196.Arithmetic.CheckerRule
open PA196.Arithmetic.Scalar PA196.Arithmetic.HeadGraphs
def zero : Scalar.Expr := .num 0
def one : Scalar.Expr := .num 1
def accepted (x : Scalar.Expr) : Scalar.Expr := .add x one
def r1 : Scalar.Expr := .right .payload
def r2 : Scalar.Expr := .right r1
def r3 : Scalar.Expr := .right r2
def r4 : Scalar.Expr := .right r3
def a : Scalar.Expr := .left .payload
def b : Scalar.Expr := .left r1
def c : Scalar.Expr := .left r2
def u : Scalar.Expr := .left r3
def h (e : M6.PA.ActualArithmeticGraph.Expr) : Scalar.Expr := .head e a b c u
def requireZero (tail result : Scalar.Expr) : Scalar.Expr := .ifEq tail zero result zero
def minor : Scalar.Expr := .nth .previous b
def major : Scalar.Expr := .nth .previous c

def mp : Scalar.Expr := requireZero r3 <|
  .ifEq minor zero zero <| .ifEq major zero zero <|
  .ifEq major (accepted (.head implicationExpr (.sub minor one) a zero zero))
    (accepted a) zero
def gen : Scalar.Expr := requireZero r2 <|
  .ifEq minor zero zero (accepted (.head universalExpr a (.sub minor one) zero zero))
def leaf1 : Scalar.Expr := requireZero r2 (accepted (h head1Expr))
def leaf2 : Scalar.Expr := requireZero r3 (accepted (h head2Expr))
def leaf3 : Scalar.Expr := requireZero r3 (accepted (h head3Expr))
def leaf4 : Scalar.Expr := requireZero r3 (accepted (h head4Expr))
def leaf5 : Scalar.Expr := requireZero r2 (accepted (h head5Expr))
def leaf6 : Scalar.Expr := requireZero r3 (accepted (h head6Expr))
def leaf8 : Scalar.Expr := requireZero r4 (.ifLe u a (accepted (h rho8Expr)) zero)
def rawBundle : Scalar.Expr := requireZero r3 <|
  .ifEq c a zero (.ifEq c b zero (accepted (h bundleExpr)))

def rule : Scalar.Expr :=
  .ifEq .tag (.num 0) mp <|
  .ifEq .tag (.num 1) gen <|
  .ifEq .tag (.num 2) leaf1 <|
  .ifEq .tag (.num 3) leaf2 <|
  .ifEq .tag (.num 4) leaf3 <|
  .ifEq .tag (.num 5) leaf4 <|
  .ifEq .tag (.num 6) leaf5 <|
  .ifEq .tag (.num 7) leaf6 <|
  .ifEq .tag (.num 8) leaf8 <|
  .ifEq .tag (.num 9) rawBundle zero
end PA196.Arithmetic.CheckerRule

module
public import PA196.Arithmetic.Scalar
@[expose] public section

/-!
One round of the PA196 proof checker, arithmetized uniformly in every IΣ₁
model. Tags 0 and 1 are MP/generalization; tags 2–7 are paper heads 1–6;
tag 8 is the dominated propositional head; tag 9 is the guarded gate.
The value zero rejects, while `a+1` accepts the formula with exact code `a`.
Malformed tuples, failed guards, rejected children and other tags reject.
-/
namespace PA196.Arithmetic.CheckerRule
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open M6.PA.SourceCantorInternal Scalar HeadGraphs

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

noncomputable def ruleGraph : 𝚺ᴬ₁.Semisentence 4 := Scalar.graph rule

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def ruleValue (previous tag payload : V) : V := Scalar.eval rule previous tag payload

theorem rule_graph (z previous tag payload : V) :
    ruleGraph.val.Evalb ![z, previous, tag, payload] ↔ z = ruleValue previous tag payload :=
  Scalar.graph_correct _ _ _ _ _

theorem rule_total_unique (previous tag payload : V) :
    ∃! z, ruleGraph.val.Evalb ![z, previous, tag, payload] := Scalar.total_unique _ _ _ _

instance ruleValue_defined : 𝚺ᴬ₁-Function₃ (ruleValue : V → V → V → V) via ruleGraph := .mk fun v => by
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext ⟨i, hi⟩
    have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases he with rfl | rfl | rfl | rfl <;> rfl
  rw [hv]
  exact rule_graph _ _ _ _
instance ruleValue_definable : 𝚺ᴬ₁-Function₃ (ruleValue : V → V → V → V) :=
  ruleValue_defined.to_definable

#print axioms rule_graph
#print axioms rule_total_unique
end PA196.Arithmetic.CheckerRule

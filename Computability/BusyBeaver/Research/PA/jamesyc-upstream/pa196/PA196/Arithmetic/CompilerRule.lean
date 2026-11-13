module
public import PA196.Arithmetic.WordMacros
public import PA196.Arithmetic.CheckerRule
@[expose] public section

namespace PA196.Arithmetic.CompilerRule
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CheckerRule (a b c u r2 r3 r4 zero)
open WordExpression Commands

def requireZero (tail : WordExpression.Scalar) (result : WordExpression.Expr) : WordExpression.Expr :=
  .ifEq tail zero result .nil
def mp : WordExpression.Expr := requireZero r3 <|
  .append (.lookup c) (.append (WordMacros.literal (atoms Commands.push))
    (.append (.lookup b) (.append (WordMacros.literal (atoms Commands.push)) (WordMacros.mp a))))
def gen : WordExpression.Expr := requireZero r2 <| .append (.lookup b) (WordMacros.gen a)
def leaf1 : WordExpression.Expr := requireZero r2 (WordMacros.head 6 a b zero)
def leaf2 : WordExpression.Expr := requireZero r3 (WordMacros.head 5 a c b)
def leaf3 : WordExpression.Expr := requireZero r3 (WordMacros.head 4 a c b)
def leaf4 : WordExpression.Expr := requireZero r3 (WordMacros.head 3 a c b)
def leaf5 : WordExpression.Expr := requireZero r2 (WordMacros.head 2 a b zero)
def leaf6 : WordExpression.Expr := requireZero r3 (WordMacros.head 1 a c b)
def leaf8 : WordExpression.Expr := requireZero r4 <|
  .ifLe u a (WordMacros.rho8 a b c u) .nil
def rawBundle : WordExpression.Expr := requireZero r3 <|
  .ifEq c a .nil (.ifEq c b .nil (WordMacros.gate a b c))

def rule : WordExpression.Expr :=
  .ifEq .tag (.num 0) mp <|
  .ifEq .tag (.num 1) gen <|
  .ifEq .tag (.num 2) leaf1 <|
  .ifEq .tag (.num 3) leaf2 <|
  .ifEq .tag (.num 4) leaf3 <|
  .ifEq .tag (.num 5) leaf4 <|
  .ifEq .tag (.num 6) leaf5 <|
  .ifEq .tag (.num 7) leaf6 <|
  .ifEq .tag (.num 8) leaf8 <|
  .ifEq .tag (.num 9) rawBundle .nil

noncomputable def ruleGraph : 𝚺ᴬ₁.Semisentence 4 := WordExpression.graph rule
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def ruleValue (previous tag payload : V) : V := WordExpression.eval rule previous tag payload

theorem rule_graph (z previous tag payload : V) :
    ruleGraph.val.Evalb ![z, previous, tag, payload] ↔ z = ruleValue previous tag payload :=
  WordExpression.graph_correct _ _ _ _ _
theorem rule_total_unique (previous tag payload : V) :
    ∃! z, ruleGraph.val.Evalb ![z, previous, tag, payload] := WordExpression.total_unique _ _ _ _

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
end PA196.Arithmetic.CompilerRule

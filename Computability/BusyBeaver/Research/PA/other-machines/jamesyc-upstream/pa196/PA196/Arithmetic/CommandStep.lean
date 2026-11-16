module
public import PA196.Arithmetic.WordExpression
public import PA196.Commands.Coding
@[expose] public section

/-! An explicit Σ₁ graph for the PA196 command interpreter in any IΣ₁ model.
Zero represents halted execution; live states use the nonempty HFS vector
`[t,w,d,h]`. The stack `w` itself uses source Cantor pairing. -/
namespace PA196.Arithmetic.CommandStep
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open WordExpression HeadGraphs M6.PA.SourceCantorInternal

noncomputable def stateCode {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (t w d h : V) : V := t ∷ w ∷ d ∷ h ∷ 0

def zero : WordExpression.Scalar := .num 0
def top : WordExpression.Scalar := .nth .previous (.num 0)
def stack : WordExpression.Scalar := .nth .previous (.num 1)
def cacheD : WordExpression.Scalar := .nth .previous (.num 2)
def cacheH : WordExpression.Scalar := .nth .previous (.num 3)
def tag : WordExpression.Scalar := .left .tag
def fields : WordExpression.Scalar := .right .tag
def first : WordExpression.Scalar := .left fields
def second : WordExpression.Scalar := .left (.right fields)
def state (t w d h : WordExpression.Scalar) : WordExpression.Expr :=
  .cons t (.cons w (.cons d (.cons h .nil)))
def pair (a b : WordExpression.Scalar) : WordExpression.Scalar :=
  .head (.pair .a .b) a b zero zero
def imp (a b : WordExpression.Scalar) : WordExpression.Scalar :=
  .head implicationExpr a b zero zero
def headValue (e : M6.PA.ActualArithmeticGraph.Expr) (a b c : WordExpression.Scalar) :
    WordExpression.Scalar := .head e a b c cacheD
def push : List WordExpression.Scalar → WordExpression.Scalar → WordExpression.Scalar
  | [], w => w
  | a :: as, w => pair a (push as w)

def shift : WordExpression.Expr := .ifEq (.add top cacheH) (.num 1) .nil <|
  state cacheH (.right stack) cacheD (.left stack)
def mp : WordExpression.Expr :=
  let y : WordExpression.Scalar := .add cacheD first
  .ifEq (imp top y) cacheH
    (state y (pair zero stack) y zero)
    (state zero stack y zero)
def ax : WordExpression.Expr :=
  let D : WordExpression.Scalar := .add cacheD second
  let H : WordExpression.Scalar := .add cacheH first
  let A : WordExpression.Scalar := .sub tag (.num 2)
  let gate : WordExpression.Scalar :=
    .ifEq A H zero (.ifEq A D zero (headValue bundleExpr H D A))
  let heads : List WordExpression.Scalar :=
    [headValue head6Expr D A H, headValue head5Expr D H zero,
     headValue head4Expr D A H, headValue head3Expr D A H,
     headValue head2Expr D A H, headValue head1Expr D H zero,
     headValue rho8Expr D A H,
     .head universalExpr cacheD cacheH zero zero, top]
  state gate (push heads stack) zero zero

def stepExpr : WordExpression.Expr := .ifEq .previous zero .nil <|
  .ifEq tag zero shift (.ifEq tag (.num 1) mp ax)

noncomputable def stepGraph : 𝚺ᴬ₁.Semisentence 3 :=
  (WordExpression.graph stepExpr).rew (Rew.subst ![#0, #2, #1, ‘0’])

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def stepValue (atom state : V) : V := WordExpression.eval stepExpr state atom 0

theorem step_graph (z atom state : V) :
    stepGraph.val.Evalb ![z, atom, state] ↔ z = stepValue atom state := by
  simp [stepGraph, WordExpression.graph_correct, stepValue]

instance step_defined : 𝚺ᴬ₁-Function₂ (stepValue : V → V → V) via stepGraph := .mk fun v => by
  have hv : v = ![v 0, v 1, v 2] := by
    funext ⟨i, hi⟩
    have he : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases he with rfl | rfl | rfl <;> rfl
  rw [hv]
  exact step_graph _ _ _
instance step_definable : 𝚺ᴬ₁-Function₂ (stepValue : V → V → V) := step_defined.to_definable

theorem stateCode_ne_zero (t w d h : V) : stateCode t w d h ≠ 0 := by simp [stateCode]

@[simp] theorem step_halted (atom : V) : stepValue atom 0 = 0 := by
  simp [stepValue, stepExpr, zero, WordExpression.eval, Scalar.eval]

theorem step_total_unique (atom state : V) : ∃! z, stepGraph.val.Evalb ![z, atom, state] :=
  ⟨stepValue atom state, (step_graph _ _ _).mpr rfl, fun _ hz => (step_graph _ _ _).mp hz⟩

@[simp] theorem nth_adjoin_three (x xs : V) : (x ∷ xs).[3] = xs.[2] := by
  simpa [-nth_adjoin_succ, two_add_one_eq_three] using nth_adjoin_succ x xs 2

theorem shift_value (t w d h : V) :
    stepValue 0 (stateCode t w d h) =
      if t + h = 1 then 0 else stateCode h (decodeRight w) d (decodeLeft w) := by
  by_cases ht : t + h = 1 <;>
    simp [stepValue, stepExpr, shift, state, WordExpression.eval, zero, top,
      stack, cacheD, cacheH, tag, Scalar.eval, stateCode, decodeLeft, decodeRight, ht]

#print axioms step_graph
#print axioms step_total_unique
#print axioms shift_value
end PA196.Arithmetic.CommandStep

module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualWordMacros
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualWordExpression ActualHeadGraphs

/-- Execution-state codec: zero is halted; every live state is the nonempty
HFS vector [T,W,D,H]. W remains a Source Cantor stack, not an HFS vector. -/
noncomputable def stateCode {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (t w d h : V) : V := t ∷ w ∷ d ∷ h ∷ 0
def zero : Scalar := .num 0
def top : Scalar := .nth .previous (.num 0)
def stack : Scalar := .nth .previous (.num 1)
def cacheD : Scalar := .nth .previous (.num 2)
def cacheH : Scalar := .nth .previous (.num 3)
def tag : Scalar := .left .tag
def fields : Scalar := .right .tag
def first : Scalar := .left fields
def second : Scalar := .left (.right fields)
def state (t w d h : Scalar) : Expr := .cons t (.cons w (.cons d (.cons h .nil)))
def imp (a b : Scalar) : Scalar := .head implicationExpr a b zero zero
def headValue (e : ActualArithmeticGraph.Expr) (a b c : Scalar) : Scalar := .head e a b c cacheD
def push : List Scalar → Scalar → Scalar
  | [],w => w
  | a::as,w => ActualWordMacros.pair a (push as w)

def shift : Expr := .ifEq (.add top cacheH) (.num 1) .nil <|
  state cacheH (.right stack) cacheD (.left stack)
def mp : Expr :=
  let y : Scalar := .add cacheD first
  .ifEq (imp top y) cacheH
    (state y (ActualWordMacros.pair zero stack) y zero)
    (state zero stack y zero)
def ax : Expr :=
  let a : Scalar := .add cacheD second
  let b : Scalar := .add cacheH first
  let c : Scalar := .sub tag (.num 2)
  let gate : Scalar := .ifEq c a zero (.ifEq c b zero (headValue bundleExpr a b c))
  let heads : List Scalar := [headValue rho1Expr a b c,headValue rho2Expr a b c,
    headValue rho3Expr a b c,headValue rho4Expr a b c,headValue rho5Expr a b c,
    headValue rho6Expr a b c,headValue rho7Expr a b c,headValue rho8Expr a b c,
    .head universalExpr cacheD cacheH zero zero,top]
  state gate (push heads stack) zero zero

/-- A halted execution remains halted. Noncanonical live inputs are read
through HFS nth with its existing default-zero behavior. -/
def stepExpr : Expr := .ifEq .previous zero .nil <|
  .ifEq tag zero shift (.ifEq tag (.num 1) mp ax)

noncomputable def stepGraph : 𝚺ᴬ₁.Semisentence 3 :=
  (graph stepExpr).rew (Rew.subst ![#0,#2,#1,‘0’])
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def stepValue (atom state : V) : V := eval stepExpr state atom 0

theorem step_graph (z atom state : V) :
    stepGraph.val.Evalb ![z,atom,state] ↔ z=stepValue atom state := by
  simp [stepGraph,graph_correct,stepValue]
instance step_defined : 𝚺ᴬ₁-Function₂ (stepValue : V → V → V) via stepGraph := .mk fun v => by
  have hv : v=![v 0,v 1,v 2] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases he with rfl|rfl|rfl <;> rfl
  rw [hv]
  exact step_graph _ _ _
instance step_definable : 𝚺ᴬ₁-Function₂ (stepValue : V → V → V) := step_defined.to_definable

theorem stateCode_ne_zero (t w d h : V) : stateCode t w d h ≠ 0 := by simp [stateCode]
@[simp] theorem step_halted (atom : V) : stepValue atom 0=0 := by
  simp [stepValue,stepExpr,zero,eval,ActualCheckExpression.eval]

theorem step_total_unique (atom state : V) : ∃! z,stepGraph.val.Evalb ![z,atom,state] :=
  ⟨stepValue atom state,(step_graph _ _ _).mpr rfl,fun _ hz => (step_graph _ _ _).mp hz⟩

open M6.Source M6.Source.CommandAtomEncoding SourceCantorInternal
attribute [local irreducible] stepValue ax

@[simp] private theorem nth_adjoin_three (x xs : V) : (x ∷ xs).[3]=xs.[2] := by
  simpa [-nth_adjoin_succ,two_add_one_eq_three] using nth_adjoin_succ x xs 2

/-- Literal shift arithmetic, uniformly in every I-Sigma-1 model. -/
theorem shift_value (t w d h : V) :
    stepValue 0 (stateCode t w d h) =
      if t+h=1 then 0 else stateCode h (decodeRight w) d (decodeLeft w) := by
  by_cases ht : t+h=1 <;>
    simp [stepValue,stepExpr,shift,state,eval,zero,top,stack,cacheD,cacheH,tag,
      ActualCheckExpression.eval,stateCode,decodeLeft,decodeRight,ht]

noncomputable def resultCode : Option CommandStore → Nat
  | none => 0
  | some s => stateCode s.t s.w s.d s.h

@[simp] theorem resultCode_eq_zero (s : Option CommandStore) : resultCode s=0 ↔ s=none := by
  cases s <;> simp [resultCode,stateCode_ne_zero]

private theorem push_standard (xs : List Scalar) (tail : Scalar) (p a d : Nat) :
    ActualCheckExpression.eval (push xs tail) p a d =
      (xs.map fun e => ActualCheckExpression.eval e p a d).foldr Cantor.pair (ActualCheckExpression.eval tail p a d) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [push,ActualWordMacros.pair_standard,List.map_cons,List.foldr_cons,ih]

private theorem state_eval (t w d h : Scalar) (p a k : Nat) :
    eval (state t w d h) p a k=stateCode
      (ActualCheckExpression.eval t p a k) (ActualCheckExpression.eval w p a k)
      (ActualCheckExpression.eval d p a k) (ActualCheckExpression.eval h p a k) := rfl

theorem shift_standard (t w d h : Nat) :
    stepValue (atom .shift) (stateCode t w d h)=resultCode (commandEval .shift ⟨t,w,d,h⟩) := by
  by_cases ht : t+h=1
  all_goals simp [stepValue,stepExpr,shift,state_eval,eval,zero,top,stack,cacheD,cacheH,tag,
    ActualCheckExpression.eval,atom,Enumeration.encodeCommand,decodeLeft,decodeRight,decodeState_standard,
    Cantor.decode_pair,stateCode,resultCode,commandEval,ht]

theorem mp_standard (x t w d h : Nat) :
    stepValue (atom (.mp x)) (stateCode t w d h)=resultCode (commandEval (.mp x) ⟨t,w,d,h⟩) := by
  by_cases he : AXCode.wim t (d+x)=h
  all_goals simp [stepValue,stepExpr,mp,state_eval,eval,zero,top,stack,cacheD,cacheH,tag,first,fields,imp,
    ActualCheckExpression.eval,ActualWordMacros.pair_standard,ActualArithmeticGraph.eval_standard,implication_exact,
    atom,Enumeration.encodeCommand,decodeLeft,decodeRight,decodeState_standard,
    Cantor.decode_pair,stateCode,resultCode,commandEval,he]
  all_goals rfl

private theorem select_ax (c x y t w d h : Nat) :
    stepValue (atom (.ax c x y)) (stateCode t w d h) =
      eval ax (stateCode t w d h) (atom (.ax c x y)) 0 := by
  simp [stepValue,stepExpr,tag,zero,eval,ActualCheckExpression.eval,
    atom,Enumeration.encodeCommand,decodeLeft,decodeRight,decodeState_standard,
    Cantor.decode_pair,stateCode]

theorem ax_standard (c x y t w d h : Nat) :
    stepValue (atom (.ax c x y)) (stateCode t w d h)=resultCode (commandEval (.ax c x y) ⟨t,w,d,h⟩) := by
  rw [select_ax,ax,state_eval,push_standard]
  simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil]
  simp only [headValue,zero,top,stack,cacheD,cacheH,tag,first,second,fields,ActualCheckExpression.eval]
  simp only [ActualArithmeticGraph.eval_standard,rho1_exact,rho2_exact,rho3_exact,rho4_exact,
    rho5_exact,rho6_exact,rho7_exact,rho8_exact,bundle_exact,universal_exact]
  by_cases ha : c=d+x
  all_goals by_cases hb : c=h+y
  all_goals simp [ActualWordMacros.sub_standard,atom,Enumeration.encodeCommand,
    decodeLeft,decodeRight,decodeState_standard,Cantor.decode_pair,stateCode,
    resultCode,commandEval,ActualAXCode.gate,ActualAXCode.pa135Heads,ha,hb]
  all_goals rfl

theorem step_standard (c : Enumeration.Command) (s : CommandStore) :
    stepValue (atom c) (resultCode (some s))=resultCode (commandEval c s) := by
  cases s with
  | mk t w d h =>
    cases c with
    | shift => exact shift_standard t w d h
    | mp x => exact mp_standard x t w d h
    | ax c x y => exact ax_standard c x y t w d h

#print axioms step_graph
#print axioms step_halted
#print axioms shift_value
#print axioms step_standard
end M6.PA.ActualCommandStepGraph


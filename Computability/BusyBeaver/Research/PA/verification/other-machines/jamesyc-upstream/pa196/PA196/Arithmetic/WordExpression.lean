module
public import PA196.Arithmetic.Scalar
public import PA196.Arithmetic.VectorAppend
@[expose] public section
open M6.Arithmetic.PA

/-! Explicit HFS-vector expressions for the deterministic command compiler.
Scalar inputs retain the exact V1 previous-table/tag/payload interpretation.
This supplies all-model word construction, not execution correctness. -/
namespace PA196.Arithmetic.WordExpression
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
abbrev Scalar := PA196.Arithmetic.Scalar.Expr

inductive Expr where
  | nil
  | cons (atom : Scalar) (tail : Expr)
  | append (left right : Expr)
  | lookup (index : Scalar)
  | ifEq (x y : Scalar) (yes no : Expr)
  | ifLe (x y : Scalar) (yes no : Expr)

noncomputable def graph : Expr → 𝚺ᴬ₁.Semisentence 4
  | .nil => .mkSigma “z p t d. z=0”
  | .cons a xs => .mkSigma “z p t d. ∃ aa xx,
      !(PA196.Arithmetic.Scalar.graph a) aa p t d ∧ !(graph xs) xx p t d ∧ !adjoinDef z aa xx”
  | .append xs ys => .mkSigma “z p t d. ∃ xx yy,
      !(graph xs) xx p t d ∧ !(graph ys) yy p t d ∧ !VectorAppend.appendDef z xx yy”
  | .lookup i => .mkSigma “z p t d. ∃ ii, !(PA196.Arithmetic.Scalar.graph i) ii p t d ∧ !nthDef z p ii”
  | .ifEq x y yes no => .mkSigma “z p t d. ∃ xx yy,
      !(PA196.Arithmetic.Scalar.graph x) xx p t d ∧ !(PA196.Arithmetic.Scalar.graph y) yy p t d ∧
      ((xx=yy ∧ !(graph yes) z p t d) ∨ (xx≠yy ∧ !(graph no) z p t d))”
  | .ifLe x y yes no => .mkSigma “z p t d. ∃ xx yy,
      !(PA196.Arithmetic.Scalar.graph x) xx p t d ∧ !(PA196.Arithmetic.Scalar.graph y) yy p t d ∧
      ((xx≤yy ∧ !(graph yes) z p t d) ∨ (yy<xx ∧ !(graph no) z p t d))”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def eval : Expr → V → V → V → V
  | .nil,_,_,_ => 0
  | .cons a xs,p,t,d => PA196.Arithmetic.Scalar.eval a p t d ∷ eval xs p t d
  | .append xs ys,p,t,d => VectorAppend.append (eval xs p t d) (eval ys p t d)
  | .lookup i,p,t,d => nth p (PA196.Arithmetic.Scalar.eval i p t d)
  | .ifEq x y yes no,p,t,d =>
      if PA196.Arithmetic.Scalar.eval x p t d = PA196.Arithmetic.Scalar.eval y p t d then eval yes p t d else eval no p t d
  | .ifLe x y yes no,p,t,d =>
      if PA196.Arithmetic.Scalar.eval x p t d ≤ PA196.Arithmetic.Scalar.eval y p t d then eval yes p t d else eval no p t d

theorem graph_correct (e : Expr) (z p t d : V) :
    (graph e).val.Evalb ![z,p,t,d] ↔ z=eval e p t d := by
  induction e generalizing z with
  | nil => simp [graph,eval]
  | cons a xs ih => simp [graph,eval,PA196.Arithmetic.Scalar.graph_correct,ih]
  | append xs ys hx hy => simp [graph,eval,hx,hy]
  | lookup i => simp [graph,eval,PA196.Arithmetic.Scalar.graph_correct]
  | ifEq x y yes no hy hn =>
      by_cases h : PA196.Arithmetic.Scalar.eval x p t d = PA196.Arithmetic.Scalar.eval y p t d <;>
        simp [graph,eval,PA196.Arithmetic.Scalar.graph_correct,hy,hn,h]
  | ifLe x y yes no hy hn =>
      by_cases h : PA196.Arithmetic.Scalar.eval x p t d ≤ PA196.Arithmetic.Scalar.eval y p t d
      · simp [graph,eval,PA196.Arithmetic.Scalar.graph_correct,hy,hn,h]
      · have ht := not_le.mp h
        simp [graph,eval,PA196.Arithmetic.Scalar.graph_correct,hy,hn,h,ht]

theorem total_unique (e : Expr) (p t d : V) : ∃! z, (graph e).val.Evalb ![z,p,t,d] :=
  ⟨eval e p t d,(graph_correct _ _ _ _ _).mpr rfl,fun _ hz => (graph_correct _ _ _ _ _).mp hz⟩

#print axioms graph_correct
#print axioms total_unique
end PA196.Arithmetic.WordExpression


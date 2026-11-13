module
public import PA196.Arithmetic.HeadGraphs
public import Foundation.FirstOrder.Arithmetic.HFS.Vec
@[expose] public section
open M6.Arithmetic.PA
namespace PA196.Arithmetic.Scalar
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open M6.PA.SourceCantorInternal

/- Adapted from the generic PA209 expression interpreter, with its original
proved graph structure and a narrowed import closure. -/

/-- Finite straight-line rule arithmetic. The three inputs are the preceding
HFS table, the exact V1 tag, and its payload; this is not a proof calculus. -/
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

noncomputable def graph : Expr → 𝚺ᴬ₁.Semisentence 4
  | .previous => .mkSigma “z p t d. z=p”
  | .tag => .mkSigma “z p t d. z=t”
  | .payload => .mkSigma “z p t d. z=d”
  | .num n => .mkSigma “z p t d. z=↑n”
  | .add x y => .mkSigma “z p t d. ∃ a b, !(graph x) a p t d ∧ !(graph y) b p t d ∧ z=a+b”
  | .sub x y => .mkSigma “z p t d. ∃ a b, !(graph x) a p t d ∧ !(graph y) b p t d ∧ !subDef z a b”
  | .left x => .mkSigma “z p t d. ∃ a b, !(graph x) a p t d ∧ !decodeGraph z b a”
  | .right x => .mkSigma “z p t d. ∃ a b, !(graph x) a p t d ∧ !decodeGraph b z a”
  | .nth xs i => .mkSigma “z p t d. ∃ a b, !(graph xs) a p t d ∧ !(graph i) b p t d ∧ !nthDef z a b”
  | .head e a b c u => .mkSigma “z p t d. ∃ aa bb cc uu,
      !(graph a) aa p t d ∧ !(graph b) bb p t d ∧ !(graph c) cc p t d ∧ !(graph u) uu p t d ∧
      !(M6.PA.ActualArithmeticGraph.graph e) z aa bb cc uu”
  | .ifEq x y yes no => .mkSigma “z p t d. ∃ a b, !(graph x) a p t d ∧ !(graph y) b p t d ∧
      ((a=b ∧ !(graph yes) z p t d) ∨ (a≠b ∧ !(graph no) z p t d))”
  | .ifLe x y yes no => .mkSigma “z p t d. ∃ a b, !(graph x) a p t d ∧ !(graph y) b p t d ∧
      ((a≤b ∧ !(graph yes) z p t d) ∨ (b<a ∧ !(graph no) z p t d))”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def eval : Expr → V → V → V → V
  | .previous,p,_,_ => p
  | .tag,_,t,_ => t
  | .payload,_,_,d => d
  | .num n,_,_,_ => n
  | .add x y,p,t,d => eval x p t d + eval y p t d
  | .sub x y,p,t,d => eval x p t d - eval y p t d
  | .left x,p,t,d => decodeLeft (eval x p t d)
  | .right x,p,t,d => decodeRight (eval x p t d)
  | .nth xs i,p,t,d => FFL.FirstOrder.Arithmetic.nth (eval xs p t d) (eval i p t d)
  | .head e a b c u,p,t,d => M6.PA.ActualArithmeticGraph.eval e (eval a p t d) (eval b p t d) (eval c p t d) (eval u p t d)
  | .ifEq x y yes no,p,t,d => if eval x p t d = eval y p t d then eval yes p t d else eval no p t d
  | .ifLe x y yes no,p,t,d => if eval x p t d ≤ eval y p t d then eval yes p t d else eval no p t d

theorem graph_correct (e : Expr) (z p t d : V) :
    (graph e).val.Evalb ![z,p,t,d] ↔ z=eval e p t d := by
  induction e generalizing z with
  | previous => simp [graph,eval]
  | tag => simp [graph,eval]
  | payload => simp [graph,eval]
  | num n => simp [graph,eval,numeral_eq_natCast]
  | add x y hx hy => simp [graph,eval,hx,hy]
  | sub x y hx hy => simp [graph,eval,hx,hy]
  | left x hx => simp [graph,eval,hx,decode_graph]
  | right x hx => simp [graph,eval,hx,decode_graph]
  | nth xs i hx hi => simp [graph,eval,hx,hi]
  | head e a b c u ha hb hc hu =>
    simp [graph,eval,ha,hb,hc,hu,M6.PA.ActualArithmeticGraph.graph_correct,Matrix.comp_vecCons'']
  | ifEq x y yes no hx hy hyes hno =>
    by_cases h : eval x p t d = eval y p t d <;> simp [graph,eval,hx,hy,hyes,hno,h]
  | ifLe x y yes no hx hy hyes hno =>
    by_cases h : eval x p t d ≤ eval y p t d
    · simp [graph,eval,hx,hy,hyes,hno,h]
    · have ht := not_le.mp h
      simp [graph,eval,hx,hy,hyes,hno,h,ht]

theorem total_unique (e : Expr) (p t d : V) : ∃! z, (graph e).val.Evalb ![z,p,t,d] := by
  exact ⟨eval e p t d,(graph_correct _ _ _ _ _).mpr rfl,
    fun z hz => (graph_correct _ _ _ _ _).mp hz⟩

#print axioms graph_correct
#print axioms total_unique
end PA196.Arithmetic.Scalar


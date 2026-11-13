module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCantorInjectiveInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualArithmeticGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCantorInternal

/-- A tiny arithmetic expression language, not a native proof calculus.
It makes the object graph syntax independent of the chosen arithmetic model. -/
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

noncomputable def graph : Expr → 𝚺ᴬ₁.Semisentence 5
  | .a => .mkSigma “z a b c u. z = a”
  | .b => .mkSigma “z a b c u. z = b”
  | .c => .mkSigma “z a b c u. z = c”
  | .u => .mkSigma “z a b c u. z = u”
  | .lit n => .mkSigma “z a b c u. z = ↑n”
  | .add x y => .mkSigma “z a b c u. ∃ l r, !(graph x) l a b c u ∧ !(graph y) r a b c u ∧ z = l+r”
  | .mul x y => .mkSigma “z a b c u. ∃ l r, !(graph x) l a b c u ∧ !(graph y) r a b c u ∧ z = l*r”
  | .pair x y => .mkSigma “z a b c u. ∃ l r, !(graph x) l a b c u ∧ !(graph y) r a b c u ∧ !pairGraph z l r”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def eval : Expr → V → V → V → V → V
  | .a,a,_,_,_ => a
  | .b,_,b,_,_ => b
  | .c,_,_,c,_ => c
  | .u,_,_,_,u => u
  | .lit n,_,_,_,_ => n
  | .add x y,a,b,c,u => eval x a b c u + eval y a b c u
  | .mul x y,a,b,c,u => eval x a b c u * eval y a b c u
  | .pair x y,a,b,c,u => pairValue (eval x a b c u) (eval y a b c u)

theorem graph_correct (e : Expr) (z a b c u : V) :
    (graph e).val.Evalb ![z,a,b,c,u] ↔ z=eval e a b c u := by
  induction e generalizing z with
  | a => simp [graph,eval]
  | b => simp [graph,eval]
  | c => simp [graph,eval]
  | u => simp [graph,eval]
  | «lit» n => simp [graph,eval,numeral_eq_natCast]
  | add x y ihx ihy => simp [graph,eval,ihx,ihy, Matrix.comp_vecCons'']
  | mul x y ihx ihy => simp [graph,eval,ihx,ihy, Matrix.comp_vecCons'']
  | pair x y ihx ihy => simp [graph,eval,ihx,ihy,SourceCantorInternal.pair_graph, Matrix.comp_vecCons'']

theorem graph_total_unique (e : Expr) (a b c u : V) :
    ∃! z, (graph e).val.Evalb ![z,a,b,c,u] := by
  refine ⟨eval e a b c u,(graph_correct _ _ _ _ _ _).mpr rfl,?_⟩
  intro z hz
  exact (graph_correct _ _ _ _ _ _).mp hz

theorem eval_standard (e : Expr) (a b c u : Nat) : eval e a b c u = evalNat e a b c u := by
  induction e <;> simp [eval,evalNat,pair_standard, *]

noncomputable def totalSentence (e : Expr) : ArithmeticSentence :=
  “∀ a b c u, ∃ z, !(graph e) z a b c u”
theorem pa_proves_total (e : Expr) : theory ⊢ totalSentence e := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [totalSentence,models_iff,Matrix.comp_vecCons'',graph_correct]

#print axioms graph_correct
#print axioms eval_standard
#print axioms pa_proves_total
end M6.PA.ActualArithmeticGraph


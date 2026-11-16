module
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.WordMacros
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Scalar

def atomInput : Expr := .previous
def tailInput : Expr := .tag
def tag : Expr := .left atomInput
def fields : Expr := .right atomInput
/-- Replace the terminal zero of a standalone source command atom with a
new source residual tail. HFS word-vector coding is not used for this pair. -/
def spliceExpr : Expr :=
  .ifEq tag (.num 0) (WordMacros.pair (.num 0) tailInput) <|
  .ifEq tag (.num 1) (WordMacros.pair (.num 1) (WordMacros.pair (.left fields) tailInput)) <|
  WordMacros.pair tag (WordMacros.pair (.left fields) (WordMacros.pair (.left (.right fields)) tailInput))

noncomputable def spliceGraph : 𝚺ᴬ₁.Semisentence 3 :=
  (graph spliceExpr).rew (Rew.subst ![#0,#1,#2,‘0’])
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def spliceValue (atom tail : V) : V := eval spliceExpr atom tail 0

theorem splice_graph (z atom tail : V) :
    spliceGraph.val.Evalb ![z,atom,tail] ↔ z=spliceValue atom tail := by
  simp [spliceGraph,graph_correct,spliceValue]
instance splice_defined : 𝚺ᴬ₁-Function₂ (spliceValue : V → V → V) via spliceGraph := .mk fun v => by
  have hv : v=![v 0,v 1,v 2] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases he with rfl|rfl|rfl <;> rfl
  rw [hv]
  exact splice_graph _ _ _

open SourceCantorInternal

#print axioms splice_graph
end PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal


module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualWordMacros
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCommandEncodingInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckExpression

def atomInput : Expr := .previous
def tailInput : Expr := .tag
def tag : Expr := .left atomInput
def fields : Expr := .right atomInput
/-- Replace the terminal zero of a standalone source command atom with a
new source residual tail. HFS word-vector coding is not used for this pair. -/
def spliceExpr : Expr :=
  .ifEq tag (.num 0) (ActualWordMacros.pair (.num 0) tailInput) <|
  .ifEq tag (.num 1) (ActualWordMacros.pair (.num 1) (ActualWordMacros.pair (.left fields) tailInput)) <|
  ActualWordMacros.pair tag (ActualWordMacros.pair (.left fields) (ActualWordMacros.pair (.left (.right fields)) tailInput))

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

open SourceCantorInternal M6.Source.CommandAtomEncoding

theorem splice_standard (atom tail : Nat) : spliceValue atom tail=splice atom tail := by
  generalize hd : M6.Source.Cantor.decode atom=p
  rcases p with ⟨tag,payload⟩
  cases tag with
  | zero =>
    simp [spliceValue,spliceExpr,atomInput,tailInput,fields,SourceCommandEncodingInternal.tag,
      eval,ActualWordMacros.pair_standard,decodeLeft,decodeRight,decodeState_standard,splice,hd]
  | succ tag =>
    cases tag with
    | zero =>
      simp [spliceValue,spliceExpr,atomInput,tailInput,fields,SourceCommandEncodingInternal.tag,
        eval,ActualWordMacros.pair_standard,decodeLeft,decodeRight,decodeState_standard,splice,hd]
    | succ tag =>
      simp [spliceValue,spliceExpr,atomInput,tailInput,fields,SourceCommandEncodingInternal.tag,
        eval,ActualWordMacros.pair_standard,decodeLeft,decodeRight,decodeState_standard,splice,hd]

#print axioms splice_graph
#print axioms splice_standard
end M6.PA.SourceCommandEncodingInternal


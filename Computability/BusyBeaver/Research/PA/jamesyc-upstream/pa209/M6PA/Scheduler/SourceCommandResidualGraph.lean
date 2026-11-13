module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCommandDecodeInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCommandEncodingInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckExpression
def tagExpr : Expr := .left .previous
def restExpr : Expr := .right .previous

def residualExpr : Expr := .ifEq tagExpr (.num 0) restExpr <|
  .ifEq tagExpr (.num 1) (.right restExpr) (.right (.right restExpr))
def commandAtomExpr : Expr := .ifEq tagExpr (.num 0) (.num 0) <|
  .ifEq tagExpr (.num 1) (ActualWordMacros.pair (.num 1) (ActualWordMacros.pair (.left restExpr) (.num 0))) <|
  ActualWordMacros.pair tagExpr (ActualWordMacros.pair (.left restExpr)
    (ActualWordMacros.pair (.left (.right restExpr)) (.num 0)))
noncomputable def residualGraph : 𝚺ᴬ₁.Semisentence 2 :=
  (graph residualExpr).rew (Rew.subst ![#0,#1,‘0’,‘0’])
noncomputable def commandAtomGraph : 𝚺ᴬ₁.Semisentence 2 :=
  (graph commandAtomExpr).rew (Rew.subst ![#0,#1,‘0’,‘0’])
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem residual_graph (z tail : V) : residualGraph.val.Evalb ![z,tail] ↔ z=residual tail := by
  simp [residualGraph,graph_correct,residualExpr,tagExpr,restExpr,eval,residual]
theorem commandAtom_graph (z tail : V) : commandAtomGraph.val.Evalb ![z,tail] ↔ z=commandAtom tail := by
  simp [commandAtomGraph,graph_correct,commandAtomExpr,tagExpr,restExpr,eval,commandAtom,
    ActualCommandStepGraph.eval_source_pair]
instance residual_defined : 𝚺ᴬ₁-Function₁ (residual : V→V) via residualGraph := .mk fun v => by
  have hv : v=![v 0,v 1] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 := by omega
    rcases he with rfl|rfl <;> rfl
  rw [hv]; exact residual_graph _ _
instance commandAtom_defined : 𝚺ᴬ₁-Function₁ (commandAtom : V→V) via commandAtomGraph := .mk fun v => by
  have hv : v=![v 0,v 1] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 := by omega
    rcases he with rfl|rfl <;> rfl
  rw [hv]; exact commandAtom_graph _ _
#print axioms residual_graph
#print axioms commandAtom_graph
end M6.PA.SourceCommandEncodingInternal


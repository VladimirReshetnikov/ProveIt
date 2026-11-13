module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandPushInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualCommandWordGraph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def jWord (u : V) : V := if u=0 then 0 else mpCode u ∷ 0

theorem eval_mp_atom (u : ActualWordExpression.Scalar) (p a b : V) :
    ActualCheckExpression.eval (ActualWordMacros.mpAtom u) p a b=
      mpCode (ActualCheckExpression.eval u p a b) := by
  simp [ActualWordMacros.mpAtom,eval_source_pair,ActualCheckExpression.eval,mpCode]

theorem j_expr (u : ActualWordExpression.Scalar) (p a b : V) :
    ActualWordExpression.eval (ActualWordMacros.j u) p a b=
      jWord (ActualCheckExpression.eval u p a b) := by
  simp [ActualWordMacros.j,ActualWordMacros.singleton,ActualWordExpression.eval,
    ActualCheckExpression.eval,eval_mp_atom,jWord]

/-- The actual parameter-injection macro is safe for every model value. -/
theorem J_value (u w : V) :
    wordValue (jWord u) (stateCode 0 w 0 0)=stateCode 0 w u 0 := by
  by_cases hu : u=0
  · simp [jWord,hu]
  · have he : ActualArithmeticGraph.eval ActualHeadGraphs.implicationExpr 0 u 0 0≠0 := by
      simpa [implication_eq_zero] using hu
    simp [jWord,hu,word_cons,mp_value,he]

theorem J_expr_value (u : ActualWordExpression.Scalar) (p a b w : V) :
    wordValue (ActualWordExpression.eval (ActualWordMacros.j u) p a b) (stateCode 0 w 0 0)=
      stateCode 0 w (ActualCheckExpression.eval u p a b) 0 := by
  rw [j_expr,J_value]

#print axioms J_value
#print axioms J_expr_value
end M6.PA.ActualCommandStepGraph

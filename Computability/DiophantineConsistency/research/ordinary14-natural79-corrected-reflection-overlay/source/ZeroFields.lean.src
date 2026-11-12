import P84QcubeGraph
import P85QcubeGraph
import FirstRootBridge

/-! Source-only factor extraction from each graph's own zero. Draft imports
and tactics are unelaborated; no natural-norm or endpoint result is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZeroFields8485Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def eval (e : Expr (Fin 14)) (v : Fin 14 → V) : DiffRing V :=
  e.evalRing (fun j => ι (v j))

/-- Extract all five signed field equalities from the 84 graph's own zero. -/
theorem fields84 (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    eval (P84QcubeGraph.graph p).A0 v=0 ∧
    eval (P84QcubeGraph.graph p).A1 v=0 ∧
    eval (P84QcubeGraph.graph p).aux v-1=0 ∧
    eval (P84QcubeGraph.graph p).gap v=0 ∧
    eval (P84QcubeGraph.graph p).guardResidual v=0 := by
  rw [internalZero_iff,P84QcubeGraph.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P84QcubeGraph.graph p).A0 v)
      (eval (P84QcubeGraph.graph p).A1 v) (eval (P84QcubeGraph.graph p).aux v-1)
      (eval (P84QcubeGraph.graph p).gap v) (eval (P84QcubeGraph.graph p).guardResidual v)=0 := by
    simpa only [fiveSquares,eval] using hz
  exact (fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive

/-- Extract all five signed field equalities from the 85 graph's own zero. -/
theorem fields85 (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    eval (P85QcubeGraph.graph p).A0 v=0 ∧
    eval (P85QcubeGraph.graph p).A1 v=0 ∧
    eval (P85QcubeGraph.graph p).aux v-1=0 ∧
    eval (P85QcubeGraph.graph p).gap v=0 ∧
    eval (P85QcubeGraph.graph p).guardResidual v=0 := by
  rw [internalZero_iff,P85QcubeGraph.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P85QcubeGraph.graph p).A0 v)
      (eval (P85QcubeGraph.graph p).A1 v) (eval (P85QcubeGraph.graph p).aux v-1)
      (eval (P85QcubeGraph.graph p).gap v) (eval (P85QcubeGraph.graph p).guardResidual v)=0 := by
    simpa only [fiveSquares,eval] using hz
  exact (fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive

end DiophantineConsistency.ZeroFields8485Draft

#print axioms DiophantineConsistency.ZeroFields8485Draft.fields84
#print axioms DiophantineConsistency.ZeroFields8485Draft.fields85

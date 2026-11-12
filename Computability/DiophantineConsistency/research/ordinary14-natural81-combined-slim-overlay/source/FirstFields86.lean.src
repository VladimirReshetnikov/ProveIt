import P86ResidueGraph
import FirstRootBridge

/-! Source-only 86 own-zero field extraction and first-root evaluation.
Imports are unelaborated drafts; no quotient or witness map is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.FirstFields86Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta
def Q (beta : V) (v : Fin 14 → V) : V := q beta v*(q beta v*q beta v)
def b (beta : V) (v : Fin 14 → V) : V := v 0*beta
def M (beta : V) (v : Fin 14 → V) : V := Q beta v*b beta v
def k (v : Fin 14 → V) : V := v 9+v 10
def ell (v : Fin 14 → V) : V := (v 6*v 7)*(v 7*k v)
def firstP (v : Fin 14 → V) : V := ell v+k v
def radicand (v : Fin 14 → V) : V := 1+ell v*firstP v
def eval (e : Expr (Fin 14)) (v : Fin 14 → V) : DiffRing V := e.evalRing (fun j => ι (v j))
def putRoot (v : Fin 14 → V) (r : V) : Fin 14 → V := Function.update v 8 r

/-- The signed 86 first term is represented as a difference of natural
parts, with no sign or subtraction assumption. -/
theorem first_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P86ResidueGraph.graph p).A0 v=
      (ι (M beta v*firstP v+b beta v*v 7)-ι (M beta v*v 8))*
        (ι (M beta v*firstP v+b beta v*v 7)-ι (M beta v*v 8))-
      (ι (M beta v)*ι (M beta v))*ι (radicand v) := by
  simp [eval,P86ResidueGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,q,Q,b,M,k,ell,firstP,
    radicand,hport,map_add,map_mul,map_one] <;> ring

/-- All non-first fields of the 86 graph ignore its first-root coordinate. -/
theorem other_fields_ignore_root (p : Fin 4 → ℤ) (v : Fin 14 → V) (r : V) :
    eval (P86ResidueGraph.graph p).A1 (putRoot v r)=eval (P86ResidueGraph.graph p).A1 v ∧
    eval (P86ResidueGraph.graph p).aux (putRoot v r)=eval (P86ResidueGraph.graph p).aux v ∧
    eval (P86ResidueGraph.graph p).gap (putRoot v r)=eval (P86ResidueGraph.graph p).gap v ∧
    eval (P86ResidueGraph.graph p).guardResidual (putRoot v r)=
      eval (P86ResidueGraph.graph p).guardResidual v := by
  simp [eval,P86ResidueGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,putRoot,Function.update]

/-- Extract the five signed residuals from this graph's own zero. -/
theorem fields_of_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P86ResidueGraph.graph p).output v) :
    eval (P86ResidueGraph.graph p).A0 v=0 ∧
    eval (P86ResidueGraph.graph p).A1 v=0 ∧
    eval (P86ResidueGraph.graph p).aux v-1=0 ∧
    eval (P86ResidueGraph.graph p).gap v=0 ∧
    eval (P86ResidueGraph.graph p).guardResidual v=0 := by
  rw [internalZero_iff,P86ResidueGraph.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P86ResidueGraph.graph p).A0 v)
      (eval (P86ResidueGraph.graph p).A1 v) (eval (P86ResidueGraph.graph p).aux v-1)
      (eval (P86ResidueGraph.graph p).gap v) (eval (P86ResidueGraph.graph p).guardResidual v)=0 := by
    simpa only [fiveSquares,eval] using hz
  exact (fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive

end DiophantineConsistency.FirstFields86Draft

#print axioms DiophantineConsistency.FirstFields86Draft.first_eval
#print axioms DiophantineConsistency.FirstFields86Draft.fields_of_zero

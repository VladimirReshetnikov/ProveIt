import P88FourSquareGraph
import FirstRootBridge

/-! Source-only extraction of four parent residuals from its own zero.
No target graph, positivity, Lean elaboration or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ParentFourFieldsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def eval (e : Expr (Fin 13)) (v : Fin 13 → V) : DiffRing V := e.evalRing (fun j => ι (v j))

/-- Four parent residuals vanish at the parent four-square own zero. -/
theorem fields_of_zero (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (P88FourSquare.graph p).output v) :
    eval (P88FourSquare.graph p).A0 v=0 ∧
    eval (P88FourSquare.graph p).A1 v=0 ∧
    eval (P88FourSquare.graph p).aux v-1=0 ∧
    eval (P88FourSquare.graph p).gap v=0 := by
  rw [internalZero_iff,P88FourSquare.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P88FourSquare.graph p).A0 v)
      (eval (P88FourSquare.graph p).A1 v) (eval (P88FourSquare.graph p).aux v-1)
      (eval (P88FourSquare.graph p).gap v) 0=0 := by
    simpa only [fiveSquares,eval,mul_zero,add_zero] using hz
  have h := (fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

end DiophantineConsistency.ParentFourFieldsDraft

#print axioms DiophantineConsistency.ParentFourFieldsDraft.fields_of_zero

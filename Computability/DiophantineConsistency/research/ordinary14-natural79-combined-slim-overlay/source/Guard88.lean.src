import P88QuotientGuardedGraph
import FirstRootBridge

/-! Source-only quotient-guard extraction. No positive parent witness,
other graph zero, Lean elaboration or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Guard88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def eval (e : Expr (Fin 14)) (v : Fin 14 → V) : DiffRing V := e.evalRing (fun j => ι (v j))

/-- The 88 own zero gives its signed guard equation; no port cast needed. -/
theorem guard_of_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    eval (P88QuotientGuarded.graph p).Bt v =
      eval (P88QuotientGuarded.graph p).b v*ι (v 13) := by
  rw [internalZero_iff,P88QuotientGuarded.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P88QuotientGuarded.graph p).A0 v)
      (eval (P88QuotientGuarded.graph p).A1 v) (eval (P88QuotientGuarded.graph p).aux v-1)
      (eval (P88QuotientGuarded.graph p).gap v)
      (eval (P88QuotientGuarded.graph p).Bt v-eval (P88QuotientGuarded.graph p).b v*ι (v 13))=0 := by
    simpa only [fiveSquares,eval] using hz
  exact sub_eq_zero.mp ((fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive).2.2.2.2

/-- With a natural beta representation, b is J*beta. -/
theorem b_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P88QuotientGuarded.graph p).b v=ι (v 0*beta) := by
  simp [eval,P88QuotientGuarded.graph,Expr.evalRing_mul,Expr.evalRing_var,
    Expr.evalRing_constant,hport,map_mul]

/-- Same own-zero guard as a cast natural product. -/
theorem bt_of_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    eval (P88QuotientGuarded.graph p).Bt v=ι ((v 0*beta)*v 13) := by
  rw [guard_of_zero p v hz,b_eval p beta v hport,map_mul]

end DiophantineConsistency.Guard88Draft

#print axioms DiophantineConsistency.Guard88Draft.bt_of_zero

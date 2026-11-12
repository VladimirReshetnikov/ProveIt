import FirstFactor74

/-! Source-only alternative cut for the literal 74 first factor. This avoids
unfolding unrelated graph fields in the evaluation proof. No Lean run has
established whether it elaborates or improves resource use. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.FirstFactorSmallCut74Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing FirstFactor74Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def qExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := 1+(.var 0)*(.constant (p 0))
def XExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := qExpr p*(.var 6)
def YExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := (qExpr p*(qExpr p*qExpr p))*(.var 7)
def kExpr : Expr (Fin 14) := (.var 9)+(.var 10)
def ellExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := (XExpr p*YExpr p)*(YExpr p*kExpr)
def firstExpr (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  (.var 8)*(.var 8)-ellExpr p*(ellExpr p+kExpr)

/-- The cut preserves the literal first-factor syntax. -/
theorem first_shape (p : Fin 4 → ℤ) : (P74PositiveGuard.graph p).first=firstExpr p := by rfl

/-- Same statement as the existing draft's first_eval, through the smaller
literal factor cut; beta's model cast remains explicit. -/
theorem first_eval_small (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) :
    (P74PositiveGuard.graph p).first.evalRing (fun j => ι (v j)) =
      ι (v 8*v 8)-ι ((m beta v*k v)*(m beta v*k v+k v)) := by
  rw [first_shape]
  simp [firstExpr,ellExpr,XExpr,YExpr,kExpr,qExpr,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    q,X,Y,m,k,hbeta,map_add,map_mul,map_one] <;> ring

end DiophantineConsistency.FirstFactorSmallCut74Draft

#print axioms DiophantineConsistency.FirstFactorSmallCut74Draft.first_shape
#print axioms DiophantineConsistency.FirstFactorSmallCut74Draft.first_eval_small

import DiophantineConsistency.SharingSign25Squares
import DiophantineConsistency.SharingSign26Squares

/-! SOURCE-ONLY: product cut and its affected norm transfer. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25FirstCut
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [Mul S] (v : Fin 26 → S) : Fin 27 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 17 * v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25]

def oldEll (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 19) - ((Expr.var 17) * (Expr.var 18)))

theorem old_ell_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 3).head? = some (oldEll p) := by rfl

theorem old_ell_zero (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    InternalZero (oldEll p) (lift v) := by
  rw [internalZero_iff]
  simp [oldEll, lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var, map_mul]

def oldN0 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((((Expr.var 22) * (Expr.var 22)) - ((Expr.var 19) * ((Expr.var 19) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

def newN0 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((((Expr.var 21) * (Expr.var 21)) - (((Expr.var 17) * (Expr.var 18)) * (((Expr.var 17) * (Expr.var 18)) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem old_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 8).head? = some (oldN0 p) := by rfl

theorem new_N0_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 7).head? = some (newN0 p) := by rfl

theorem N0_eval (p : Fin 4 → ℤ) (v : Fin 26 → V) :
    (oldN0 p).evalRing (fun j => ι (lift v j)) = (newN0 p).evalRing (fun j => ι (v j)) := by
  simp [oldN0, newN0, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_mul]
end DiophantineConsistency.Sign25FirstCut
#print axioms DiophantineConsistency.Sign25FirstCut.old_ell_row
#print axioms DiophantineConsistency.Sign25FirstCut.old_ell_zero
#print axioms DiophantineConsistency.Sign25FirstCut.old_N0_row
#print axioms DiophantineConsistency.Sign25FirstCut.new_N0_row
#print axioms DiophantineConsistency.Sign25FirstCut.N0_eval

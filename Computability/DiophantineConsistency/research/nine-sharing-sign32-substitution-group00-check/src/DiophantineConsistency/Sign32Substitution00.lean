import DiophantineConsistency.SharingSign32Squares

/-! UNCOMPILED: the eliminated q² residual and its first dependent residual.
No full substitution or zero-set bridge is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32Substitution00
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exactly the draft lift: distinguished input, q² insertion and tail. -/
def lift {S : Type*} [CommSemiring S] (beta : S) (v : Fin 33 → S) : Fin 34 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, (beta * (v 1 + 1) + 1) ^ 2, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32]

/-- The first residual remaining after the old q² row. -/
def oldQ3 (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  (Expr.var 16) - ((Expr.var 15) * (((Expr.constant (p 0)) *
    ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))

theorem old_q3_head (p : Fin 4 → ℤ) :
    (SharingSeed33.remainingResiduals p).head? = some (oldQ3 p) := by rfl

theorem old_q2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    InternalZero (SharingSeed33.firstResidual p) (lift beta v) := by
  rw [internalZero_iff]
  simp [SharingSeed33.firstResidual, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant,
    hp0, map_add, map_mul, pow_two]

theorem old_q3_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldQ3 p).evalRing (fun j => ι (lift beta v j)) =
      (SharingSeed32Sextic.firstResidual p).evalRing (fun j => ι (v j)) := by
  simp [oldQ3, SharingSeed32Sextic.firstResidual, lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant,
    hp0, map_add, map_mul, pow_two]
end DiophantineConsistency.Sign32Substitution00

#print axioms DiophantineConsistency.Sign32Substitution00.old_q3_head
#print axioms DiophantineConsistency.Sign32Substitution00.old_q2_zero
#print axioms DiophantineConsistency.Sign32Substitution00.old_q3_eval

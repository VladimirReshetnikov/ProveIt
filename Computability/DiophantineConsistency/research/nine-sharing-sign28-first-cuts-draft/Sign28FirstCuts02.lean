import DiophantineConsistency.Sign28FirstCuts01

/-! UNCOMPILED: removed cut and affected surviving residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28FirstCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldnormalizedS2 (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 30) - ((Expr.var 29) * (Expr.var 29)))

theorem old_normalizedS2_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 17).head? = some (oldnormalizedS2 p) := by rfl

theorem old_normalizedS2_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    InternalZero (oldnormalizedS2 p) (lift beta v) := by
  rw [internalZero_iff]
  simp [oldnormalizedS2, lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two]

def oldNa (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 30) * (Expr.var 31))) - (Expr.constant (1 : ℤ)))

def newNa (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((Expr.var 27) * (Expr.var 27)) * (Expr.var 28))) - (Expr.constant (1 : ℤ)))

theorem old_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 19).head? = some (oldNa p) := by rfl

theorem new_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 16).head? = some (newNa p) := by rfl

theorem Na_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldNa p).evalRing (fun j => ι (lift beta v j)) = (newNa p).evalRing (fun j => ι (v j)) := by
  simp [oldNa, newNa, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two]

def oldscaledNs (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((((Expr.var 21) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - (Expr.var 30)) - (Expr.var 21))

def newscaledNs (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((((Expr.var 20) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((Expr.var 27) * (Expr.var 27))) - (Expr.var 20))

theorem old_scaledNs_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 20).head? = some (oldscaledNs p) := by rfl

theorem new_scaledNs_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 17).head? = some (newscaledNs p) := by rfl

theorem scaledNs_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V) :
    (oldscaledNs p).evalRing (fun j => ι (lift beta v j)) = (newscaledNs p).evalRing (fun j => ι (v j)) := by
  simp [oldscaledNs, newscaledNs, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two]

end DiophantineConsistency.Sign28FirstCuts

#print axioms DiophantineConsistency.Sign28FirstCuts.old_normalizedS2_row
#print axioms DiophantineConsistency.Sign28FirstCuts.old_normalizedS2_zero
#print axioms DiophantineConsistency.Sign28FirstCuts.old_Na_row
#print axioms DiophantineConsistency.Sign28FirstCuts.new_Na_row
#print axioms DiophantineConsistency.Sign28FirstCuts.Na_eval
#print axioms DiophantineConsistency.Sign28FirstCuts.old_scaledNs_row
#print axioms DiophantineConsistency.Sign28FirstCuts.new_scaledNs_row
#print axioms DiophantineConsistency.Sign28FirstCuts.scaledNs_eval

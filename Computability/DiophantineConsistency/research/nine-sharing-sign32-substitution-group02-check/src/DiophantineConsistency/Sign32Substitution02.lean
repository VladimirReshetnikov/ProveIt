import DiophantineConsistency.Sign32Substitution01

/-! UNCOMPILED: three more remaining substitution identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32Substitution02
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldkY (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 20) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 18)))

def newkY (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 19) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 17)))

theorem old_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 4).head? = some (oldkY p) := by rfl

theorem new_kY_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 3).head? = some (newkY p) := by rfl

theorem kY_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldkY p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newkY p).evalRing (fun j => ι (v j)) := by
  simp [oldkY, newkY, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldell (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 21) - ((Expr.var 19) * (Expr.var 20)))

def newell (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 20) - ((Expr.var 18) * (Expr.var 19)))

theorem old_ell_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 5).head? = some (oldell p) := by rfl

theorem new_ell_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 4).head? = some (newell p) := by rfl

theorem ell_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldell p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newell p).evalRing (fun j => ι (v j)) := by
  simp [oldell, newell, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

def oldDelta (p : Fin 4 → ℤ) : Expr (Fin 34) :=
  ((Expr.var 22) - ((((Expr.var 19) + (Expr.var 18)) * ((Expr.var 19) + (Expr.var 18))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 19) + (Expr.var 18))) + (Expr.constant (3 : ℤ)))))

def newDelta (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 21) - ((((Expr.var 18) + (Expr.var 17)) * ((Expr.var 18) + (Expr.var 17))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 18) + (Expr.var 17))) + (Expr.constant (3 : ℤ)))))

theorem old_Delta_row (p : Fin 4 → ℤ) :
    ((SharingSeed33.remainingResiduals p).drop 6).head? = some (oldDelta p) := by rfl

theorem new_Delta_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 5).head? = some (newDelta p) := by rfl

theorem Delta_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V) :
    (oldDelta p).evalRing (fun j => ι (Sign32Substitution00.lift beta v j)) =
      (newDelta p).evalRing (fun j => ι (v j)) := by
  simp [oldDelta, newDelta, Sign32Substitution00.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign32Substitution02

#print axioms DiophantineConsistency.Sign32Substitution02.old_kY_row
#print axioms DiophantineConsistency.Sign32Substitution02.new_kY_row
#print axioms DiophantineConsistency.Sign32Substitution02.kY_eval
#print axioms DiophantineConsistency.Sign32Substitution02.old_ell_row
#print axioms DiophantineConsistency.Sign32Substitution02.new_ell_row
#print axioms DiophantineConsistency.Sign32Substitution02.ell_eval
#print axioms DiophantineConsistency.Sign32Substitution02.old_Delta_row
#print axioms DiophantineConsistency.Sign32Substitution02.new_Delta_row
#print axioms DiophantineConsistency.Sign32Substitution02.Delta_eval

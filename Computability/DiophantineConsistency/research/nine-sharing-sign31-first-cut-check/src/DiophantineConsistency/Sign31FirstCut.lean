import DiophantineConsistency.SharingSign31Squares
import DiophantineConsistency.SharingSign32Squares

/-! UNCOMPILED: f² removal and its two affected surviving rows. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31FirstCut
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [CommSemiring S] (v : Fin 32 → S) : Fin 33 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, (v 5 + 1) ^ 2, v 27, v 28, v 29, v 30, v 31] 

def oldF2 (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 27) - (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))))

theorem old_f2_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 14).head? = some (oldF2 p) := by rfl

theorem old_f2_zero (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    InternalZero (oldF2 p) (lift v) := by
  rw [internalZero_iff]
  simp [oldF2, lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two]

def oldV (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((Expr.var 29) - (((Expr.var 27) * (Expr.var 28)) - ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

def newV (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((Expr.var 28) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 27)) - ((Expr.var 19) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

theorem old_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 16).head? = some (oldV p) := by rfl

theorem new_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 15).head? = some (newV p) := by rfl

theorem V_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldV p).evalRing (fun j => ι (lift v j)) = (newV p).evalRing (fun j => ι (v j)) := by
  simp [oldV, newV, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two]

def oldscaledNs (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  ((((Expr.var 21) * (Expr.var 27)) - (Expr.var 31)) - (Expr.var 21))

def newscaledNs (p : Fin 4 → ℤ) : Expr (Fin 32) :=
  ((((Expr.var 21) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - (Expr.var 30)) - (Expr.var 21))

theorem old_scaledNs_row (p : Fin 4 → ℤ) :
    ((SharingSeed32Sextic.remainingResiduals p).drop 21).head? = some (oldscaledNs p) := by rfl

theorem new_scaledNs_row (p : Fin 4 → ℤ) :
    ((SharingSeed31Sextic.remainingResiduals p).drop 20).head? = some (newscaledNs p) := by rfl

theorem scaledNs_eval (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    (oldscaledNs p).evalRing (fun j => ι (lift v j)) = (newscaledNs p).evalRing (fun j => ι (v j)) := by
  simp [oldscaledNs, newscaledNs, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, pow_two]

end DiophantineConsistency.Sign31FirstCut

#print axioms DiophantineConsistency.Sign31FirstCut.old_f2_row
#print axioms DiophantineConsistency.Sign31FirstCut.old_f2_zero
#print axioms DiophantineConsistency.Sign31FirstCut.old_V_row
#print axioms DiophantineConsistency.Sign31FirstCut.new_V_row
#print axioms DiophantineConsistency.Sign31FirstCut.V_eval
#print axioms DiophantineConsistency.Sign31FirstCut.old_scaledNs_row
#print axioms DiophantineConsistency.Sign31FirstCut.new_scaledNs_row
#print axioms DiophantineConsistency.Sign31FirstCut.scaledNs_eval

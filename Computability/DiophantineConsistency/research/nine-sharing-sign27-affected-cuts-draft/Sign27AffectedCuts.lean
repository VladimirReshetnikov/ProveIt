import DiophantineConsistency.Sign27FirstCut

/-! SOURCE-ONLY: three residual identities affected by root normalization. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27AffectedCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldMainRoot (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 21) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 17) + (Expr.var 16)) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ))))))

def newMainRoot (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  (((Expr.var 21) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 17) + (Expr.var 16)) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ))))))

theorem old_MainRoot_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 5).head? = some (oldMainRoot p) := by rfl

theorem new_MainRoot_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 5).head? = some (newMainRoot p) := by rfl

theorem MainRoot_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldMainRoot p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newMainRoot p).evalRing (fun j => ι (v j)) := by
  simp [oldMainRoot, newMainRoot, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]


def oldDc2 (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 22) - ((Expr.var 20) * (((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))

def newDc2 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  (((Expr.var 21) * ((Expr.var 21) + (Expr.constant (2 : ℤ)))) - ((Expr.var 20) * (((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))

theorem old_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 6).head? = some (oldDc2 p) := by rfl

theorem new_Dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 6).head? = some (newDc2 p) := by rfl

theorem Dc2_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldDc2 p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newDc2 p).evalRing (fun j => ι (v j)) := by
  simp [oldDc2, newDc2, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]


def oldNormalizedS (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 27) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (Expr.var 22)))

def newNormalizedS (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 26) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 21) * ((Expr.var 21) + (Expr.constant (2 : ℤ))))))

theorem old_NormalizedS_row (p : Fin 4 → ℤ) :
    ((SharingSeed28Sextic.remainingResiduals p).drop 14).head? = some (oldNormalizedS p) := by rfl

theorem new_NormalizedS_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 13).head? = some (newNormalizedS p) := by rfl

theorem NormalizedS_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (oldNormalizedS p).evalRing (fun j => ι (Sign27FirstCut.lift v j)) =
      (newNormalizedS p).evalRing (fun j => ι (v j)) := by
  simp [oldNormalizedS, newNormalizedS, Sign27FirstCut.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

end DiophantineConsistency.Sign27AffectedCuts
#print axioms DiophantineConsistency.Sign27AffectedCuts.old_MainRoot_row
#print axioms DiophantineConsistency.Sign27AffectedCuts.new_MainRoot_row
#print axioms DiophantineConsistency.Sign27AffectedCuts.MainRoot_eval
#print axioms DiophantineConsistency.Sign27AffectedCuts.old_Dc2_row
#print axioms DiophantineConsistency.Sign27AffectedCuts.new_Dc2_row
#print axioms DiophantineConsistency.Sign27AffectedCuts.Dc2_eval
#print axioms DiophantineConsistency.Sign27AffectedCuts.old_NormalizedS_row
#print axioms DiophantineConsistency.Sign27AffectedCuts.new_NormalizedS_row
#print axioms DiophantineConsistency.Sign27AffectedCuts.NormalizedS_eval

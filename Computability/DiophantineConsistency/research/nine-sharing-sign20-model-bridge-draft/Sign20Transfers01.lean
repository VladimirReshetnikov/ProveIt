import DiophantineConsistency.Sign20Coordinate

/-! SOURCE-ONLY: E substitution transfers; no Lean compilation claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldcTminusR (p : Fin 4 → ℤ) : Expr (Fin 22) :=
  ((Expr.var 19) - ((((((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newcTminusR (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  ((Expr.var 18) - ((((((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_cTminusR_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 6).head? = some (oldcTminusR p) := by rfl

theorem new_cTminusR_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 5).head? = some (newcTminusR p) := by rfl

theorem cTminusR_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldcTminusR p).evalRing (fun j => ι (Sign20Coordinate.lift beta v j)) =
      (newcTminusR p).evalRing (fun j => ι (v j)) := by
  simp [oldcTminusR, newcTminusR, Sign20Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat, hp0]

def oldV (p : Fin 4 → ℤ) : Expr (Fin 22) :=
  ((Expr.var 20) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 19)) - (((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

def newV (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  ((Expr.var 19) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 18)) - (((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

theorem old_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 7).head? = some (oldV p) := by rfl

theorem new_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 6).head? = some (newV p) := by rfl

theorem V_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldV p).evalRing (fun j => ι (Sign20Coordinate.lift beta v j)) =
      (newV p).evalRing (fun j => ι (v j)) := by
  simp [oldV, newV, Sign20Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat, hp0]

def oldV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 22) :=
  ((Expr.var 21) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 20) * (Expr.var 20))))

def newV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  ((Expr.var 20) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 19) * (Expr.var 19))))

theorem old_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 8).head? = some (oldV2minusY2 p) := by rfl

theorem new_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 7).head? = some (newV2minusY2 p) := by rfl

theorem V2minusY2_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldV2minusY2 p).evalRing (fun j => ι (Sign20Coordinate.lift beta v j)) =
      (newV2minusY2 p).evalRing (fun j => ι (v j)) := by
  simp [oldV2minusY2, newV2minusY2, Sign20Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat, hp0]

def oldNa (p : Fin 4 → ℤ) : Expr (Fin 22) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 17) * ((Expr.var 17) + (Expr.constant (2 : ℤ))))) * (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 17) * ((Expr.var 17) + (Expr.constant (2 : ℤ)))))) * (Expr.var 21))) - (Expr.constant (1 : ℤ)))

def newNa (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 16) * ((Expr.var 16) + (Expr.constant (2 : ℤ))))) * (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 16) * ((Expr.var 16) + (Expr.constant (2 : ℤ)))))) * (Expr.var 20))) - (Expr.constant (1 : ℤ)))

theorem old_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 9).head? = some (oldNa p) := by rfl

theorem new_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 8).head? = some (newNa p) := by rfl

theorem Na_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldNa p).evalRing (fun j => ι (Sign20Coordinate.lift beta v j)) =
      (newNa p).evalRing (fun j => ι (v j)) := by
  simp [oldNa, newNa, Sign20Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat, hp0]

def oldscaled_Ns (p : Fin 4 → ℤ) : Expr (Fin 22) :=
  (((((((Expr.var 16) + (Expr.var 15)) * ((Expr.var 16) + (Expr.var 15))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ)))) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 17) * ((Expr.var 17) + (Expr.constant (2 : ℤ))))) * (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 17) * ((Expr.var 17) + (Expr.constant (2 : ℤ))))))) - ((((Expr.var 16) + (Expr.var 15)) * ((Expr.var 16) + (Expr.var 15))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ)))))

def newscaled_Ns (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  ((((((((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + (Expr.var 15)) * (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + (Expr.var 15))) + (((Expr.constant (4 : ℤ)) * (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + (Expr.var 15))) + (Expr.constant (3 : ℤ)))) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 16) * ((Expr.var 16) + (Expr.constant (2 : ℤ))))) * (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 16) * ((Expr.var 16) + (Expr.constant (2 : ℤ))))))) - (((((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + (Expr.var 15)) * (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + (Expr.var 15))) + (((Expr.constant (4 : ℤ)) * (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + (Expr.var 15))) + (Expr.constant (3 : ℤ)))))

theorem old_scaled_Ns_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 10).head? = some (oldscaled_Ns p) := by rfl

theorem new_scaled_Ns_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 9).head? = some (newscaled_Ns p) := by rfl

theorem scaled_Ns_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldscaled_Ns p).evalRing (fun j => ι (Sign20Coordinate.lift beta v j)) =
      (newscaled_Ns p).evalRing (fun j => ι (v j)) := by
  simp [oldscaled_Ns, newscaled_Ns, Sign20Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat, hp0]

end DiophantineConsistency.Sign20Transfers
#print axioms DiophantineConsistency.Sign20Transfers.cTminusR_eval
#print axioms DiophantineConsistency.Sign20Transfers.V_eval
#print axioms DiophantineConsistency.Sign20Transfers.V2minusY2_eval
#print axioms DiophantineConsistency.Sign20Transfers.Na_eval
#print axioms DiophantineConsistency.Sign20Transfers.scaled_Ns_eval

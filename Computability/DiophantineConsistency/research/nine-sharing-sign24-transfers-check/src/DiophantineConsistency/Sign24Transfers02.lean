import DiophantineConsistency.Sign24Coordinate

/-! SOURCE-ONLY: q3 substitution transfers; no Lean compilation claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldV (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 23) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 22)) - ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

def newV (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 22) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 21)) - ((Expr.var 17) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))

theorem old_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 10).head? = some (oldV p) := by rfl

theorem new_V_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 9).head? = some (newV p) := by rfl

theorem V_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldV p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newV p).evalRing (fun j => ι (v j)) := by
  simp [oldV, newV, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

def oldnormalized_S (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 24) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 20) * ((Expr.var 20) + (Expr.constant (2 : ℤ))))))

def newnormalized_S (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 23) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * ((Expr.var 19) * ((Expr.var 19) + (Expr.constant (2 : ℤ))))))

theorem old_normalized_S_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 11).head? = some (oldnormalized_S p) := by rfl

theorem new_normalized_S_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 10).head? = some (newnormalized_S p) := by rfl

theorem normalized_S_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldnormalized_S p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newnormalized_S p).evalRing (fun j => ι (v j)) := by
  simp [oldnormalized_S, newnormalized_S, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

def oldV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((Expr.var 25) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 23) * (Expr.var 23))))

def newV2minusY2 (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 24) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 22) * (Expr.var 22))))

theorem old_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 12).head? = some (oldV2minusY2 p) := by rfl

theorem new_V2minusY2_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 11).head? = some (newV2minusY2 p) := by rfl

theorem V2minusY2_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldV2minusY2 p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newV2minusY2 p).evalRing (fun j => ι (v j)) := by
  simp [oldV2minusY2, newV2minusY2, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

def oldNa (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((Expr.var 24) * (Expr.var 24)) * (Expr.var 25))) - (Expr.constant (1 : ℤ)))

def newNa (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((Expr.var 23) * (Expr.var 23)) * (Expr.var 24))) - (Expr.constant (1 : ℤ)))

theorem old_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 13).head? = some (oldNa p) := by rfl

theorem new_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 12).head? = some (newNa p) := by rfl

theorem Na_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldNa p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newNa p).evalRing (fun j => ι (v j)) := by
  simp [oldNa, newNa, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

def oldscaled_Ns (p : Fin 4 → ℤ) : Expr (Fin 26) :=
  ((((Expr.var 19) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((Expr.var 24) * (Expr.var 24))) - (Expr.var 19))

def newscaled_Ns (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((((Expr.var 18) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((Expr.var 23) * (Expr.var 23))) - (Expr.var 18))

theorem old_scaled_Ns_row (p : Fin 4 → ℤ) :
    ((SharingSeed25Octic.remainingResiduals p).drop 14).head? = some (oldscaled_Ns p) := by rfl

theorem new_scaled_Ns_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 13).head? = some (newscaled_Ns p) := by rfl

theorem scaled_Ns_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldscaled_Ns p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =
      (newscaled_Ns p).evalRing (fun j => ι (v j)) := by
  simp [oldscaled_Ns, newscaled_Ns, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

end DiophantineConsistency.Sign24Transfers
#print axioms DiophantineConsistency.Sign24Transfers.V_eval
#print axioms DiophantineConsistency.Sign24Transfers.normalized_S_eval
#print axioms DiophantineConsistency.Sign24Transfers.V2minusY2_eval
#print axioms DiophantineConsistency.Sign24Transfers.Na_eval
#print axioms DiophantineConsistency.Sign24Transfers.scaled_Ns_eval

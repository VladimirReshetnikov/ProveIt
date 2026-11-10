import DiophantineConsistency.Sign16Coordinate

/-! SOURCE-ONLY individual conditional signed residual transfer. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldscaled_Ns (p : Fin 4 → ℤ) : Expr (Fin 18) := SharingSeed17Degree96.row07 p
def newscaled_Ns (p : Fin 4 → ℤ) : Expr (Fin 17) := SharingSeed16Degree112.row06 p

theorem old_scaled_Ns_row (p : Fin 4 → ℤ) :
    ((SharingSeed17Degree96.remainingResiduals p).drop 6).head? = some (oldscaled_Ns p) := by rfl

theorem new_scaled_Ns_row (p : Fin 4 → ℤ) :
    ((SharingSeed16Degree112.remainingResiduals p).drop 5).head? = some (newscaled_Ns p) := by rfl

theorem scaled_Ns_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V) (gap : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hg : ι gap = (ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16) - ι (C beta v)) :
    (oldscaled_Ns p).evalRing (fun j => ι (Sign16Coordinate.lift v gap j)) =
      (newscaled_Ns p).evalRing (fun j => ι (v j)) := by
  simp [oldscaled_Ns, newscaled_Ns, SharingSeed17Degree96.row07, SharingSeed16Degree112.row06,
    SharingSeed17Degree96.shared00, SharingSeed17Degree96.shared01, SharingSeed17Degree96.shared02, SharingSeed17Degree96.shared03, SharingSeed17Degree96.shared04, SharingSeed17Degree96.shared05, SharingSeed17Degree96.shared06, SharingSeed17Degree96.shared07, SharingSeed17Degree96.shared08, SharingSeed17Degree96.shared09, SharingSeed17Degree96.shared10, SharingSeed17Degree96.shared11, SharingSeed17Degree96.shared12, SharingSeed17Degree96.shared13, SharingSeed17Degree96.shared14, SharingSeed17Degree96.shared15, SharingSeed17Degree96.shared16, SharingSeed17Degree96.shared17, SharingSeed17Degree96.shared18, SharingSeed17Degree96.shared19, SharingSeed17Degree96.shared20, SharingSeed17Degree96.shared21, SharingSeed17Degree96.shared22, SharingSeed17Degree96.shared23, SharingSeed17Degree96.shared24, SharingSeed17Degree96.shared25, SharingSeed17Degree96.shared26, SharingSeed17Degree96.shared27, SharingSeed17Degree96.shared28, SharingSeed17Degree96.shared29, SharingSeed17Degree96.shared30, SharingSeed17Degree96.shared31, SharingSeed17Degree96.shared32, SharingSeed17Degree96.shared33, SharingSeed17Degree96.shared34, SharingSeed16Degree112.shared00, SharingSeed16Degree112.shared01, SharingSeed16Degree112.shared02, SharingSeed16Degree112.shared03, SharingSeed16Degree112.shared04, SharingSeed16Degree112.shared05, SharingSeed16Degree112.shared06, SharingSeed16Degree112.shared07, SharingSeed16Degree112.shared08, SharingSeed16Degree112.shared09, SharingSeed16Degree112.shared10, SharingSeed16Degree112.shared11, SharingSeed16Degree112.shared12, SharingSeed16Degree112.shared13, SharingSeed16Degree112.shared14, SharingSeed16Degree112.shared15, SharingSeed16Degree112.shared16, SharingSeed16Degree112.shared17, SharingSeed16Degree112.shared18, SharingSeed16Degree112.shared19, SharingSeed16Degree112.shared20, SharingSeed16Degree112.shared21, SharingSeed16Degree112.shared22, SharingSeed16Degree112.shared23, SharingSeed16Degree112.shared24, SharingSeed16Degree112.shared25, SharingSeed16Degree112.shared26, SharingSeed16Degree112.shared27, SharingSeed16Degree112.shared28, SharingSeed16Degree112.shared29, SharingSeed16Degree112.shared30, SharingSeed16Degree112.shared31, SharingSeed16Degree112.shared32, SharingSeed16Degree112.shared33, SharingSeed16Degree112.shared34, SharingSeed16Degree112.shared35, SharingSeed16Degree112.shared36, Sign16Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul,
    map_ofNat, C, Y, A, hp0, hg]
end DiophantineConsistency.Sign16Transfers
#print axioms DiophantineConsistency.Sign16Transfers.scaled_Ns_eval

import DiophantineConsistency.Sign17Coordinate

/-! SOURCE-ONLY individual conditional signed residual transfer. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldtau (p : Fin 4 → ℤ) : Expr (Fin 19) := SharingSeed18Degree94.row01 p
def newtau (p : Fin 4 → ℤ) : Expr (Fin 18) := SharingSeed17Degree96.row01 p

theorem old_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed18Degree94.remainingResiduals p).drop 0).head? = some (oldtau p) := by rfl

theorem new_tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed17Degree96.remainingResiduals p).drop 0).head? = some (newtau p) := by rfl

theorem tau_eval (p : Fin 4 → ℤ) (v : Fin 18 → V) (gap : V)
    (hg : ι gap = (ι (v 13) + 1) * (ι (v 13) + 1) - ι (v 17) * ι (v 17)) :
    (oldtau p).evalRing (fun j => ι (Sign17Coordinate.lift v gap j)) =
      (newtau p).evalRing (fun j => ι (v j)) := by
  simp [oldtau, newtau, SharingSeed18Degree94.row01, SharingSeed17Degree96.row01,
    SharingSeed18Degree94.shared00, SharingSeed18Degree94.shared01, SharingSeed18Degree94.shared02, SharingSeed18Degree94.shared03, SharingSeed18Degree94.shared04, SharingSeed18Degree94.shared05, SharingSeed18Degree94.shared06, SharingSeed18Degree94.shared07, SharingSeed18Degree94.shared08, SharingSeed18Degree94.shared09, SharingSeed18Degree94.shared10, SharingSeed18Degree94.shared11, SharingSeed18Degree94.shared12, SharingSeed18Degree94.shared13, SharingSeed18Degree94.shared14, SharingSeed18Degree94.shared15, SharingSeed18Degree94.shared16, SharingSeed18Degree94.shared17, SharingSeed18Degree94.shared18, SharingSeed18Degree94.shared19, SharingSeed18Degree94.shared20, SharingSeed18Degree94.shared21, SharingSeed18Degree94.shared22, SharingSeed18Degree94.shared23, SharingSeed18Degree94.shared24, SharingSeed18Degree94.shared25, SharingSeed18Degree94.shared26, SharingSeed18Degree94.shared27, SharingSeed18Degree94.shared28, SharingSeed18Degree94.shared29, SharingSeed18Degree94.shared30, SharingSeed18Degree94.shared31, SharingSeed18Degree94.shared32, SharingSeed18Degree94.shared33, SharingSeed18Degree94.shared34, SharingSeed17Degree96.shared00, SharingSeed17Degree96.shared01, SharingSeed17Degree96.shared02, SharingSeed17Degree96.shared03, SharingSeed17Degree96.shared04, SharingSeed17Degree96.shared05, SharingSeed17Degree96.shared06, SharingSeed17Degree96.shared07, SharingSeed17Degree96.shared08, SharingSeed17Degree96.shared09, SharingSeed17Degree96.shared10, SharingSeed17Degree96.shared11, SharingSeed17Degree96.shared12, SharingSeed17Degree96.shared13, SharingSeed17Degree96.shared14, SharingSeed17Degree96.shared15, SharingSeed17Degree96.shared16, SharingSeed17Degree96.shared17, SharingSeed17Degree96.shared18, SharingSeed17Degree96.shared19, SharingSeed17Degree96.shared20, SharingSeed17Degree96.shared21, SharingSeed17Degree96.shared22, SharingSeed17Degree96.shared23, SharingSeed17Degree96.shared24, SharingSeed17Degree96.shared25, SharingSeed17Degree96.shared26, SharingSeed17Degree96.shared27, SharingSeed17Degree96.shared28, SharingSeed17Degree96.shared29, SharingSeed17Degree96.shared30, SharingSeed17Degree96.shared31, SharingSeed17Degree96.shared32, SharingSeed17Degree96.shared33, SharingSeed17Degree96.shared34, Sign17Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul,
    map_ofNat, hg]
end DiophantineConsistency.Sign17Transfers
#print axioms DiophantineConsistency.Sign17Transfers.tau_eval

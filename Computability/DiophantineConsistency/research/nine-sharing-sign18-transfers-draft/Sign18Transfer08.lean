import DiophantineConsistency.Sign18Coordinate

/-! SOURCE-ONLY individual staged residual transfer. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign18Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldscaled_Ns (p : Fin 4 → ℤ) : Expr (Fin 20) := SharingSeed19Degree44.row09 p
def newscaled_Ns (p : Fin 4 → ℤ) : Expr (Fin 19) := SharingSeed18Degree94.row08 p

theorem old_scaled_Ns_row (p : Fin 4 → ℤ) :
    ((SharingSeed19Degree44.remainingResiduals p).drop 8).head? = some (oldscaled_Ns p) := by rfl

theorem new_scaled_Ns_row (p : Fin 4 → ℤ) :
    ((SharingSeed18Degree94.remainingResiduals p).drop 7).head? = some (newscaled_Ns p) := by rfl

theorem scaled_Ns_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 19 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (oldscaled_Ns p).evalRing (fun j => ι (Sign18Coordinate.lift beta v j)) =
      (newscaled_Ns p).evalRing (fun j => ι (v j)) := by
  simp [oldscaled_Ns, newscaled_Ns, SharingSeed19Degree44.row09, SharingSeed18Degree94.row08,
    SharingSeed18Degree94.shared00, SharingSeed18Degree94.shared01, SharingSeed18Degree94.shared02, SharingSeed18Degree94.shared03, SharingSeed18Degree94.shared04, SharingSeed18Degree94.shared05, SharingSeed18Degree94.shared06, SharingSeed18Degree94.shared07, SharingSeed18Degree94.shared08, SharingSeed18Degree94.shared09, SharingSeed18Degree94.shared10, SharingSeed18Degree94.shared11, SharingSeed18Degree94.shared12, SharingSeed18Degree94.shared13, SharingSeed18Degree94.shared14, SharingSeed18Degree94.shared15, SharingSeed18Degree94.shared16, SharingSeed18Degree94.shared17, SharingSeed18Degree94.shared18, SharingSeed18Degree94.shared19, SharingSeed18Degree94.shared20, SharingSeed18Degree94.shared21, SharingSeed18Degree94.shared22, SharingSeed18Degree94.shared23, SharingSeed18Degree94.shared24, SharingSeed18Degree94.shared25, SharingSeed18Degree94.shared26, SharingSeed18Degree94.shared27, SharingSeed18Degree94.shared28, SharingSeed18Degree94.shared29, SharingSeed18Degree94.shared30, SharingSeed18Degree94.shared31, SharingSeed18Degree94.shared32, SharingSeed18Degree94.shared33, SharingSeed18Degree94.shared34, Sign18Coordinate.lift, Sign18Coordinate.rootValue, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant,
    map_add, map_mul, map_ofNat, hp0]
end DiophantineConsistency.Sign18Transfers
#print axioms DiophantineConsistency.Sign18Transfers.scaled_Ns_eval

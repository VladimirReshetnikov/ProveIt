import DiophantineConsistency.Sign15Coordinate

/-! SOURCE-ONLY supplied-inner residual transfer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign15Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldNt (p : Fin 4 → ℤ) : Expr (Fin 17) := SharingSeed16Degree112.row03 p
def newNt (p : Fin 4 → ℤ) : Expr (Fin 16) := SharingSeed15Degree124.row03 p

theorem old_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed16Degree112.remainingResiduals p).drop 2).head? = some (oldNt p) := by rfl

theorem new_Nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed15Degree124.remainingResiduals p).drop 2).head? = some (newNt p) := by rfl

theorem Nt_eval (p : Fin 4 → ℤ) (v : Fin 16 → V) (gap : V)
    (hg : ι gap = (SharingSeed15Degree124.shared31 p).evalRing (fun j => ι (v j))) :
    (oldNt p).evalRing (fun j => ι (Sign15Coordinate.lift v gap j)) =
      (newNt p).evalRing (fun j => ι (v j)) := by
  simp [oldNt, newNt, SharingSeed16Degree112.row03, SharingSeed15Degree124.row03,
    SharingSeed16Degree112.shared00, SharingSeed16Degree112.shared01, SharingSeed16Degree112.shared02, SharingSeed16Degree112.shared03, SharingSeed16Degree112.shared04, SharingSeed16Degree112.shared05, SharingSeed16Degree112.shared06, SharingSeed16Degree112.shared07, SharingSeed16Degree112.shared08, SharingSeed16Degree112.shared09, SharingSeed16Degree112.shared10, SharingSeed16Degree112.shared11, SharingSeed16Degree112.shared12, SharingSeed16Degree112.shared13, SharingSeed16Degree112.shared14, SharingSeed16Degree112.shared15, SharingSeed16Degree112.shared16, SharingSeed16Degree112.shared17, SharingSeed16Degree112.shared18, SharingSeed16Degree112.shared19, SharingSeed16Degree112.shared20, SharingSeed16Degree112.shared21, SharingSeed16Degree112.shared22, SharingSeed16Degree112.shared23, SharingSeed16Degree112.shared24, SharingSeed16Degree112.shared25, SharingSeed16Degree112.shared26, SharingSeed16Degree112.shared27, SharingSeed16Degree112.shared28, SharingSeed16Degree112.shared29, SharingSeed16Degree112.shared30, SharingSeed16Degree112.shared31, SharingSeed16Degree112.shared32, SharingSeed16Degree112.shared33, SharingSeed16Degree112.shared34, SharingSeed16Degree112.shared35, SharingSeed16Degree112.shared36, SharingSeed15Degree124.shared00, SharingSeed15Degree124.shared01, SharingSeed15Degree124.shared02, SharingSeed15Degree124.shared03, SharingSeed15Degree124.shared04, SharingSeed15Degree124.shared05, SharingSeed15Degree124.shared06, SharingSeed15Degree124.shared07, SharingSeed15Degree124.shared08, SharingSeed15Degree124.shared09, SharingSeed15Degree124.shared10, SharingSeed15Degree124.shared11, SharingSeed15Degree124.shared12, SharingSeed15Degree124.shared13, SharingSeed15Degree124.shared14, SharingSeed15Degree124.shared15, SharingSeed15Degree124.shared16, SharingSeed15Degree124.shared17, SharingSeed15Degree124.shared18, SharingSeed15Degree124.shared19, SharingSeed15Degree124.shared20, SharingSeed15Degree124.shared21, SharingSeed15Degree124.shared22, SharingSeed15Degree124.shared23, SharingSeed15Degree124.shared24, SharingSeed15Degree124.shared25, SharingSeed15Degree124.shared26, SharingSeed15Degree124.shared27, SharingSeed15Degree124.shared28, SharingSeed15Degree124.shared29, SharingSeed15Degree124.shared30, SharingSeed15Degree124.shared31, SharingSeed15Degree124.shared32, SharingSeed15Degree124.shared33, SharingSeed15Degree124.shared34, SharingSeed15Degree124.shared35, SharingSeed15Degree124.shared36, SharingSeed15Degree124.shared37, SharingSeed15Degree124.shared38, SharingSeed15Degree124.shared39, Sign15Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul,
    map_ofNat, hg]
end DiophantineConsistency.Sign15Transfers
#print axioms DiophantineConsistency.Sign15Transfers.Nt_eval

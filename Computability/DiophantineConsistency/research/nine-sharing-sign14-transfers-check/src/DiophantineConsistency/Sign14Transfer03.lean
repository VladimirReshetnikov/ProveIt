import DiophantineConsistency.Sign14Coordinate

/-! SOURCE-ONLY supplied-inner residual transfer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldNa (p : Fin 4 → ℤ) : Expr (Fin 16) := SharingSeed15Degree124.row04 p
def newNa (p : Fin 4 → ℤ) : Expr (Fin 15) := SharingSeed14Degree124.row03 p

theorem old_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed15Degree124.remainingResiduals p).drop 3).head? = some (oldNa p) := by rfl

theorem new_Na_row (p : Fin 4 → ℤ) :
    ((SharingSeed14Degree124.remainingResiduals p).drop 2).head? = some (newNa p) := by rfl

theorem Na_eval (p : Fin 4 → ℤ) (v : Fin 15 → V) (gap : V)
    (hg : ι gap = (SharingSeed14Degree124.shared36 p).evalRing (fun j => ι (v j))) :
    (oldNa p).evalRing (fun j => ι (Sign14Coordinate.lift v gap j)) =
      (newNa p).evalRing (fun j => ι (v j)) := by
  simp [oldNa, newNa, SharingSeed15Degree124.row04, SharingSeed14Degree124.row03,
    SharingSeed15Degree124.shared00, SharingSeed15Degree124.shared01, SharingSeed15Degree124.shared02, SharingSeed15Degree124.shared03, SharingSeed15Degree124.shared04, SharingSeed15Degree124.shared05, SharingSeed15Degree124.shared06, SharingSeed15Degree124.shared07, SharingSeed15Degree124.shared08, SharingSeed15Degree124.shared09, SharingSeed15Degree124.shared10, SharingSeed15Degree124.shared11, SharingSeed15Degree124.shared12, SharingSeed15Degree124.shared13, SharingSeed15Degree124.shared14, SharingSeed15Degree124.shared15, SharingSeed15Degree124.shared16, SharingSeed15Degree124.shared17, SharingSeed15Degree124.shared18, SharingSeed15Degree124.shared19, SharingSeed15Degree124.shared20, SharingSeed15Degree124.shared21, SharingSeed15Degree124.shared22, SharingSeed15Degree124.shared23, SharingSeed15Degree124.shared24, SharingSeed15Degree124.shared25, SharingSeed15Degree124.shared26, SharingSeed15Degree124.shared27, SharingSeed15Degree124.shared28, SharingSeed15Degree124.shared29, SharingSeed15Degree124.shared30, SharingSeed15Degree124.shared31, SharingSeed15Degree124.shared32, SharingSeed15Degree124.shared33, SharingSeed15Degree124.shared34, SharingSeed15Degree124.shared35, SharingSeed15Degree124.shared36, SharingSeed15Degree124.shared37, SharingSeed15Degree124.shared38, SharingSeed15Degree124.shared39, SharingSeed14Degree124.shared00, SharingSeed14Degree124.shared01, SharingSeed14Degree124.shared02, SharingSeed14Degree124.shared03, SharingSeed14Degree124.shared04, SharingSeed14Degree124.shared05, SharingSeed14Degree124.shared06, SharingSeed14Degree124.shared07, SharingSeed14Degree124.shared08, SharingSeed14Degree124.shared09, SharingSeed14Degree124.shared10, SharingSeed14Degree124.shared11, SharingSeed14Degree124.shared12, SharingSeed14Degree124.shared13, SharingSeed14Degree124.shared14, SharingSeed14Degree124.shared15, SharingSeed14Degree124.shared16, SharingSeed14Degree124.shared17, SharingSeed14Degree124.shared18, SharingSeed14Degree124.shared19, SharingSeed14Degree124.shared20, SharingSeed14Degree124.shared21, SharingSeed14Degree124.shared22, SharingSeed14Degree124.shared23, SharingSeed14Degree124.shared24, SharingSeed14Degree124.shared25, SharingSeed14Degree124.shared26, SharingSeed14Degree124.shared27, SharingSeed14Degree124.shared28, SharingSeed14Degree124.shared29, SharingSeed14Degree124.shared30, SharingSeed14Degree124.shared31, SharingSeed14Degree124.shared32, SharingSeed14Degree124.shared33, SharingSeed14Degree124.shared34, SharingSeed14Degree124.shared35, SharingSeed14Degree124.shared36, SharingSeed14Degree124.shared37, SharingSeed14Degree124.shared38, SharingSeed14Degree124.shared39, SharingSeed14Degree124.shared40, SharingSeed14Degree124.shared41, SharingSeed14Degree124.shared42, SharingSeed14Degree124.shared43, Sign14Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul,
    map_ofNat, hg]
end DiophantineConsistency.Sign14Transfers
#print axioms DiophantineConsistency.Sign14Transfers.Na_eval

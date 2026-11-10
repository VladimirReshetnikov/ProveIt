import DiophantineConsistency.SharingSign14Squares
import DiophantineConsistency.SharingSign15Squares

/-! SOURCE-ONLY supplied tau coordinate using an abstract signed expression. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} (v : Fin 15 → S) (gap : S) : Fin 16 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, gap]

def drop {S : Type*} (v : Fin 16 → S) : Fin 15 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14]

def oldD (p : Fin 4 → ℤ) : Expr (Fin 16) := SharingSeed15Degree124.row01 p

theorem old_d_row (p : Fin 4 → ℤ) :
    (SharingSeed15Degree124.remainingResiduals p).head? = some (oldD p) := by rfl

theorem d_zero (p : Fin 4 → ℤ) (v : Fin 15 → V) (gap : V)
    (hg : ι gap = (SharingSeed14Degree124.shared36 p).evalRing (fun j => ι (v j))) :
    InternalZero (oldD p) (lift v gap) := by
  rw [internalZero_iff]
  simp [oldD, SharingSeed15Degree124.row01, SharingSeed15Degree124.shared00, SharingSeed15Degree124.shared01, SharingSeed15Degree124.shared02, SharingSeed15Degree124.shared03, SharingSeed15Degree124.shared04, SharingSeed15Degree124.shared05, SharingSeed15Degree124.shared06, SharingSeed15Degree124.shared07, SharingSeed15Degree124.shared08, SharingSeed15Degree124.shared09, SharingSeed15Degree124.shared10, SharingSeed15Degree124.shared11, SharingSeed15Degree124.shared12, SharingSeed15Degree124.shared13, SharingSeed15Degree124.shared14, SharingSeed15Degree124.shared15, SharingSeed15Degree124.shared16, SharingSeed15Degree124.shared17, SharingSeed15Degree124.shared18, SharingSeed15Degree124.shared19, SharingSeed15Degree124.shared20, SharingSeed15Degree124.shared21, SharingSeed15Degree124.shared22, SharingSeed15Degree124.shared23, SharingSeed15Degree124.shared24, SharingSeed15Degree124.shared25, SharingSeed15Degree124.shared26, SharingSeed15Degree124.shared27, SharingSeed15Degree124.shared28, SharingSeed15Degree124.shared29, SharingSeed15Degree124.shared30, SharingSeed15Degree124.shared31, SharingSeed15Degree124.shared32, SharingSeed15Degree124.shared33, SharingSeed15Degree124.shared34, SharingSeed15Degree124.shared35, SharingSeed15Degree124.shared36, SharingSeed15Degree124.shared37, SharingSeed15Degree124.shared38, SharingSeed15Degree124.shared39, SharingSeed14Degree124.shared00, SharingSeed14Degree124.shared01, SharingSeed14Degree124.shared02, SharingSeed14Degree124.shared03, SharingSeed14Degree124.shared04, SharingSeed14Degree124.shared05, SharingSeed14Degree124.shared06, SharingSeed14Degree124.shared07, SharingSeed14Degree124.shared08, SharingSeed14Degree124.shared09, SharingSeed14Degree124.shared10, SharingSeed14Degree124.shared11, SharingSeed14Degree124.shared12, SharingSeed14Degree124.shared13, SharingSeed14Degree124.shared14, SharingSeed14Degree124.shared15, SharingSeed14Degree124.shared16, SharingSeed14Degree124.shared17, SharingSeed14Degree124.shared18, SharingSeed14Degree124.shared19, SharingSeed14Degree124.shared20, SharingSeed14Degree124.shared21, SharingSeed14Degree124.shared22, SharingSeed14Degree124.shared23, SharingSeed14Degree124.shared24, SharingSeed14Degree124.shared25, SharingSeed14Degree124.shared26, SharingSeed14Degree124.shared27, SharingSeed14Degree124.shared28, SharingSeed14Degree124.shared29, SharingSeed14Degree124.shared30, SharingSeed14Degree124.shared31, SharingSeed14Degree124.shared32, SharingSeed14Degree124.shared33, SharingSeed14Degree124.shared34, SharingSeed14Degree124.shared35, SharingSeed14Degree124.shared36, SharingSeed14Degree124.shared37, SharingSeed14Degree124.shared38, SharingSeed14Degree124.shared39, SharingSeed14Degree124.shared40, SharingSeed14Degree124.shared41, SharingSeed14Degree124.shared42, SharingSeed14Degree124.shared43, lift, Expr.evalRing_sub,
    Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, hg]

theorem lift_drop (v : Fin 16 → V) : lift (drop v) (v 15) = v := by
  funext j
  fin_cases j <;> simp [lift, drop]

theorem old_gap (p : Fin 4 → ℤ) (v : Fin 16 → V)
    (hz : InternalZero (SharingSeed15Degree124.seed p) v) :
    ι (v 15) = (SharingSeed14Degree124.shared36 p).evalRing (fun j => ι (drop v j)) := by
  have hm : oldD p ∈ SharingSeed15Degree124.firstResidual p :: SharingSeed15Degree124.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_head? (old_d_row p))
  have he := (internalZero_iff _ _).mp ((SharingSign15Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [oldD, SharingSeed15Degree124.row01, Expr.evalRing_sub, Expr.evalRing_add,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  have heq := sub_eq_zero.mp he
  simpa [SharingSeed15Degree124.shared00, SharingSeed15Degree124.shared01, SharingSeed15Degree124.shared02, SharingSeed15Degree124.shared03, SharingSeed15Degree124.shared04, SharingSeed15Degree124.shared05, SharingSeed15Degree124.shared06, SharingSeed15Degree124.shared07, SharingSeed15Degree124.shared08, SharingSeed15Degree124.shared09, SharingSeed15Degree124.shared10, SharingSeed15Degree124.shared11, SharingSeed15Degree124.shared12, SharingSeed15Degree124.shared13, SharingSeed15Degree124.shared14, SharingSeed15Degree124.shared15, SharingSeed15Degree124.shared16, SharingSeed15Degree124.shared17, SharingSeed15Degree124.shared18, SharingSeed15Degree124.shared19, SharingSeed15Degree124.shared20, SharingSeed15Degree124.shared21, SharingSeed15Degree124.shared22, SharingSeed15Degree124.shared23, SharingSeed15Degree124.shared24, SharingSeed15Degree124.shared25, SharingSeed15Degree124.shared26, SharingSeed15Degree124.shared27, SharingSeed15Degree124.shared28, SharingSeed15Degree124.shared29, SharingSeed15Degree124.shared30, SharingSeed15Degree124.shared31, SharingSeed15Degree124.shared32, SharingSeed15Degree124.shared33, SharingSeed15Degree124.shared34, SharingSeed15Degree124.shared35, SharingSeed15Degree124.shared36, SharingSeed15Degree124.shared37, SharingSeed15Degree124.shared38, SharingSeed15Degree124.shared39, SharingSeed14Degree124.shared00, SharingSeed14Degree124.shared01, SharingSeed14Degree124.shared02, SharingSeed14Degree124.shared03, SharingSeed14Degree124.shared04, SharingSeed14Degree124.shared05, SharingSeed14Degree124.shared06, SharingSeed14Degree124.shared07, SharingSeed14Degree124.shared08, SharingSeed14Degree124.shared09, SharingSeed14Degree124.shared10, SharingSeed14Degree124.shared11, SharingSeed14Degree124.shared12, SharingSeed14Degree124.shared13, SharingSeed14Degree124.shared14, SharingSeed14Degree124.shared15, SharingSeed14Degree124.shared16, SharingSeed14Degree124.shared17, SharingSeed14Degree124.shared18, SharingSeed14Degree124.shared19, SharingSeed14Degree124.shared20, SharingSeed14Degree124.shared21, SharingSeed14Degree124.shared22, SharingSeed14Degree124.shared23, SharingSeed14Degree124.shared24, SharingSeed14Degree124.shared25, SharingSeed14Degree124.shared26, SharingSeed14Degree124.shared27, SharingSeed14Degree124.shared28, SharingSeed14Degree124.shared29, SharingSeed14Degree124.shared30, SharingSeed14Degree124.shared31, SharingSeed14Degree124.shared32, SharingSeed14Degree124.shared33, SharingSeed14Degree124.shared34, SharingSeed14Degree124.shared35, SharingSeed14Degree124.shared36, SharingSeed14Degree124.shared37, SharingSeed14Degree124.shared38, SharingSeed14Degree124.shared39, SharingSeed14Degree124.shared40, SharingSeed14Degree124.shared41, SharingSeed14Degree124.shared42, SharingSeed14Degree124.shared43, drop, Expr.evalRing_sub, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant] using heq
end DiophantineConsistency.Sign14Coordinate
#print axioms DiophantineConsistency.Sign14Coordinate.old_d_row
#print axioms DiophantineConsistency.Sign14Coordinate.d_zero
#print axioms DiophantineConsistency.Sign14Coordinate.lift_drop
#print axioms DiophantineConsistency.Sign14Coordinate.old_gap

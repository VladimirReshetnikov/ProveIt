import DiophantineConsistency.SharingSign15Squares
import DiophantineConsistency.SharingSign16Squares

/-! SOURCE-ONLY conditional coordinate lift with abstract signed-inner value. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign15Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} (v : Fin 16 → S) (gap : S) : Fin 17 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, gap]

def drop {S : Type*} (v : Fin 17 → S) : Fin 16 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15]

def oldD (p : Fin 4 → ℤ) : Expr (Fin 17) := SharingSeed16Degree112.row04 p

theorem old_d_row (p : Fin 4 → ℤ) :
    ((SharingSeed16Degree112.remainingResiduals p).drop 3).head? = some (oldD p) := by rfl

theorem d_zero (p : Fin 4 → ℤ) (v : Fin 16 → V) (gap : V)
    (hg : ι gap = (SharingSeed15Degree124.shared31 p).evalRing (fun j => ι (v j))) :
    InternalZero (oldD p) (lift v gap) := by
  rw [internalZero_iff]
  simp [oldD, SharingSeed16Degree112.row04, SharingSeed16Degree112.shared00, SharingSeed16Degree112.shared01, SharingSeed16Degree112.shared02, SharingSeed16Degree112.shared03, SharingSeed16Degree112.shared04, SharingSeed16Degree112.shared05, SharingSeed16Degree112.shared06, SharingSeed16Degree112.shared07, SharingSeed16Degree112.shared08, SharingSeed16Degree112.shared09, SharingSeed16Degree112.shared10, SharingSeed16Degree112.shared11, SharingSeed16Degree112.shared12, SharingSeed16Degree112.shared13, SharingSeed16Degree112.shared14, SharingSeed16Degree112.shared15, SharingSeed16Degree112.shared16, SharingSeed16Degree112.shared17, SharingSeed16Degree112.shared18, SharingSeed16Degree112.shared19, SharingSeed16Degree112.shared20, SharingSeed16Degree112.shared21, SharingSeed16Degree112.shared22, SharingSeed16Degree112.shared23, SharingSeed16Degree112.shared24, SharingSeed16Degree112.shared25, SharingSeed16Degree112.shared26, SharingSeed16Degree112.shared27, SharingSeed16Degree112.shared28, SharingSeed16Degree112.shared29, SharingSeed16Degree112.shared30, SharingSeed16Degree112.shared31, SharingSeed16Degree112.shared32, SharingSeed16Degree112.shared33, SharingSeed16Degree112.shared34, SharingSeed16Degree112.shared35, SharingSeed16Degree112.shared36, SharingSeed15Degree124.shared00, SharingSeed15Degree124.shared01, SharingSeed15Degree124.shared02, SharingSeed15Degree124.shared03, SharingSeed15Degree124.shared04, SharingSeed15Degree124.shared05, SharingSeed15Degree124.shared06, SharingSeed15Degree124.shared07, SharingSeed15Degree124.shared08, SharingSeed15Degree124.shared09, SharingSeed15Degree124.shared10, SharingSeed15Degree124.shared11, SharingSeed15Degree124.shared12, SharingSeed15Degree124.shared13, SharingSeed15Degree124.shared14, SharingSeed15Degree124.shared15, SharingSeed15Degree124.shared16, SharingSeed15Degree124.shared17, SharingSeed15Degree124.shared18, SharingSeed15Degree124.shared19, SharingSeed15Degree124.shared20, SharingSeed15Degree124.shared21, SharingSeed15Degree124.shared22, SharingSeed15Degree124.shared23, SharingSeed15Degree124.shared24, SharingSeed15Degree124.shared25, SharingSeed15Degree124.shared26, SharingSeed15Degree124.shared27, SharingSeed15Degree124.shared28, SharingSeed15Degree124.shared29, SharingSeed15Degree124.shared30, SharingSeed15Degree124.shared31, SharingSeed15Degree124.shared32, SharingSeed15Degree124.shared33, SharingSeed15Degree124.shared34, SharingSeed15Degree124.shared35, SharingSeed15Degree124.shared36, SharingSeed15Degree124.shared37, SharingSeed15Degree124.shared38, SharingSeed15Degree124.shared39, lift, Expr.evalRing_sub,
    Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, hg]

theorem lift_drop (v : Fin 17 → V) : lift (drop v) (v 16) = v := by
  funext j
  fin_cases j <;> simp [lift, drop]

theorem old_gap (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (SharingSeed16Degree112.seed p) v) :
    ι (v 16) = (SharingSeed15Degree124.shared31 p).evalRing (fun j => ι (drop v j)) := by
  have hm : oldD p ∈ SharingSeed16Degree112.firstResidual p :: SharingSeed16Degree112.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (old_d_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign16Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [oldD, SharingSeed16Degree112.row04, Expr.evalRing_sub, Expr.evalRing_add,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  have heq := sub_eq_zero.mp he
  simpa [SharingSeed16Degree112.shared00, SharingSeed16Degree112.shared01, SharingSeed16Degree112.shared02, SharingSeed16Degree112.shared03, SharingSeed16Degree112.shared04, SharingSeed16Degree112.shared05, SharingSeed16Degree112.shared06, SharingSeed16Degree112.shared07, SharingSeed16Degree112.shared08, SharingSeed16Degree112.shared09, SharingSeed16Degree112.shared10, SharingSeed16Degree112.shared11, SharingSeed16Degree112.shared12, SharingSeed16Degree112.shared13, SharingSeed16Degree112.shared14, SharingSeed16Degree112.shared15, SharingSeed16Degree112.shared16, SharingSeed16Degree112.shared17, SharingSeed16Degree112.shared18, SharingSeed16Degree112.shared19, SharingSeed16Degree112.shared20, SharingSeed16Degree112.shared21, SharingSeed16Degree112.shared22, SharingSeed16Degree112.shared23, SharingSeed16Degree112.shared24, SharingSeed16Degree112.shared25, SharingSeed16Degree112.shared26, SharingSeed16Degree112.shared27, SharingSeed16Degree112.shared28, SharingSeed16Degree112.shared29, SharingSeed16Degree112.shared30, SharingSeed16Degree112.shared31, SharingSeed16Degree112.shared32, SharingSeed16Degree112.shared33, SharingSeed16Degree112.shared34, SharingSeed16Degree112.shared35, SharingSeed16Degree112.shared36, SharingSeed15Degree124.shared00, SharingSeed15Degree124.shared01, SharingSeed15Degree124.shared02, SharingSeed15Degree124.shared03, SharingSeed15Degree124.shared04, SharingSeed15Degree124.shared05, SharingSeed15Degree124.shared06, SharingSeed15Degree124.shared07, SharingSeed15Degree124.shared08, SharingSeed15Degree124.shared09, SharingSeed15Degree124.shared10, SharingSeed15Degree124.shared11, SharingSeed15Degree124.shared12, SharingSeed15Degree124.shared13, SharingSeed15Degree124.shared14, SharingSeed15Degree124.shared15, SharingSeed15Degree124.shared16, SharingSeed15Degree124.shared17, SharingSeed15Degree124.shared18, SharingSeed15Degree124.shared19, SharingSeed15Degree124.shared20, SharingSeed15Degree124.shared21, SharingSeed15Degree124.shared22, SharingSeed15Degree124.shared23, SharingSeed15Degree124.shared24, SharingSeed15Degree124.shared25, SharingSeed15Degree124.shared26, SharingSeed15Degree124.shared27, SharingSeed15Degree124.shared28, SharingSeed15Degree124.shared29, SharingSeed15Degree124.shared30, SharingSeed15Degree124.shared31, SharingSeed15Degree124.shared32, SharingSeed15Degree124.shared33, SharingSeed15Degree124.shared34, SharingSeed15Degree124.shared35, SharingSeed15Degree124.shared36, SharingSeed15Degree124.shared37, SharingSeed15Degree124.shared38, SharingSeed15Degree124.shared39, drop, Expr.evalRing_sub, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant] using heq
end DiophantineConsistency.Sign15Coordinate
#print axioms DiophantineConsistency.Sign15Coordinate.old_d_row
#print axioms DiophantineConsistency.Sign15Coordinate.d_zero
#print axioms DiophantineConsistency.Sign15Coordinate.lift_drop
#print axioms DiophantineConsistency.Sign15Coordinate.old_gap

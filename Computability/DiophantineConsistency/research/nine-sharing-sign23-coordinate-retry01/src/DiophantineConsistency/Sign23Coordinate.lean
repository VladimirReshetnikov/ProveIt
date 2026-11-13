import DiophantineConsistency.SharingSign23Squares
import DiophantineConsistency.SharingSign24Squares

/-! SOURCE-ONLY candidate: Delta lift and coordinate recovery. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [CommSemiring S] (v : Fin 24 → S) : Fin 25 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16, v 17, (v 16 + v 15) * (v 16 + v 15) + (4 * (v 16 + v 15) + 3),
    v 18, v 19, v 20, v 21, v 22, v 23]

def drop {S : Type*} (v : Fin 25 → S) : Fin 24 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16, v 17, v 19, v 20, v 21, v 22, v 23, v 24]

def oldDelta (p : Fin 4 → ℤ) : Expr (Fin 25) :=
  ((Expr.var 18) - ((((Expr.var 16) + (Expr.var 15)) * ((Expr.var 16) + (Expr.var 15))) +
    (((Expr.constant (4 : ℤ)) * ((Expr.var 16) + (Expr.var 15))) + (Expr.constant (3 : ℤ)))))

theorem old_delta_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 2).head? = some (oldDelta p) := by rfl

theorem delta_zero (p : Fin 4 → ℤ) (v : Fin 24 → V) :
    InternalZero (oldDelta p) (lift v) := by
  rw [internalZero_iff]
  simp [oldDelta, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

theorem delta_coordinate (p : Fin 4 → ℤ) (v : Fin 25 → V)
    (hz : InternalZero (SharingSeed24Octic.seed p) v) :
    v 18 = (v 16 + v 15) * (v 16 + v 15) + (4 * (v 16 + v 15) + 3) := by
  have hm : oldDelta p ∈ SharingSeed24Octic.firstResidual p :: SharingSeed24Octic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (old_delta_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign24Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [oldDelta, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant] at he
  apply ι_injective
  simp only [map_add, map_mul, map_ofNat]
  exact sub_eq_zero.mp he

theorem lift_drop (p : Fin 4 → ℤ) (v : Fin 25 → V)
    (hz : InternalZero (SharingSeed24Octic.seed p) v) : lift (drop v) = v := by
  have he := delta_coordinate p v hz
  funext j
  fin_cases j <;> simp [lift, drop, he]
end DiophantineConsistency.Sign23Coordinate
#print axioms DiophantineConsistency.Sign23Coordinate.old_delta_row
#print axioms DiophantineConsistency.Sign23Coordinate.delta_zero
#print axioms DiophantineConsistency.Sign23Coordinate.delta_coordinate
#print axioms DiophantineConsistency.Sign23Coordinate.lift_drop

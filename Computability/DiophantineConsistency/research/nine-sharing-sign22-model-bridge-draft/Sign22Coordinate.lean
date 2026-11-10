import DiophantineConsistency.SharingSign22Squares
import DiophantineConsistency.SharingSign23Squares

/-! SOURCE-ONLY candidate: kY lift and coordinate recovery. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [CommSemiring S] (v : Fin 23 → S) : Fin 24 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16, ((v 11 + 1) + (v 12 + 1)) * v 15, v 17, v 18, v 19, v 20, v 21, v 22]

def drop {S : Type*} (v : Fin 24 → S) : Fin 23 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16, v 18, v 19, v 20, v 21, v 22, v 23]

def oldkY (p : Fin 4 → ℤ) : Expr (Fin 24) :=
  ((Expr.var 17) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) +
    ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)))

theorem old_ky_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 1).head? = some (oldkY p) := by rfl

theorem ky_zero (p : Fin 4 → ℤ) (v : Fin 23 → V) :
    InternalZero (oldkY p) (lift v) := by
  rw [internalZero_iff]
  simp [oldkY, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]

theorem ky_coordinate (p : Fin 4 → ℤ) (v : Fin 24 → V)
    (hz : InternalZero (SharingSeed23Octic.seed p) v) :
    v 17 = ((v 11 + 1) + (v 12 + 1)) * v 15 := by
  have hm : oldkY p ∈ SharingSeed23Octic.firstResidual p :: SharingSeed23Octic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (old_ky_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign23Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [oldkY, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  exact sub_eq_zero.mp he

theorem lift_drop (p : Fin 4 → ℤ) (v : Fin 24 → V)
    (hz : InternalZero (SharingSeed23Octic.seed p) v) : lift (drop v) = v := by
  have he := ky_coordinate p v hz
  funext j
  fin_cases j <;> simp [lift, drop, he]
end DiophantineConsistency.Sign22Coordinate
#print axioms DiophantineConsistency.Sign22Coordinate.old_ky_row
#print axioms DiophantineConsistency.Sign22Coordinate.ky_zero
#print axioms DiophantineConsistency.Sign22Coordinate.ky_coordinate
#print axioms DiophantineConsistency.Sign22Coordinate.lift_drop

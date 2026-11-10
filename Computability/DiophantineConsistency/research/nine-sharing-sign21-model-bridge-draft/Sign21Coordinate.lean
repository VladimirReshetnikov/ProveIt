import DiophantineConsistency.SharingSign21Squares
import DiophantineConsistency.SharingSign22Squares

/-! SOURCE-ONLY candidate: normalized-S lift and coordinate recovery. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [CommSemiring S] (v : Fin 22 → S) : Fin 23 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16, v 17, v 18, v 19, v 20, (v 6 + 1) * (v 17 * (v 17 + 2)), v 21]

def drop {S : Type*} (v : Fin 23 → S) : Fin 22 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16, v 17, v 18, v 19, v 20, v 22]

def oldS (p : Fin 4 → ℤ) : Expr (Fin 23) :=
  ((Expr.var 21) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) *
    ((Expr.var 17) * ((Expr.var 17) + (Expr.constant (2 : ℤ))))))

theorem old_s_row (p : Fin 4 → ℤ) :
    ((SharingSeed22Dodecic.remainingResiduals p).drop 8).head? = some (oldS p) := by rfl

theorem s_zero (p : Fin 4 → ℤ) (v : Fin 22 → V) :
    InternalZero (oldS p) (lift v) := by
  rw [internalZero_iff]
  simp [oldS, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]

theorem s_coordinate (p : Fin 4 → ℤ) (v : Fin 23 → V)
    (hz : InternalZero (SharingSeed22Dodecic.seed p) v) :
    v 21 = (v 6 + 1) * (v 17 * (v 17 + 2)) := by
  have hm : oldS p ∈ SharingSeed22Dodecic.firstResidual p :: SharingSeed22Dodecic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (old_s_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign22Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [oldS, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  apply ι_injective
  simp only [map_add, map_mul, map_one, map_ofNat]
  exact sub_eq_zero.mp he

theorem lift_drop (p : Fin 4 → ℤ) (v : Fin 23 → V)
    (hz : InternalZero (SharingSeed22Dodecic.seed p) v) : lift (drop v) = v := by
  have he := s_coordinate p v hz
  funext j
  fin_cases j <;> simp [lift, drop, he]
end DiophantineConsistency.Sign21Coordinate
#print axioms DiophantineConsistency.Sign21Coordinate.old_s_row
#print axioms DiophantineConsistency.Sign21Coordinate.s_zero
#print axioms DiophantineConsistency.Sign21Coordinate.s_coordinate
#print axioms DiophantineConsistency.Sign21Coordinate.lift_drop

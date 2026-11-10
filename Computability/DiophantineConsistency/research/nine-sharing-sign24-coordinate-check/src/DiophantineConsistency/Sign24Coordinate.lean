import DiophantineConsistency.SharingSign24Squares
import DiophantineConsistency.SharingSign25Squares

/-! SOURCE-ONLY candidate: q3 lift and coordinate recovery. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [CommSemiring S] (beta : S) (v : Fin 25 → S) : Fin 26 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    (beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1),
    v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24]

def drop {S : Type*} (v : Fin 26 → S) : Fin 25 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25]

theorem q3_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    InternalZero (SharingSeed25Octic.firstResidual p) (lift beta v) := by
  rw [internalZero_iff]
  simp [SharingSeed25Octic.firstResidual, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

theorem q3_coordinate (p : Fin 4 → ℤ) (beta : V) (v : Fin 26 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed25Octic.seed p) v) :
    v 15 = (beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1) := by
  have hm : SharingSeed25Octic.firstResidual p ∈
      SharingSeed25Octic.firstResidual p :: SharingSeed25Octic.remainingResiduals p := by simp
  have he := (internalZero_iff _ _).mp ((SharingSign25Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [SharingSeed25Octic.firstResidual, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0] at he
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  exact sub_eq_zero.mp he

theorem lift_drop (p : Fin 4 → ℤ) (beta : V) (v : Fin 26 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed25Octic.seed p) v) : lift beta (drop v) = v := by
  have he := q3_coordinate p beta v hp0 hz
  funext j
  fin_cases j <;> simp [lift, drop, he]
end DiophantineConsistency.Sign24Coordinate
#print axioms DiophantineConsistency.Sign24Coordinate.q3_zero
#print axioms DiophantineConsistency.Sign24Coordinate.q3_coordinate
#print axioms DiophantineConsistency.Sign24Coordinate.lift_drop

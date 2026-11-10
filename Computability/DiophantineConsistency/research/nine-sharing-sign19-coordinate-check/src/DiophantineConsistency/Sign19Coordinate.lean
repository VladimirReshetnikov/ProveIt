import DiophantineConsistency.SharingSign19Squares
import DiophantineConsistency.SharingSign20Squares

/-! SOURCE-ONLY candidate: y lift and coordinate recovery. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign19Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [CommSemiring S] (beta : S) (v : Fin 20 → S) : Fin 21 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    (v 8 + 1) * ((beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1)),
    v 15, v 16, v 17, v 18, v 19]

def drop {S : Type*} (v : Fin 21 → S) : Fin 20 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 16, v 17, v 18, v 19, v 20]

theorem y_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    InternalZero (SharingSeed20Degree20.firstResidual p) (lift beta v) := by
  rw [internalZero_iff]
  simp [SharingSeed20Degree20.firstResidual, lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

theorem y_coordinate (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed20Degree20.seed p) v) :
    v 15 = (v 8 + 1) * ((beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1) * (beta * (v 1 + 1) + 1)) := by
  have hm : SharingSeed20Degree20.firstResidual p ∈
      SharingSeed20Degree20.firstResidual p :: SharingSeed20Degree20.remainingResiduals p := by simp
  have he := (internalZero_iff _ _).mp ((SharingSign20Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [SharingSeed20Degree20.firstResidual, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0] at he
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  exact sub_eq_zero.mp he

theorem lift_drop (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed20Degree20.seed p) v) : lift beta (drop v) = v := by
  have he := y_coordinate p beta v hp0 hz
  funext j
  fin_cases j <;> simp [lift, drop, he]
end DiophantineConsistency.Sign19Coordinate
#print axioms DiophantineConsistency.Sign19Coordinate.y_zero
#print axioms DiophantineConsistency.Sign19Coordinate.y_coordinate
#print axioms DiophantineConsistency.Sign19Coordinate.lift_drop

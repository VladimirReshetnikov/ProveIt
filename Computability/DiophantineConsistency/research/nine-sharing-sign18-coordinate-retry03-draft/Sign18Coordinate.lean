import DiophantineConsistency.SharingSign18Squares
import DiophantineConsistency.SharingSign19Squares

/-! SOURCE-ONLY candidate: positive main-root lift and coordinate recovery. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign18Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def rootValue {S : Type*} [CommSemiring S] (beta : S) (v : Fin 19 → S) : S :=
  (((((v 9) * ((beta * ((v 1) + 1)) + 1)) + (beta * ((v 1) + 1))) + ((((((v 9) + 1) * ((beta * ((v 1) + 1)) + 1)) * (((v 8) + 1) * ((((beta * ((v 1) + 1)) + 1) * ((beta * ((v 1) + 1)) + 1)) * ((beta * ((v 1) + 1)) + 1)))) + (((v 8) + 1) * ((((beta * ((v 1) + 1)) + 1) * ((beta * ((v 1) + 1)) + 1)) * ((beta * ((v 1) + 1)) + 1)))) * (((((v 11) + 1) + ((v 12) + 1)) * (((v 8) + 1) * ((((beta * ((v 1) + 1)) + 1) * ((beta * ((v 1) + 1)) + 1)) * ((beta * ((v 1) + 1)) + 1)))) + ((v 11) + 1)))) + (((v 14) + 1) * ((4 * (((((v 9) + 1) * ((beta * ((v 1) + 1)) + 1)) * (((v 8) + 1) * ((((beta * ((v 1) + 1)) + 1) * ((beta * ((v 1) + 1)) + 1)) * ((beta * ((v 1) + 1)) + 1)))) + (((v 8) + 1) * ((((beta * ((v 1) + 1)) + 1) * ((beta * ((v 1) + 1)) + 1)) * ((beta * ((v 1) + 1)) + 1))))) + 3)))

def lift {S : Type*} [CommSemiring S] (beta : S) (v : Fin 19 → S) : Fin 20 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    rootValue beta v, v 15, v 16, v 17, v 18]

def drop {S : Type*} (v : Fin 20 → S) : Fin 19 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 16, v 17, v 18, v 19]

theorem root_identity (q t b c : DiffRing V) :
    (q * (t + 1) + t + b + c) + 1 = ((q + 1) * (t + 1) + b) + c := by ring

theorem root_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 19 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    InternalZero (SharingSeed19Degree44.firstResidual p) (lift beta v) := by
  rw [internalZero_iff]
  simp [SharingSeed19Degree44.firstResidual, SharingSeed19Degree44.row00,
    lift, rootValue, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, map_add, map_mul, map_one, hp0]
  rw [root_identity]
  simp only [map_ofNat, _root_.sub_self]

theorem root_coordinate (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed19Degree44.seed p) v) :
    v 15 = rootValue beta (drop v) := by
  have hm : SharingSeed19Degree44.firstResidual p ∈
      SharingSeed19Degree44.firstResidual p :: SharingSeed19Degree44.remainingResiduals p := by simp
  have he := (internalZero_iff _ _).mp ((SharingSign19Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [SharingSeed19Degree44.firstResidual, SharingSeed19Degree44.row00,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one, hp0] at he
  have he' := sub_eq_zero.mp he
  rw [← root_identity] at he'
  apply ι_injective
  simpa [rootValue, drop, map_add, map_mul, map_ofNat] using (add_right_cancel he')

theorem lift_drop (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed19Degree44.seed p) v) : lift beta (drop v) = v := by
  have he := root_coordinate p beta v hp0 hz
  funext j
  fin_cases j <;> simp [lift, drop, he]
end DiophantineConsistency.Sign18Coordinate
#print axioms DiophantineConsistency.Sign18Coordinate.root_zero
#print axioms DiophantineConsistency.Sign18Coordinate.root_coordinate
#print axioms DiophantineConsistency.Sign18Coordinate.lift_drop

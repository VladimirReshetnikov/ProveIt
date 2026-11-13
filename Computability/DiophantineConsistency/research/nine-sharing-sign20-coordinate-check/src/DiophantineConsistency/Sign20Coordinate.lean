import DiophantineConsistency.SharingSign20Squares
import DiophantineConsistency.SharingSign21Squares

/-! SOURCE-ONLY candidate: E lift and coordinate recovery. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [CommSemiring S] (beta : S) (v : Fin 21 → S) : Fin 22 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, (v 9 + 1) * (beta * (v 1 + 1) + 1) * v 15, v 16, v 17, v 18, v 19, v 20]

def drop {S : Type*} (v : Fin 22 → S) : Fin 21 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 17, v 18, v 19, v 20, v 21]

def oldE (p : Fin 4 → ℤ) : Expr (Fin 22) :=
  (Expr.var 16) - (((Expr.var 9) + (Expr.constant (1 : ℤ))) *
    (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) +
      (Expr.constant (1 : ℤ))) * (Expr.var 15))

theorem old_e_row (p : Fin 4 → ℤ) :
    (SharingSeed21Degree14.remainingResiduals p).head? = some (oldE p) := by rfl

theorem e_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    InternalZero (oldE p) (lift beta v) := by
  rw [internalZero_iff]
  simp [oldE, lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]

theorem e_coordinate (p : Fin 4 → ℤ) (beta : V) (v : Fin 22 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed21Degree14.seed p) v) :
    v 16 = (v 9 + 1) * (beta * (v 1 + 1) + 1) * v 15 := by
  have hm : oldE p ∈ SharingSeed21Degree14.firstResidual p :: SharingSeed21Degree14.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_head? (old_e_row p))
  have he := (internalZero_iff _ _).mp ((SharingSign21Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [oldE, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0] at he
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  exact sub_eq_zero.mp he

theorem lift_drop (p : Fin 4 → ℤ) (beta : V) (v : Fin 22 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed21Degree14.seed p) v) : lift beta (drop v) = v := by
  have he := e_coordinate p beta v hp0 hz
  funext j
  fin_cases j <;> simp [lift, drop, he]
end DiophantineConsistency.Sign20Coordinate
#print axioms DiophantineConsistency.Sign20Coordinate.old_e_row
#print axioms DiophantineConsistency.Sign20Coordinate.e_zero
#print axioms DiophantineConsistency.Sign20Coordinate.e_coordinate
#print axioms DiophantineConsistency.Sign20Coordinate.lift_drop

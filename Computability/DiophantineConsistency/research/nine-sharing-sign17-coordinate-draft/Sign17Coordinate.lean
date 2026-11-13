import DiophantineConsistency.SharingSign17Squares
import DiophantineConsistency.SharingSign18Squares

/-! SOURCE-ONLY conditional signed-coordinate lift, without representative existence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} (v : Fin 18 → S) (gap : S) : Fin 19 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16, v 17, gap]

def drop {S : Type*} (v : Fin 19 → S) : Fin 18 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16, v 17]

def oldD (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  (Expr.var 18) - (((Expr.var 13 + Expr.constant (1 : ℤ)) * (Expr.var 13 + Expr.constant (1 : ℤ))) -
    ((Expr.var 17) * (Expr.var 17)))

theorem old_d_row (p : Fin 4 → ℤ) :
    ((SharingSeed18Degree94.remainingResiduals p).drop 5).head? = some (oldD p) := by rfl

theorem d_zero (p : Fin 4 → ℤ) (v : Fin 18 → V) (gap : V)
    (hg : ι gap = (ι (v 13) + 1) * (ι (v 13) + 1) - ι (v 17) * ι (v 17)) :
    InternalZero (oldD p) (lift v gap) := by
  rw [internalZero_iff]
  simp [oldD, lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, hg]

theorem old_gap (p : Fin 4 → ℤ) (v : Fin 19 → V)
    (hz : InternalZero (SharingSeed18Degree94.seed p) v) :
    ι (v 18) = (ι (v 13) + 1) * (ι (v 13) + 1) - ι (v 17) * ι (v 17) := by
  have hm : oldD p ∈ SharingSeed18Degree94.firstResidual p :: SharingSeed18Degree94.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (old_d_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign18Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [oldD, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  exact sub_eq_zero.mp he

theorem lift_drop (v : Fin 19 → V) : lift (drop v) (v 18) = v := by
  funext j
  fin_cases j <;> simp [lift, drop]
end DiophantineConsistency.Sign17Coordinate
#print axioms DiophantineConsistency.Sign17Coordinate.old_d_row
#print axioms DiophantineConsistency.Sign17Coordinate.d_zero
#print axioms DiophantineConsistency.Sign17Coordinate.old_gap
#print axioms DiophantineConsistency.Sign17Coordinate.lift_drop

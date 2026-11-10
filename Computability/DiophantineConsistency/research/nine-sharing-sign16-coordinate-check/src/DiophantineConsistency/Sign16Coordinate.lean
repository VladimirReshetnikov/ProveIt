import DiophantineConsistency.SharingSign16Squares
import DiophantineConsistency.SharingSign17Squares
import DiophantineConsistency.Sign16SharedValues

/-! SOURCE-ONLY conditional signed-coordinate lift and recovery. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16Coordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} (v : Fin 17 → S) (gap : S) : Fin 18 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16, gap]

def drop {S : Type*} (v : Fin 18 → S) : Fin 17 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14,
    v 15, v 16]

def oldD (p : Fin 4 → ℤ) : Expr (Fin 18) := SharingSeed17Degree96.row05 p

theorem old_d_row (p : Fin 4 → ℤ) :
    ((SharingSeed17Degree96.remainingResiduals p).drop 4).head? = some (oldD p) := by rfl

theorem old_c_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V) (gap : V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (SharingSeed17Degree96.shared17 p).evalRing (fun j => ι (lift v gap j)) = ι (C beta v) := by
  simp [SharingSeed17Degree96.shared17, SharingSeed17Degree96.shared16,
    SharingSeed17Degree96.shared13, SharingSeed17Degree96.shared12, SharingSeed17Degree96.shared08,
    Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var,
    lift, hp, Int.cast_one,
    C, Y, A, map_add, map_mul, map_one]

theorem d_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V) (gap : V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hg : ι gap = (ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16) - ι (C beta v)) :
    InternalZero (oldD p) (lift v gap) := by
  rw [internalZero_iff]
  simp only [oldD, SharingSeed17Degree96.row05, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]
  rw [old_c_eval p beta v gap hp]
  simp [lift, hg]

theorem lift_drop (v : Fin 18 → V) : lift (drop v) (v 17) = v := by
  funext j
  fin_cases j <;> simp [lift, drop]

theorem old_gap (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed17Degree96.seed p) v) :
    ι (v 17) = (ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16) - ι (C beta (drop v)) := by
  have hm : oldD p ∈ SharingSeed17Degree96.firstResidual p :: SharingSeed17Degree96.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (old_d_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign17Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  have hc := old_c_eval p beta (drop v) (v 17) hp
  rw [lift_drop] at hc
  simp only [oldD, SharingSeed17Degree96.row05, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hc] at he
  simpa [drop] using (sub_eq_zero.mp he)
end DiophantineConsistency.Sign16Coordinate
#print axioms DiophantineConsistency.Sign16Coordinate.old_d_row
#print axioms DiophantineConsistency.Sign16Coordinate.old_c_eval
#print axioms DiophantineConsistency.Sign16Coordinate.d_zero
#print axioms DiophantineConsistency.Sign16Coordinate.lift_drop
#print axioms DiophantineConsistency.Sign16Coordinate.old_gap

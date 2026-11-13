import DiophantineConsistency.SharingSign33Squares

/-! Same-valuation residual cuts Y, E and kY; no model port casts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualBatch01
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailResidual (p : Fin 4 → ℤ) (i : ℕ) : Expr (Fin 34) :=
  (SharingSeed33.remainingResiduals p).getD i 0

theorem row3_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 2).evalRing (fun j => ι (v j)) =
      ι (v 18)-(ι (v 8)+1)*ι (v 16) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem row4_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 3).evalRing (fun j => ι (v j)) =
      ι (v 19)-ι (v 17)*ι (v 18) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var]

theorem row5_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 4).evalRing (fun j => ι (v j)) =
      ι (v 20)-((ι (v 11)+1)+(ι (v 12)+1))*ι (v 18) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem three_cuts_of_seed_zero (p : Fin 4 → ℤ) (v : Fin 34 → V)
    (hz : InternalZero (SharingSeed33.seed p) v) :
    ι (v 18) = (ι (v 8)+1)*ι (v 16) ∧
    ι (v 19) = ι (v 17)*ι (v 18) ∧
    ι (v 20) = ((ι (v 11)+1)+(ι (v 12)+1))*ι (v 18) := by
  have hm3 : tailResidual p 2 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hm4 : tailResidual p 3 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hm5 : tailResidual p 4 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hres := (SharingSign33Squares.seed_zero_iff_residuals p v).mp hz
  have he3 := (internalZero_iff (tailResidual p 2) v).mp (hres _ hm3)
  have he4 := (internalZero_iff (tailResidual p 3) v).mp (hres _ hm4)
  have he5 := (internalZero_iff (tailResidual p 4) v).mp (hres _ hm5)
  rw [row3_eval p v] at he3
  rw [row4_eval p v] at he4
  rw [row5_eval p v] at he5
  exact ⟨sub_eq_zero.mp he3, sub_eq_zero.mp he4, sub_eq_zero.mp he5⟩
end DiophantineConsistency.Sign33ResidualBatch01
#print axioms DiophantineConsistency.Sign33ResidualBatch01.row3_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch01.row4_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch01.row5_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch01.three_cuts_of_seed_zero

import DiophantineConsistency.SharingSign33Squares

/-! Same-valuation residual cuts negative auxiliary cut and two final norms; no model port casts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualBatch07
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailResidual (p : Fin 4 → ℤ) (i : ℕ) : Expr (Fin 34) :=
  (SharingSeed33.remainingResiduals p).getD i 0

theorem row21_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 20).evalRing (fun k => ι (v k)) =
      ι (v 33)-((ι (v 13)+1)*(ι (v 13)+1)-ι (v 30)*ι (v 30)) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem row22_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 21).evalRing (fun k => ι (v k)) =
      ((ι (v 13)+1)*(ι (v 13)+1)-ι (v 32)*ι (v 33))-1 := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem row23_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 22).evalRing (fun k => ι (v k)) =
      (ι (v 22)*ι (v 28)-ι (v 32))-ι (v 22) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem cut_and_norms_of_seed_zero (p : Fin 4 → ℤ) (v : Fin 34 → V)
    (hz : InternalZero (SharingSeed33.seed p) v) :
    ι (v 33) = (ι (v 13)+1)*(ι (v 13)+1)-ι (v 30)*ι (v 30) ∧
    (ι (v 13)+1)*(ι (v 13)+1)-ι (v 32)*ι (v 33) = 1 ∧
    ι (v 22)*ι (v 28)-ι (v 32) = ι (v 22) := by
  have hm21 : tailResidual p 20 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hm22 : tailResidual p 21 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hm23 : tailResidual p 22 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hres := (SharingSign33Squares.seed_zero_iff_residuals p v).mp hz
  have he21 := (internalZero_iff (tailResidual p 20) v).mp (hres _ hm21)
  rw [row21_eval p v] at he21
  have he22 := (internalZero_iff (tailResidual p 21) v).mp (hres _ hm22)
  rw [row22_eval p v] at he22
  have he23 := (internalZero_iff (tailResidual p 22) v).mp (hres _ hm23)
  rw [row23_eval p v] at he23
  exact ⟨sub_eq_zero.mp he21, sub_eq_zero.mp he22, sub_eq_zero.mp he23⟩
end DiophantineConsistency.Sign33ResidualBatch07
#print axioms DiophantineConsistency.Sign33ResidualBatch07.row21_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch07.row22_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch07.row23_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch07.cut_and_norms_of_seed_zero

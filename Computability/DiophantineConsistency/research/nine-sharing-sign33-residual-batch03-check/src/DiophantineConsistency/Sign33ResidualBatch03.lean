import DiophantineConsistency.SharingSign33Squares

/-! Same-valuation residual cuts c², Delta*c² and first norm; no model port casts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualBatch03
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailResidual (p : Fin 4 → ℤ) (i : ℕ) : Expr (Fin 34) :=
  (SharingSeed33.remainingResiduals p).getD i 0

theorem row9_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 8).evalRing (fun k => ι (v k)) =
      ι (v 24)-(((ι (v 20)+(ι (v 11)+1))*(ι (v 20)+(ι (v 11)+1)))) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem row10_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 9).evalRing (fun k => ι (v k)) =
      ι (v 25)-(ι (v 22)*ι (v 24)) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem row11_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 10).evalRing (fun k => ι (v k)) =
      (ι (v 23)*ι (v 23)-ι (v 25))-1 := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem two_cuts_and_norm_of_seed_zero (p : Fin 4 → ℤ) (v : Fin 34 → V)
    (hz : InternalZero (SharingSeed33.seed p) v) :
    ι (v 24) = (ι (v 20)+(ι (v 11)+1))*(ι (v 20)+(ι (v 11)+1)) ∧
    ι (v 25) = ι (v 22)*ι (v 24) ∧
    ι (v 23)*ι (v 23)-ι (v 25) = 1 := by
  have hm9 : tailResidual p 8 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have hm10 : tailResidual p 9 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have hm11 : tailResidual p 10 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have he9 := (internalZero_iff (tailResidual p 8) v).mp (hres _ hm9)
  rw [row9_eval p v] at he9
  have he10 := (internalZero_iff (tailResidual p 9) v).mp (hres _ hm10)
  rw [row10_eval p v] at he10
  have he11 := (internalZero_iff (tailResidual p 10) v).mp (hres _ hm11)
  rw [row11_eval p v] at he11
  exact ⟨sub_eq_zero.mp he9, sub_eq_zero.mp he10, sub_eq_zero.mp he11⟩
end DiophantineConsistency.Sign33ResidualBatch03
#print axioms DiophantineConsistency.Sign33ResidualBatch03.row9_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch03.row10_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch03.row11_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch03.two_cuts_and_norm_of_seed_zero

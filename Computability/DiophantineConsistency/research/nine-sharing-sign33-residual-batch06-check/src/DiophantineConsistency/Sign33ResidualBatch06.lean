import DiophantineConsistency.SharingSign33Squares

/-! Same-valuation residual cuts V, normalized S and normalized S²; no model port casts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualBatch06
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailResidual (p : Fin 4 → ℤ) (i : ℕ) : Expr (Fin 34) :=
  (SharingSeed33.remainingResiduals p).getD i 0

theorem row18_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 17).evalRing (fun k => ι (v k)) =
      ι (v 30)-(ι (v 28)*ι (v 29)-(ι (v 20)+(ι (v 11)+1))) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem row19_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 18).evalRing (fun k => ι (v k)) =
      ι (v 31)-((ι (v 6)+1)*ι (v 25)) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem row20_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 19).evalRing (fun k => ι (v k)) =
      ι (v 32)-(ι (v 31)*ι (v 31)) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem three_cuts_of_seed_zero (p : Fin 4 → ℤ) (v : Fin 34 → V)
    (hz : InternalZero (SharingSeed33.seed p) v) :
    ι (v 30) = ι (v 28)*ι (v 29)-(ι (v 20)+(ι (v 11)+1)) ∧
    ι (v 31) = (ι (v 6)+1)*ι (v 25) ∧
    ι (v 32) = ι (v 31)*ι (v 31) := by
  have hm18 : tailResidual p 17 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have hm19 : tailResidual p 18 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have hm20 : tailResidual p 19 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have he18 := (internalZero_iff (tailResidual p 17) v).mp (hres _ hm18)
  rw [row18_eval p v] at he18
  have he19 := (internalZero_iff (tailResidual p 18) v).mp (hres _ hm19)
  rw [row19_eval p v] at he19
  have he20 := (internalZero_iff (tailResidual p 19) v).mp (hres _ hm20)
  rw [row20_eval p v] at he20
  exact ⟨sub_eq_zero.mp he18, sub_eq_zero.mp he19, sub_eq_zero.mp he20⟩
end DiophantineConsistency.Sign33ResidualBatch06
#print axioms DiophantineConsistency.Sign33ResidualBatch06.row18_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch06.row19_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch06.row20_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch06.three_cuts_of_seed_zero

import DiophantineConsistency.SharingSign33Squares

/-! Same-valuation residual cuts ell, Delta and main root; no model port casts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualBatch02
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailResidual (p : Fin 4 → ℤ) (i : ℕ) : Expr (Fin 34) :=
  (SharingSeed33.remainingResiduals p).getD i 0

theorem row6_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 5).evalRing (fun k => ι (v k)) =
      ι (v 21)-(ι (v 19)*ι (v 20)) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, Int.cast_ofNat]

theorem row7_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 6).evalRing (fun k => ι (v k)) =
      ι (v 22)-((ι (v 19)+ι (v 18))*(ι (v 19)+ι (v 18))+(4*(ι (v 19)+ι (v 18))+3)) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, Int.cast_ofNat]

theorem row8_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 7).evalRing (fun k => ι (v k)) =
      ι (v 23)-((ι (v 17)+((ι (v 19)+ι (v 18))*(ι (v 20)+(ι (v 11)+1))))+((ι (v 14)+1)*(4*(ι (v 19)+ι (v 18))+3))) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, Int.cast_ofNat]

theorem three_cuts_of_seed_zero (p : Fin 4 → ℤ) (v : Fin 34 → V)
    (hz : InternalZero (SharingSeed33.seed p) v) :
    ι (v 21) = ι (v 19)*ι (v 20) ∧
    ι (v 22) = (ι (v 19)+ι (v 18))*(ι (v 19)+ι (v 18))+(4*(ι (v 19)+ι (v 18))+3) ∧
    ι (v 23) = (ι (v 17)+((ι (v 19)+ι (v 18))*(ι (v 20)+(ι (v 11)+1))))+((ι (v 14)+1)*(4*(ι (v 19)+ι (v 18))+3)) := by
  have hm6 : tailResidual p 5 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hm7 : tailResidual p 6 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hm8 : tailResidual p 7 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have he6 := (internalZero_iff (tailResidual p 5) v).mp (hres _ hm6)
  rw [row6_eval p v] at he6
  have he7 := (internalZero_iff (tailResidual p 6) v).mp (hres _ hm7)
  rw [row7_eval p v] at he7
  have he8 := (internalZero_iff (tailResidual p 7) v).mp (hres _ hm8)
  rw [row8_eval p v] at he8
  exact ⟨sub_eq_zero.mp he6, sub_eq_zero.mp he7, sub_eq_zero.mp he8⟩
end DiophantineConsistency.Sign33ResidualBatch02
#print axioms DiophantineConsistency.Sign33ResidualBatch02.row6_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch02.row7_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch02.row8_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch02.three_cuts_of_seed_zero

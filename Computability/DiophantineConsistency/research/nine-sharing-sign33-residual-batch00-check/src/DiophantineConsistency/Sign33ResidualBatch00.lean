import DiophantineConsistency.Sign33FirstCut
import DiophantineConsistency.SharingSign33Squares

/-! First three same-valuation sign33 static cuts: q², q³ and X. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualBatch00
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (b : V) (v : Fin 34 → V) : DiffRing V := ι b*(ι (v 1)+1)+1

def tailResidual (p : Fin 4 → ℤ) (i : ℕ) : Expr (Fin 34) :=
  (SharingSeed33.remainingResiduals p).getD i 0

theorem row1_eval (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0)) :
    (tailResidual p 0).evalRing (fun j => ι (v j)) = ι (v 16)-ι (v 15)*q (ports 0) v := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_zero,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one, hp0, q]

theorem row2_eval (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0)) :
    (tailResidual p 1).evalRing (fun j => ι (v j)) = ι (v 17)-(ι (v 9)+1)*q (ports 0) v := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0, q]

theorem three_cuts_of_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hz : InternalZero (SharingSeed33.seed p) v) :
    ι (v 15) = q (ports 0) v*q (ports 0) v ∧
    ι (v 16) = ι (v 15)*q (ports 0) v ∧
    ι (v 17) = (ι (v 9)+1)*q (ports 0) v := by
  have h0 : ι (v 15) = q (ports 0) v*q (ports 0) v := by
    simpa only [q] using Sign33FirstCut.first_cut_of_seed_zero p ports v hp0 hz
  have hm1 : tailResidual p 0 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hm2 : tailResidual p 1 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have hres := (SharingSign33Squares.seed_zero_iff_residuals p v).mp hz
  have he1 := (internalZero_iff (tailResidual p 0) v).mp (hres _ hm1)
  have he2 := (internalZero_iff (tailResidual p 1) v).mp (hres _ hm2)
  rw [row1_eval p ports v hp0] at he1
  rw [row2_eval p ports v hp0] at he2
  exact ⟨h0, sub_eq_zero.mp he1, sub_eq_zero.mp he2⟩
end DiophantineConsistency.Sign33ResidualBatch00
#print axioms DiophantineConsistency.Sign33ResidualBatch00.row1_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch00.row2_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch00.three_cuts_of_seed_zero

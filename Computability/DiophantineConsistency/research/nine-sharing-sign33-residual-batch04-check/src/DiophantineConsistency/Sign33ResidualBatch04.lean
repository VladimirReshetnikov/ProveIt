import DiophantineConsistency.SharingSign33Squares

/-! Same-valuation residual cuts gap, tau and second norm; no model port casts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualBatch04
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailResidual (p : Fin 4 → ℤ) (i : ℕ) : Expr (Fin 34) :=
  (SharingSeed33.remainingResiduals p).getD i 0

def t (ports : Fin 4 → V) (v : Fin 34 → V) : DiffRing V :=
  ι (ports 0)*(ι (v 1)+1)

def q (ports : Fin 4 → V) (v : Fin 34 → V) : DiffRing V := t ports v+1

theorem row12_eval (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0)) :
    (tailResidual p 11).evalRing (fun k => ι (v k)) =
      ι (v 26)-((t ports v*(t ports v+1)+(ι (v 3)+1))-t ports v*(ι (v 2)+1)) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0, q, t]

theorem row13_eval (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3)) :
    (tailResidual p 12).evalRing (fun k => ι (v k)) =
      ι (v 27)-(((ι (v 19)*(ι (v 10)+1)+((ι (v 11)+1)+(ι (v 12)+1)))+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+q ports v*ι (ports 3))*(ι (v 1)+1))) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0, hp2, hp3, q, t]

theorem row14_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 13).evalRing (fun k => ι (v k)) =
      (ι (v 27)*ι (v 27)-ι (v 21)*(ι (v 21)+((ι (v 11)+1)+(ι (v 12)+1))))-1 := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem signed_cuts_and_norm_of_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3))
    (hz : InternalZero (SharingSeed33.seed p) v) :
    ι (v 26) = (t ports v*(t ports v+1)+(ι (v 3)+1))-t ports v*(ι (v 2)+1) ∧
    ι (v 27) = ((ι (v 19)*(ι (v 10)+1)+((ι (v 11)+1)+(ι (v 12)+1)))+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+q ports v*ι (ports 3))*(ι (v 1)+1)) ∧
    ι (v 27)*ι (v 27)-ι (v 21)*(ι (v 21)+((ι (v 11)+1)+(ι (v 12)+1))) = 1 := by
  have hm12 : tailResidual p 11 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have hm13 : tailResidual p 12 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have hm14 : tailResidual p 13 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have he12 := (internalZero_iff (tailResidual p 11) v).mp (hres _ hm12)
  rw [row12_eval p ports v hp0] at he12
  have he13 := (internalZero_iff (tailResidual p 12) v).mp (hres _ hm13)
  rw [row13_eval p ports v hp0 hp2 hp3] at he13
  have he14 := (internalZero_iff (tailResidual p 13) v).mp (hres _ hm14)
  rw [row14_eval p v] at he14
  exact ⟨sub_eq_zero.mp he12, sub_eq_zero.mp he13, sub_eq_zero.mp he14⟩
end DiophantineConsistency.Sign33ResidualBatch04
#print axioms DiophantineConsistency.Sign33ResidualBatch04.row12_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch04.row13_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch04.row14_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch04.signed_cuts_and_norm_of_seed_zero

import DiophantineConsistency.SharingSign33Squares

/-! Same-valuation residual cuts transport row, f² and cT-minus-r signed cut; explicit port casts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualBatch05
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tailResidual (p : Fin 4 → ℤ) (i : ℕ) : Expr (Fin 34) :=
  (SharingSeed33.remainingResiduals p).getD i 0

def t (ports : Fin 4 → V) (v : Fin 34 → V) : DiffRing V :=
  ι (ports 0)*(ι (v 1)+1)

def q (ports : Fin 4 → V) (v : Fin 34 → V) : DiffRing V := t ports v+1

theorem row15_eval (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι (ports 1)) :
    (tailResidual p 14).evalRing (fun k => ι (v k)) =
      ((((ι (ports 1)+(ι (v 9)+1))*q ports v)+q ports v)-((((ι (ports 1)+(ι (v 9)+1))*((ι (v 2)+1)+(ι (v 3)+1)))+(ι (v 2)+1))+((ι (v 4)+1)*t ports v)))-1 := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0, hp1, q, t]

theorem row16_eval (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    (tailResidual p 15).evalRing (fun k => ι (v k)) =
      ι (v 28)-(ι (v 5)+1)*(ι (v 5)+1) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]

theorem row17_eval (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3)) :
    (tailResidual p 16).evalRing (fun k => ι (v k)) =
      ι (v 29)-(((ι (v 20)+(ι (v 11)+1))*(ι (v 7)+1)+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+q ports v*ι (ports 3))*(ι (v 1)+1))) := by
  simp only [tailResidual, SharingSeed33.remainingResiduals, List.getD_cons_succ,
    List.getD_cons_zero, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0, hp2, hp3, q, t]

theorem transport_and_cuts_of_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι (ports 1))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3))
    (hz : InternalZero (SharingSeed33.seed p) v) :
    (((ι (ports 1)+(ι (v 9)+1))*q ports v)+q ports v)-((((ι (ports 1)+(ι (v 9)+1))*((ι (v 2)+1)+(ι (v 3)+1)))+(ι (v 2)+1))+((ι (v 4)+1)*t ports v)) = 1 ∧
    ι (v 28) = (ι (v 5)+1)*(ι (v 5)+1) ∧
    ι (v 29) = ((ι (v 20)+(ι (v 11)+1))*(ι (v 7)+1)+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+q ports v*ι (ports 3))*(ι (v 1)+1)) := by
  have hm15 : tailResidual p 14 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have hm16 : tailResidual p 15 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have hm17 : tailResidual p 16 ∈ SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p := by
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
  have he15 := (internalZero_iff (tailResidual p 14) v).mp (hres _ hm15)
  rw [row15_eval p ports v hp0 hp1] at he15
  have he16 := (internalZero_iff (tailResidual p 15) v).mp (hres _ hm16)
  rw [row16_eval p v] at he16
  have he17 := (internalZero_iff (tailResidual p 16) v).mp (hres _ hm17)
  rw [row17_eval p ports v hp0 hp2 hp3] at he17
  exact ⟨sub_eq_zero.mp he15, sub_eq_zero.mp he16, sub_eq_zero.mp he17⟩
end DiophantineConsistency.Sign33ResidualBatch05
#print axioms DiophantineConsistency.Sign33ResidualBatch05.row15_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch05.row16_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch05.row17_eval
#print axioms DiophantineConsistency.Sign33ResidualBatch05.transport_and_cuts_of_seed_zero

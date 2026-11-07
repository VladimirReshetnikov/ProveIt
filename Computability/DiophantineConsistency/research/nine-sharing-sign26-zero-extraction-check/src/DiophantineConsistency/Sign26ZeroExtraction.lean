import DiophantineConsistency.SharingSign26Squares

/-! SOURCE-ONLY: derive q3 and Nt ring equalities from sign26 seed zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26ZeroExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ntResidual (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))

theorem nt_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 9).head? = some (ntResidual p) := by rfl

theorem q3_eq (p : Fin 4 → ℤ) (v : Fin 27 → V)
    (hz : InternalZero (SharingSeed26Sextic.seed p) v) :
    ι (v 15) = (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) *
      (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) *
      (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) := by
  have he := (internalZero_iff _ _).mp ((SharingSign26Squares.seed_zero_iff_residuals p v).mp hz _ List.mem_cons_self)
  simp only [SharingSeed26Sextic.firstResidual, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  exact sub_eq_zero.mp he

theorem nt_eq (p : Fin 4 → ℤ) (v : Fin 27 → V)
    (hz : InternalZero (SharingSeed26Sextic.seed p) v) :
    (((p 1 : ℤ) : DiffRing V) + (ι (v 9) + 1)) *
        ((((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) - (ι (v 2) + 1) - (ι (v 3) + 1)) =
      (ι (v 2) + 1) + ι (v 4) * (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1)) := by
  have hm : ntResidual p ∈ SharingSeed26Sextic.firstResidual p :: SharingSeed26Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (nt_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign26Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [ntResidual, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  have hident :
      ((((p 1 : ℤ) : DiffRing V) + (ι (v 9) + 1)) * (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) +
        (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) -
        ((((p 1 : ℤ) : DiffRing V) + (ι (v 9) + 1)) * ((ι (v 2) + 1) + (ι (v 3) + 1)) +
          (ι (v 2) + 1) + (ι (v 4) + 1) * (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1))) - 1) =
      (((p 1 : ℤ) : DiffRing V) + (ι (v 9) + 1)) *
        ((((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) - (ι (v 2) + 1) - (ι (v 3) + 1)) -
        (ι (v 2) + 1) - ι (v 4) * (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1)) := by ring
  rw [hident] at he
  have h := (sub_eq_iff_eq_add).mp (sub_eq_zero.mp he)
  simpa only [add_comm] using h
end DiophantineConsistency.Sign26ZeroExtraction
#print axioms DiophantineConsistency.Sign26ZeroExtraction.nt_row
#print axioms DiophantineConsistency.Sign26ZeroExtraction.q3_eq
#print axioms DiophantineConsistency.Sign26ZeroExtraction.nt_eq

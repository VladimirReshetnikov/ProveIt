import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! Literal first and main adaptive scaled norms from the actual split zero.
Signed roots are represented by natural pairs. No quotient is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveFactorUnits2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Select the root in the literal `1+(root*root-rhs)` factor shape. -/
def rootTerm {σ : Type*} : Expr σ → Expr σ
  | .add _ (.sub (.mul z _) _) => z
  | _ => .constant 0

def rightTerm {σ : Type*} : Expr σ → Expr σ
  | .add _ (.sub _ rhs) => rhs
  | _ => .constant 0

theorem first_shape (p : Fin 4 → ℤ) :
    (factors p).1 = 1 + (rootTerm (factors p).1 * rootTerm (factors p).1 - rightTerm (factors p).1) := rfl

theorem main_shape (p : Fin 4 → ℤ) :
    (factors p).2.1 = 1 + (rootTerm (factors p).2.1 * rootTerm (factors p).2.1 - rightTerm (factors p).2.1) := rfl

private theorem square_magnitude (p : Pair V) :
    Equivalent (multiply p p) (natural (magnitude p*magnitude p)) := by
  wlog h : p.2 ≤ p.1 generalizing p
  · have hh := this (swap p) (le_of_not_ge h)
    rw [multiply_swap_left, multiply_swap_right, magnitude_swap] at hh
    simpa only [swap, Prod.eta] using hh
  let u := p.1-p.2
  have hu : p.1=p.2+u := by rw [add_comm,tsub_add_cancel_of_le h]
  rw [magnitude_of_add hu]
  change p.1*p.1+p.2*p.2+0=(p.1*p.2+p.2*p.1)+u*u
  rw [hu]; ring

/-- A positive signed unit of the displayed square-minus-right factor forces
an equality of its actual natural split, with no sign of the root assumed. -/
theorem unit_square_norm {σ : Type*} (z rhs : Expr σ) (v : σ → V)
    (hu : (pairEval (1+(z*z-rhs)) v).1 = (pairEval (1+(z*z-rhs)) v).2+1) :
    magnitude (pairEval z v)*magnitude (pairEval z v) + (pairEval rhs v).2 =
      (pairEval rhs v).1 := by
  have hp : Equivalent (multiply (pairEval z v) (pairEval z v)) (pairEval rhs v) := by
    have h : 1+((multiply (pairEval z v) (pairEval z v)).1+(pairEval rhs v).2) =
        1+((multiply (pairEval z v) (pairEval z v)).2+(pairEval rhs v).1) := by
      simpa [pairEval,Expr.splitNatural,NatExpr.evalSemiring,multiply,add_assoc,add_comm,add_left_comm]
        using hu
    exact add_left_cancel h
  have h := equivalent_trans (equivalent_symm (square_magnitude (pairEval z v))) hp
  simpa [Equivalent,natural] using h

/-- Both scaled equations follow from the actual arbitrary-port split zero. -/
theorem expressionAt_scaled_norms (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt p) v) :
    magnitude (pairEval (rootTerm (factors p).1) v)*magnitude (pairEval (rootTerm (factors p).1) v) +
        (pairEval (rightTerm (factors p).1) v).2 = (pairEval (rightTerm (factors p).1) v).1 ∧
    magnitude (pairEval (rootTerm (factors p).2.1) v)*magnitude (pairEval (rootTerm (factors p).2.1) v) +
        (pairEval (rightTerm (factors p).2.1) v).2 = (pairEval (rightTerm (factors p).2.1) v).1 := by
  obtain ⟨h0,h1,_,_⟩ := expressionAt_factor_units p v hz
  rw [first_shape p] at h0
  rw [main_shape p] at h1
  exact ⟨unit_square_norm _ _ _ h0,unit_square_norm _ _ _ h1⟩

end DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011

import DiophantineConsistency.AdaptiveGap85ShiftContext

/-! Transfer equivalent signed inputs through the exact 85 context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftContextEquiv
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveFirstRootFactor87Syntax ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveGap85Literal AdaptiveGap85ShiftContext AdaptiveGap85ShiftFirstInput
open AdaptiveGap85ShiftMainShift AdaptiveGap85ShiftAuxInput
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem subst_assoc {σ τ υ : Type*} (e : Expr σ) (f : σ → Expr τ) (g : τ → Expr υ) :
    (e.subst f).subst g=e.subst (fun i => (f i).subst g) := by
  induction e <;> simp_all [Expr.subst]

/-- Full literal equivalence follows from its three signed inputs and the
    coordinates outside those inputs. No zero or positivity is assumed. -/
theorem literal_equiv_of_inputs (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hcommon : ∀ i, ¬(i=2 ∨ i=5 ∨ i=8 ∨ i=12) → w i=v i)
    (hf : Equivalent (pairEval (firstInput (fun j => (p j:ℤ))) w)
      (pairEval (firstInput (fun j => (p j:ℤ))) v))
    (hm : Equivalent (pairEval (mainShift (fun j => (p j:ℤ))) w)
      (pairEval (mainShift (fun j => (p j:ℤ))) v))
    (ha : Equivalent (pairEval (auxiliaryInput (fun j => (p j:ℤ))) w)
      (pairEval (auxiliaryInput (fun j => (p j:ℤ))) v)) :
    Equivalent (pairEval (expressionAt85 (fun j => (p j:ℤ))) w)
      (pairEval (expressionAt85 (fun j => (p j:ℤ))) v) := by
  let port : Fin 4 → ℤ := fun j => (p j:ℤ)
  let val : Sum (Fin 13) (Fin 13) → V := Sum.elim w v
  let left : Fin 13 → Expr (Sum (Fin 13) (Fin 13)) := fun i => .var (Sum.inl i)
  let right : Fin 13 → Expr (Sum (Fin 13) (Fin 13)) := fun i => .var (Sum.inr i)
  have h (i : Option (Option (Option (Fin 13)))) :
      Equivalent (splitEval ((fill port i).subst left) val)
        (splitEval ((fill port i).subst right) val) := by
    cases i with
    | none =>
      change Equivalent (splitEval ((firstInput port).subst (fun j => .var (Sum.inl j))) val)
        (splitEval ((firstInput port).subst (fun j => .var (Sum.inr j))) val)
      rw [splitEval_subst_var,splitEval_subst_var]
      exact hf
    | some i =>
      cases i with
      | none =>
        change Equivalent (splitEval ((mainShift port).subst (fun j => .var (Sum.inl j))) val)
          (splitEval ((mainShift port).subst (fun j => .var (Sum.inr j))) val)
        rw [splitEval_subst_var,splitEval_subst_var]
        exact hm
      | some i =>
        cases i with
        | none =>
          change Equivalent (splitEval ((auxiliaryInput port).subst (fun j => .var (Sum.inl j))) val)
            (splitEval ((auxiliaryInput port).subst (fun j => .var (Sum.inr j))) val)
          rw [splitEval_subst_var,splitEval_subst_var]
          exact ha
        | some i =>
          by_cases hi : i=2 ∨ i=5 ∨ i=8 ∨ i=12
          · simp only [fill,hi,ite_true,Expr.subst]; exact equivalent_refl _
          · have hwi := hcommon i hi
            simp only [fill,hi,ite_false,left,right,Expr.subst,splitEval,Expr.splitNatural,
              NatExpr.evalSemiring,val,Sum.elim_inl,Sum.elim_inr,hwi]
            exact equivalent_refl _
  have he := splitEval_subst_equiv (AdaptiveGap85ShiftContext.contextAt port)
    (fun i => (fill port i).subst left) (fun i => (fill port i).subst right) val h
  rw [← subst_assoc, ← subst_assoc, literal_as_context,
    splitEval_subst_var, splitEval_subst_var] at he
  exact he
end DiophantineConsistency.AdaptiveGap85ShiftContextEquiv

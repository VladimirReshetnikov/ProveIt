import DiophantineConsistency.AdaptiveAQ35Maps
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ35Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift AdaptiveSquareWitnessDirect14
open AdaptiveAQ35Context AdaptiveAQ35Zeros AdaptiveAQ35Positive AdaptiveAQ35Maps AdaptiveAQ40Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem old_all {σ : Type*} (p : Fin 4 → ℤ) (f : Unit ⊕ Fin 35 → Expr σ) (v : σ → V)
    (hz : InternalZero ((oldSum p).subst f) v) :
    ∀ i : Fin 23, InternalZero ((residuals p i).subst f) v := by
  obtain ⟨h0, ht⟩ := (old_zero p f v).mp hz
  exact Fin.cases h0 ht

theorem project_inputs (p : Fin 4 → ℤ) (v : Fin 36 → V)
    (hz : InternalZero (AdaptiveAQ36Literal.literal p) v) :
    ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill i) (project v)) := by
  have ho : InternalZero ((oldSum p).subst oldFill) v := by rw [old_literal]; exact hz
  have hall := old_all p oldFill v ho
  intro i
  cases i with
  | inl i =>
    have hh := hall 4
    change InternalZero ((oldFill (.inl ())) - (newFill (.inl ())).subst (fun j => .var (oldRest j))) v at hh
    have he := (sub_zero_iff_equiv _ _ v).mp hh
    change Equivalent (splitEval (oldFill (.inl ())) v)
      (splitEval ((newFill (.inl ())).subst (fun j => .var (oldRest j))) v) at he
    rw [splitEval_subst_var] at he
    cases i
    exact he
  | inr i =>
    change Equivalent (natural (v (oldRest i))) (natural (v (oldRest i)))
    exact equivalent_refl _

theorem extend_inputs (v : Fin 35 → V) :
    ∀ i, Equivalent (splitEval (oldFill i) (extend v)) (splitEval (newFill i) v) := by
  intro i
  cases i with
  | inl i =>
    cases i
    have hr : SignedRep (newFill (.inl ())) v (natural (squareValue v)) :=
      rawSquare_rep ((.var 26 - .var 27) : Expr (Fin 35)) v
    change Equivalent (natural (squareValue v)) (splitEval (newFill (.inl ())) v)
    exact equivalent_symm hr
  | inr i =>
    change Equivalent (natural (extend v (oldRest i))) (natural (v i))
    rw [extend_rest]
    exact equivalent_refl _
#print axioms project_inputs
#print axioms extend_inputs
end DiophantineConsistency.AdaptiveAQ35Transport

import DiophantineConsistency.AdaptiveAQ36Zeros
import DiophantineConsistency.AdaptiveAQ36Maps
import DiophantineConsistency.AdaptiveAQ36Literal
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ36Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift AdaptiveSquareWitnessDirect14
open AdaptiveAQ36Context AdaptiveAQ36Maps AdaptiveAQ36Zeros AdaptiveAQ40Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem old_all {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 4 ⊕ Fin 36 → Expr σ) (v : σ → V)
    (hz : InternalZero ((oldSum p).subst f) v) :
    ∀ i : Fin 27, InternalZero ((residuals p i).subst f) v := by
  obtain ⟨h0, ht⟩ := (old_zero p f v).mp hz
  exact Fin.cases h0 ht

theorem project_inputs (p : Fin 4 → ℤ) (v : Fin 40 → V)
    (hz : InternalZero (AdaptiveAQ40Literal.literal p) v) :
    ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill p i) (project v)) := by
  have ho : InternalZero ((oldSum p).subst oldFill) v := by rw [old_literal]; exact hz
  have hall := old_all p oldFill v ho
  intro i
  cases i with
  | inl i =>
    fin_cases i
    · have hh := hall 11
      change InternalZero ((oldFill (.inl 0)) - (newFill p (.inl 0)).subst (fun j => .var (oldRest j))) v at hh
      have he := (sub_zero_iff_equiv _ _ v).mp hh
      change Equivalent (splitEval (oldFill (.inl 0)) v)
        (splitEval ((newFill p (.inl 0)).subst (fun j => .var (oldRest j))) v) at he
      rw [splitEval_subst_var] at he
      exact he
    · have hh := hall 12
      change InternalZero ((oldFill (.inl 1)) - (newFill p (.inl 1)).subst (fun j => .var (oldRest j))) v at hh
      have he := (sub_zero_iff_equiv _ _ v).mp hh
      change Equivalent (splitEval (oldFill (.inl 1)) v)
        (splitEval ((newFill p (.inl 1)).subst (fun j => .var (oldRest j))) v) at he
      rw [splitEval_subst_var] at he
      exact he
    · have hh := hall 21
      change InternalZero ((oldFill (.inl 2)) - (newFill p (.inl 2)).subst (fun j => .var (oldRest j))) v at hh
      have he := (sub_zero_iff_equiv _ _ v).mp hh
      change Equivalent (splitEval (oldFill (.inl 2)) v)
        (splitEval ((newFill p (.inl 2)).subst (fun j => .var (oldRest j))) v) at he
      rw [splitEval_subst_var] at he
      exact he
    · have hh := hall 25
      change InternalZero ((oldFill (.inl 3)) - (newFill p (.inl 3)).subst (fun j => .var (oldRest j))) v at hh
      have he := (sub_zero_iff_equiv _ _ v).mp hh
      change Equivalent (splitEval (oldFill (.inl 3)) v)
        (splitEval ((newFill p (.inl 3)).subst (fun j => .var (oldRest j))) v) at he
      rw [splitEval_subst_var] at he
      exact he
  | inr i =>
    change Equivalent (natural (v (oldRest i))) (natural (v (oldRest i)))
    exact equivalent_refl _

theorem extend_inputs (p : Fin 4 → ℤ) (b : ℕ) (hb : p 0 = (b : ℤ)) (v : Fin 36 → V) :
    ∀ i, Equivalent (splitEval (oldFill i) (extend b v)) (splitEval (newFill p i) v) := by
  intro i
  cases i with
  | inl i =>
    fin_cases i
    · have hr : SignedRep (newFill p (.inl 0)) v (natural (qvalue b v * v 30)) := by
        change SignedRep (Expr.mul (Expr.add (Expr.constant 1) (Expr.mul (.var 0) (.constant (p 0)))) (.var 30) : Expr (Fin 36)) v _
        rw [hb]
        have h := rep_mul_nat (rep_add_nat (rep_one v) (rep_mul_nat (rep_var v 0) (rep_nat v b))) (rep_var v 30)
        change SignedRep (Expr.mul (Expr.add (Expr.constant 1) (Expr.mul (.var 0) (.constant (b : ℤ)))) (.var 30) : Expr (Fin 36)) v (natural ((1 + v 0 * (b : V)) * v 30)) at h
        rw [mul_comm (v 0) (b : V)] at h
        exact h
      change Equivalent (natural (qvalue b v * v 30)) (splitEval (newFill p (.inl 0)) v)
      exact equivalent_symm hr
    · have hr : SignedRep (newFill p (.inl 1)) v (natural (v 31 * qvalue b v)) := by
        change SignedRep (Expr.mul (.var 31) (Expr.add (Expr.constant 1) (Expr.mul (.var 0) (.constant (p 0)))) : Expr (Fin 36)) v _
        rw [hb]
        have h := rep_mul_nat (rep_var v 31) (rep_add_nat (rep_one v) (rep_mul_nat (rep_var v 0) (rep_nat v b)))
        change SignedRep (Expr.mul (.var 31) (Expr.add (Expr.constant 1) (Expr.mul (.var 0) (.constant (b : ℤ)))) : Expr (Fin 36)) v (natural (v 31 * (1 + v 0 * (b : V)))) at h
        rw [mul_comm (v 0) (b : V)] at h
        exact h
      change Equivalent (natural (v 31 * qvalue b v)) (splitEval (newFill p (.inl 1)) v)
      exact equivalent_symm hr
    · have hr : SignedRep (newFill p (.inl 2)) v (natural (v 14 * v 14)) :=
        rep_mul_nat (rep_var v 14) (rep_var v 14)
      change Equivalent (natural (v 14 * v 14)) (splitEval (newFill p (.inl 2)) v)
      exact equivalent_symm hr
    · have hr : SignedRep (newFill p (.inl 3)) v (natural (v 11 * v 11)) :=
        rep_mul_nat (rep_var v 11) (rep_var v 11)
      change Equivalent (natural (v 11 * v 11)) (splitEval (newFill p (.inl 3)) v)
      exact equivalent_symm hr
  | inr i =>
    change Equivalent (natural (extend b v (oldRest i))) (natural (v i))
    rw [extend_rest]
    exact equivalent_refl _
#print axioms project_inputs
#print axioms extend_inputs
end DiophantineConsistency.AdaptiveAQ36Transport

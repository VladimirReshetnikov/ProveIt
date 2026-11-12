import ConciseIPRA.NativeLogic
import ConciseIPRA.Scalar

/-!
# Translation of `T_eq` into the native scalar core

`NFm.ofFm` reads a first-order formula over the iterator terms as a native
formula, replacing every connective by its native abbreviation.  The main
result `NPrf.ofPrf` translates derivations: whatever `T_eq` proves, the native
calculus proves of the translations.

The logical rules are the derived rules of `ConciseIPRA.NativeLogic`.  The
axioms of `T_eq` are derived natively: the iterator equations are rules,
coverage is proof by numerical cases, separation is the identity on `0 = 1`,
and equation induction is the progress form of `D`-introduction.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter one)

variable {n m k : ℕ}

namespace NFm

/-- The native reading of a first-order formula. -/
def ofFm : {n : ℕ} → Fm Tm n → NFm n
  | _, .eq s t => eq s t
  | _, .bot => bot
  | _, .and φ ψ => and (ofFm φ) (ofFm ψ)
  | _, .or φ ψ => or (ofFm φ) (ofFm ψ)
  | _, .imp φ ψ => imp (ofFm φ) (ofFm ψ)
  | _, .all φ => all (ofFm φ)
  | _, .ex φ => ex (ofFm φ)

@[simp] theorem ofFm_and (φ ψ : Fm Tm n) : ofFm (φ ⋏ ψ) = and (ofFm φ) (ofFm ψ) := rfl
@[simp] theorem ofFm_or (φ ψ : Fm Tm n) : ofFm (φ ⋎ ψ) = or (ofFm φ) (ofFm ψ) := rfl
@[simp] theorem ofFm_imp (φ ψ : Fm Tm n) : ofFm (φ ⟶ ψ) = imp (ofFm φ) (ofFm ψ) := rfl
@[simp] theorem ofFm_all (φ : Fm Tm (n + 1)) : ofFm (Fm.all φ) = all (ofFm φ) := rfl
@[simp] theorem ofFm_ex (φ : Fm Tm (n + 1)) : ofFm (Fm.ex φ) = ex (ofFm φ) := rfl

/-- The native reading commutes with substitution. -/
theorem ofFm_subst (φ : Fm Tm n) :
    ∀ {m : ℕ} (σ : Fin n → Tm m), ofFm (φ.subst σ) = (ofFm φ).subst σ := by
  induction φ with intro m σ
  | eq s t => rfl
  | bot => rfl
  | and φ ψ ih₁ ih₂ => simp only [Fm.subst_and, ofFm_and, ih₁, ih₂, NFm.and_subst]
  | or φ ψ ih₁ ih₂ => simp only [Fm.subst_or, ofFm_or, ih₁, ih₂, NFm.or_subst]
  | imp φ ψ ih₁ ih₂ => simp only [Fm.subst_imp, ofFm_imp, ih₁, ih₂, NFm.imp_subst]
  | all φ ih => simp only [Fm.subst_all, ofFm_all, ih, NFm.all_subst]
  | ex φ ih => simp only [Fm.subst_ex, ofFm_ex, ih, NFm.ex_subst]

theorem ofFm_shift (φ : Fm Tm n) : ofFm φ.shift = (ofFm φ).shift := ofFm_subst φ _

theorem map_ofFm_shift (Γ : List (Fm Tm n)) :
    (Γ.map Fm.shift).map ofFm = (Γ.map ofFm).map NFm.shift := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih => simp only [List.map_cons, ih, ofFm_shift]

end NFm

namespace NPrf

variable {Γ : List (NFm n)}

/-- A universal statement moved under a fresh variable holds of that variable. -/
theorem allVar {A : NFm (n + 1)} {Δ : List (NFm (n + 1))} (h : NPrf Δ (NFm.all A).shift) :
    NPrf Δ A := by
  rw [NFm.shift, NFm.all_subst] at h
  simpa only [NFm.subst_up_inst_var] using allE (Syn.var 0) h

/-- Coverage: every number is zero or a successor. -/
theorem coverN (t : Tm n) :
    NPrf Γ (NFm.or (.eq t zero) (NFm.ex (.eq (Syn.shift t) (succ (Syn.var 0))))) := by
  have h := cases (Γ := Γ)
    (NFm.or (.eq (Syn.var 0) zero)
      (NFm.ex (.eq (Syn.shift (Syn.var 0)) (succ (Syn.var 0))))) t
    (by
      simp only [NFm.or_subst, NFm.subst_eq, Syn.subst_var, Syn.inst_zero, Tm.subst_zero]
      exact orI₁ (eqRefl zero))
    (by
      simp only [NFm.or_subst, NFm.ex_subst, NFm.subst_eq, Syn.subst_var, Syn.repl_zero,
        Tm.subst_zero, Tm.subst_succ, Syn.subst_up_shift, Syn.up_zero]
      refine orI₂ (exI (Syn.var 0) ?_)
      simp only [NFm.subst_eq, Syn.subst_inst_shift, Tm.subst_succ, Syn.subst_var,
        Syn.inst_zero]
      exact eqRefl _)
  simp only [NFm.or_subst, NFm.ex_subst, NFm.subst_eq, Syn.subst_var, Syn.inst_zero,
    Tm.subst_zero, Tm.subst_succ, Syn.subst_up_shift, Syn.up_zero] at h
  exact h

/-- Induction for a literal equation, in the form of the axiom of `T_eq`. -/
theorem indN (s t : Tm (n + 1)) :
    NPrf Γ (NFm.imp ((NFm.eq s t).subst (inst zero))
      (NFm.imp
        (NFm.all (NFm.imp (.eq s t) ((NFm.eq s t).subst (repl (succ (Syn.var 0))))))
        (NFm.all (.eq s t)))) := by
  refine impI (impI ?_)
  have hX : NPrf (NFm.eq s t ::
        (NFm.all (NFm.imp (.eq s t) ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) ::
          (NFm.eq s t).subst (inst zero) :: Γ).map NFm.shift)
      (NFm.all (NFm.imp (.eq s t) ((NFm.eq s t).subst (repl (succ (Syn.var 0)))))).shift :=
    .hyp (List.mem_cons_of_mem _ (List.mem_map_of_mem List.mem_cons_self))
  show NPrf _ (NFm.and ((NFm.eq s t).subst (inst zero)) (.Q (.eq s t)))
  exact andI (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))
    (qIProg s t (impE (allVar hX) hyp0))

/-- Every axiom of `T_eq` is derivable in the native calculus. -/
theorem ofAx {φ : Fm Tm k} (h : TeqAx k φ) : ∀ {Γ : List (NFm k)}, NPrf Γ (NFm.ofFm φ) := by
  cases h with intro Γ
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | cover =>
    have h := coverN (Γ := Γ) (Syn.var 0)
    rwa [Syn.shift_var] at h
  | sep => exact impI hyp0
  | ind s t => exact indN s t

/-- Translation of derivations: `T_eq` is interpreted in the native scalar
core by the native reading of formulas. -/
theorem ofPrf {Γ : List (Fm Tm n)} {φ : Fm Tm n} (h : Γ ⊢[TeqAx] φ) :
    NPrf (Γ.map NFm.ofFm) (NFm.ofFm φ) := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | ax h σ =>
    rw [NFm.ofFm_subst]
    exact ((ofAx h (Γ := [])).subst σ).ofNil
  | botE φ _ ih => exact botE _ ih
  | andI _ _ ih₁ ih₂ => exact andI ih₁ ih₂
  | andE₁ _ ih => exact andE₁ ih
  | andE₂ _ ih => exact andE₂ ih
  | orI₁ _ ih => exact orI₁ ih
  | orI₂ _ ih => exact orI₂ ih
  | orE _ _ _ ih ih₁ ih₂ => exact orE ih ih₁ ih₂
  | impI _ ih => exact impI ih
  | impE _ _ ih₁ ih₂ => exact impE ih₁ ih₂
  | allI _ ih =>
    rw [NFm.map_ofFm_shift] at ih
    exact allI ih
  | allE t _ ih =>
    rw [NFm.ofFm_subst]
    exact allE t ih
  | exI t _ ih =>
    rw [NFm.ofFm_subst] at ih
    exact exI t ih
  | exE _ _ ih₁ ih₂ =>
    rw [List.map_cons, NFm.map_ofFm_shift, NFm.ofFm_shift] at ih₂
    exact exE ih₁ ih₂
  | eqRefl t => exact eqRefl t
  | eqSubst φ σ σ' _ _ ih₁ ih₂ =>
    rw [NFm.ofFm_subst] at ih₂ ⊢
    exact leibniz _ σ σ' ih₁ ih₂

end NPrf

end LeanProofs.ConciseIPRA

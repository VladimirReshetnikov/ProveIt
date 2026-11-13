import ConciseIPRA.Term
import ConciseIPRA.Deduction

/-!
# The scalar equational theory `T_eq`

`T_eq` is the ordinary first-order realization of the native scalar core: the
iterator terms of `ConciseIPRA.Term` under intuitionistic logic with equality,
with

* the two computation equations of the iterator,
* numerical coverage `x = 0 ∨ ∃ y, x = S y`,
* separation `0 = S 0 → ⊥`, and
* induction for literal equations only.

Successor injectivity, `S x ≠ 0` in general, and induction for compound
formulas are not axioms.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter one)

/-- The axioms of `T_eq`. -/
inductive TeqAx : Theory Tm
  | iterZero {n : ℕ} (a : Tm n) (h : Tm (n + 1)) : TeqAx n (iter zero a h ≐ a)
  | iterSucc {n : ℕ} (c a : Tm n) (h : Tm (n + 1)) :
      TeqAx n (iter (succ c) a h ≐ Syn.subst (inst (iter c a h)) h)
  | cover : TeqAx 1 ((var 0 ≐ zero) ⋎ Fm.ex (var 1 ≐ succ (var 0)))
  | sep : TeqAx 0 ((zero ≐ succ zero) ⟶ Fm.bot)
  | ind {n : ℕ} (s t : Tm (n + 1)) :
      TeqAx n ((s ≐ t).subst (inst zero) ⟶
        Fm.all ((s ≐ t) ⟶ (s ≐ t).subst (repl (succ (var 0)))) ⟶ Fm.all (s ≐ t))

namespace Teq

variable {n : ℕ} {Γ : List (Fm Tm n)}

theorem iterZero (a : Tm n) (h : Tm (n + 1)) : Γ ⊢[TeqAx] iter zero a h ≐ a :=
  .axm (.iterZero a h)

theorem iterSucc (c a : Tm n) (h : Tm (n + 1)) :
    Γ ⊢[TeqAx] iter (succ c) a h ≐ Syn.subst (inst (iter c a h)) h :=
  .axm (.iterSucc c a h)

/-- Coverage at an arbitrary term. -/
theorem cover (t : Tm n) :
    Γ ⊢[TeqAx] (t ≐ zero) ⋎ Fm.ex (Syn.shift t ≐ succ (var 0)) := by
  simpa using Prf.ax (Γ := Γ) TeqAx.cover (fun _ => t)

theorem sep : Γ ⊢[TeqAx] (zero ≐ succ zero) ⟶ Fm.bot := by
  simpa using Prf.ax (Γ := Γ) TeqAx.sep Fin.elim0

/-- Case distinction on a term, with an unshifted conclusion. -/
theorem casesOn (t : Tm n) {ψ : Fm Tm n}
    (h0 : (t ≐ zero) :: Γ ⊢[TeqAx] ψ)
    (hS : (Syn.shift t ≐ succ (var 0)) :: Γ.map Fm.shift ⊢[TeqAx] ψ.shift) :
    Γ ⊢[TeqAx] ψ :=
  .orE (cover t) h0 (.exE Prf.hyp0 (hS.weaken (List.cons_subset_cons _ (by simp))))

/-- Proof by cases on a number: `φ(0)` and `φ(S z)` for a fresh `z` give
`∀ y, φ(y)`.  Only coverage is used. -/
theorem caseAll (φ : Fm Tm (n + 1)) (h0 : Γ ⊢[TeqAx] φ.subst (inst zero))
    (hS : Γ.map Fm.shift ⊢[TeqAx] φ.subst (repl (succ (var 0)))) :
    Γ ⊢[TeqAx] Fm.all φ := by
  refine .allI (casesOn (var 0) ?_ ?_)
  · have key : (var 0 ≐ zero) :: Γ.map Fm.shift ⊢[TeqAx] φ.subst var := by
      refine .eqSubst φ (fun i => Syn.shift (inst zero i)) var
        (fun i => Fin.cases (Prf.eqSymm Prf.hyp0) (fun _ => Prf.eqRefl _) i) ?_
      rw [← Fm.shift_subst]; exact h0.shift.wk
    rwa [Fm.subst_id] at key
  · have h1 := hS.subst (up (fun i => (var i.succ : Tm (n + 1))))
    rw [Fm.map_shift_subst, Fm.subst_subst] at h1
    exact .eqSubst φ _ (fun i => var i.succ)
      (fun i => Fin.cases (Prf.eqSymm Prf.hyp0) (fun _ => Prf.eqRefl _) i) h1.wk

/-- Induction for a literal equation. -/
theorem eqInd (s t : Tm (n + 1)) (h0 : Γ ⊢[TeqAx] (s ≐ t).subst (inst zero))
    (hS : (s ≐ t) :: Γ.map Fm.shift ⊢[TeqAx] (s ≐ t).subst (repl (succ (var 0)))) :
    Γ ⊢[TeqAx] Fm.all (s ≐ t) :=
  .impE (.impE (.axm (.ind s t)) h0) (.allI (.impI hS))

end Teq

end LeanProofs.ConciseIPRA

import ConciseIPRA.PRAToScalar
import ConciseIPRA.ScalarToPRA

/-!
# The round trip `T_eq → iPRA → T_eq`

The translation `tau` of `T_eq` into `iPRA` turns an iterator into the function
symbol `prec a (stepSym h)`, and the translation `sigma` back turns that symbol
into the term `prc c a (itG h)`: a primitive recursion whose step ignores the
counter.  One equation induction shows that such a recursion is the iterator,

  `prc c a (itG h) = I(c, a; u. h)`,

and a second one that the iterator respects provable equality of its body.
Hence `T_eq ⊢ sigma (tau t) = t` for every term `t`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- The step of a recursion that ignores its counter: the body of an iterator,
read with the previous value in the second bound variable. -/
def Tm.itG (h : Tm (n + 1)) : Tm (n + 2) :=
  Syn.subst (Fin.cases (Syn.var 1) (fun l => Syn.var l.succ.succ)) h

theorem Tm.subst_itG (σ : Fin n → Tm m) (h : Tm (n + 1)) :
    Syn.subst (up (up σ)) (Tm.itG h) = Tm.itG (Syn.subst (up σ) h) := by
  unfold Tm.itG
  rw [subst_subst, subst_subst]
  refine congrArg (fun ρ => Syn.subst ρ h) (funext (Fin.cases ?_ fun l => ?_))
  · simp
  · simp only [Fin.cases_succ, Syn.subst_var, Syn.up_succ]
    rw [subst_shift]
    simp only [Fin.cases_succ, shift, subst_subst, Syn.subst_var]

theorem Tm.subst_itG_cases (c p : Tm n) (h : Tm (n + 1)) :
    Syn.subst (Fin.cases c (Fin.cases p Syn.var)) (Tm.itG h) = Syn.subst (inst p) h := by
  unfold Tm.itG
  rw [subst_subst]
  refine congrArg (fun ρ => Syn.subst ρ h) (funext (Fin.cases ?_ fun l => ?_)) <;> simp

/-- A closed equation holds under every substitution, in every context. -/
theorem Teq.substNil {h h' : Tm n} (hh : [] ⊢[TeqAx] h ≐ h') {Γ' : List (Fm Tm m)}
    (σ : Fin n → Tm m) : Γ' ⊢[TeqAx] Syn.subst σ h ≐ Syn.subst σ h' :=
  Prf.ofNil (hh.subst σ)

namespace Q

variable {Γ : List (Fm Tm n)}

/-! ### Uniqueness of iteration -/

/-- A term with the base and the step of an iterator is that iterator. -/
theorem iter_unique (f : Tm (n + 1)) (a : Tm n) (h : Tm (n + 1)) (c : Tm n)
    (h0 : mk Γ (Syn.subst (inst Tm.zero) f) = mk Γ a)
    (hS : ∀ Δ : List (Fm Tm (n + 1)), mk Δ (Syn.subst (repl (Tm.succ (var 0))) f)
      = app (Syn.subst (up fun i => var i.succ) h) (mk Δ f)) :
    mk Γ (Syn.subst (inst c) f) = mk Γ (Tm.iter c a h) := by
  have key := eqInd (Γ := Γ) f
    (Tm.iter (var 0) (shift a) (Syn.subst (up (fun i => var i.succ)) h)) c
    (by
      simp only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        Syn.subst_up_inst_up_shift]
      exact h0.trans (sound (Teq.iterZero a h)).symm)
    (fun ih => by
      simp only [Tm.subst_iter, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift,
        Syn.subst_up_repl_up_shift]
      rw [hS, ih]
      exact (iterate_succ _ (mk _ (var 0)) (mk _ (shift a))).symm)
  simpa only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    Syn.subst_up_inst_up_shift] using key

/-- The iterator respects equality of its body. -/
theorem iter_body_congr {h h' : Tm (n + 1)} (hh : [] ⊢[TeqAx] h ≐ h') (c a : Tm n) :
    Γ ⊢[TeqAx] Tm.iter c a h ≐ Tm.iter c a h' := by
  refine exact ?_
  have key := iter_unique (Γ := Γ)
    (Tm.iter (var 0) (shift a) (Syn.subst (up (fun i => var i.succ)) h)) a h' c
    (by
      simp only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        Syn.subst_up_inst_up_shift]
      exact sound (Teq.iterZero a h))
    (fun Δ => by
      simp only [Tm.subst_iter, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift,
        Syn.subst_up_repl_up_shift]
      refine (iterate_succ _ (mk Δ (var 0)) (mk Δ (shift a))).trans (sound ?_)
      rw [subst_subst, subst_subst]
      exact Teq.substNil hh _)
  simpa only [Tm.subst_iter, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    Syn.subst_up_inst_up_shift] using key

/-- The iterator respects provable equality in all three arguments. -/
theorem iter_congr {c c' a a' : Tm n} {h h' : Tm (n + 1)} (hc : Γ ⊢[TeqAx] c ≐ c')
    (ha : Γ ⊢[TeqAx] a ≐ a') (hh : [] ⊢[TeqAx] h ≐ h') :
    Γ ⊢[TeqAx] Tm.iter c a h ≐ Tm.iter c' a' h' := by
  refine exact ?_
  have e : mk Γ (Tm.iter c a h) = mk Γ (Tm.iter c' a' h) := by
    show iterate h (mk Γ c) (mk Γ a) = iterate h (mk Γ c') (mk Γ a')
    rw [sound hc, sound ha]
  exact e.trans (sound (iter_body_congr hh c' a'))

/-- A recursion that ignores its counter is the iterator. -/
theorem prc_itG (c a : Tm n) (h : Tm (n + 1)) :
    Γ ⊢[TeqAx] Tm.prc c a (Tm.itG h) ≐ Tm.iter c a h := by
  refine exact ?_
  have key := iter_unique (Γ := Γ)
    (Tm.prc (var 0) (shift a) (Tm.itG (Syn.subst (up (fun i => var i.succ)) h))) a h c
    (by
      simp only [Tm.subst_prc, Tm.subst_itG, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, Syn.subst_up_inst_up_shift]
      exact sound (prc_zero a _))
    (fun Δ => by
      simp only [Tm.subst_prc, Tm.subst_itG, Syn.subst_var, Syn.repl_zero,
        Syn.subst_repl_shift, Syn.subst_up_repl_up_shift]
      exact (sound (prc_succ _ _ _)).trans (congrArg (mk Δ) (Tm.subst_itG_cases _ _ _)))
  simpa only [Tm.subst_prc, Tm.subst_itG, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, Syn.subst_up_inst_up_shift] using key

end Q

namespace RoundTrip

/-! ### Codes of the simulated iterator -/

theorem code_stepSym (H : PR (n + 1)) :
    FromPRA.code (ToPRA.stepSym H) = Tm.itG (FromPRA.code H) := by
  have e : (fun j => FromPRA.code
        ((Fin.cases (PR.proj 1) (fun l => PR.proj l.succ.succ) : Fin (n + 1) → PR (n + 2)) j))
      = Fin.cases (Syn.var 1) (fun l => Syn.var l.succ.succ) := by
    refine funext (Fin.cases ?_ fun l => ?_) <;> rfl
  exact congrArg (fun ρ => Syn.subst ρ (FromPRA.code H)) e

theorem subst_code_iterSym (C : Tm n) (A : PR n) (H : PR (n + 1)) :
    Syn.subst (inst C) (FromPRA.code (ToPRA.iterSym A H))
      = Tm.prc C (FromPRA.code A) (Tm.itG (FromPRA.code H)) := by
  unfold ToPRA.iterSym
  rw [FromPRA.code_prec, code_stepSym, Tm.subst_prc, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, Tm.subst_itG, Tm.subst_itG, Syn.subst_up_inst_up_shift]

theorem code_cases_proj (P : PR n) :
    (fun j => FromPRA.code ((Fin.cases P PR.proj : Fin (n + 1) → PR n) j))
      = inst (FromPRA.code P) := by
  refine funext (Fin.cases ?_ fun l => ?_) <;> rfl

/-- Compiling a term to a function symbol and back gives the term. -/
theorem code_code (t : Tm n) : [] ⊢[TeqAx] FromPRA.code (ToPRA.code t) ≐ t := by
  induction t with
  | var i => exact Prf.eqRefl _
  | zero => exact Prf.eqRefl _
  | succ t ih => exact Q.exact (congrArg Q.succ (Q.sound ih))
  | iter c a h ihc iha ihh =>
    show [] ⊢[TeqAx] Syn.subst (fun j => FromPRA.code
        ((Fin.cases (ToPRA.code c) PR.proj : Fin (_ + 1) → PR _) j))
        (FromPRA.code (ToPRA.iterSym (ToPRA.code a) (ToPRA.code h))) ≐ _
    rw [code_cases_proj, subst_code_iterSym]
    exact Prf.eqTrans (Q.prc_itG _ _ _) (Q.iter_congr ihc iha ihh)

/-- The round trip `T_eq → iPRA → T_eq` is provably the identity on terms. -/
theorem sigma_tau (t : Tm n) : [] ⊢[TeqAx] FromPRA.sigma (ToPRA.tau t) ≐ t := by
  induction t with
  | var i => exact Prf.eqRefl _
  | zero => exact Prf.eqRefl _
  | succ t ih => exact Q.exact (congrArg Q.succ (Q.sound ih))
  | iter c a h ihc _ _ =>
    show [] ⊢[TeqAx] Syn.subst (fun i => FromPRA.sigma (inst (ToPRA.tau c) i))
        (FromPRA.code (ToPRA.iterSym (ToPRA.code a) (ToPRA.code h))) ≐ _
    rw [FromPRA.sigma_inst, subst_code_iterSym]
    exact Prf.eqTrans (Q.prc_itG _ _ _) (Q.iter_congr ihc (code_code a) (code_code h))

end RoundTrip

end LeanProofs.ConciseIPRA

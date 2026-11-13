import ConciseIPRA.PRAToScalar
import ConciseIPRA.ScalarToPRA

/-!
# The round trip `T_eq → iPRA → T_eq`

The translation `tau` of `T_eq` into `iPRA` turns an iterator into the function
symbol `prec a (stepSym h)`, and the translation `sigma` back turns that symbol
into the term `prc c a (itG h)`: a primitive recursion whose step ignores the
counter.  One equation induction shows that such a recursion is the iterator
of any provably equal body,

  `prc c a (itG h) = I(c, a; u. h')`  when  `⊢ h = h'`,

and two instances of it show that the iterator respects provable equality of
its body.  Hence `T_eq ⊢ sigma (tau t) = t` for every term `t`.
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

namespace Q

variable {Γ : List (Fm Tm n)}

/-- A recursion that ignores its counter is the iterator of a provably equal body. -/
theorem prc_itG (c a : Tm n) {h h' : Tm (n + 1)} (hh : [] ⊢[TeqAx] h ≐ h') :
    Γ ⊢[TeqAx] Tm.prc c a (Tm.itG h) ≐ Tm.iter c a h' := by
  refine exact ?_
  have key := eqInd (Γ := Γ)
    (Tm.prc (var 0) (shift a) (Tm.itG (Syn.subst (up (fun i => var i.succ)) h)))
    (Tm.iter (var 0) (shift a) (Syn.subst (up (fun i => var i.succ)) h')) c
    (by
      simp only [Tm.subst_prc, Tm.subst_itG, Tm.subst_iter, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, Syn.subst_up_inst_up_shift]
      exact (sound (prc_zero a _)).trans (sound (Teq.iterZero a h')).symm)
    (fun ih => by
      simp only [Tm.subst_prc, Tm.subst_itG, Tm.subst_iter, Syn.subst_var, Syn.repl_zero,
        Syn.subst_repl_shift, Syn.subst_up_repl_up_shift]
      refine (sound (prc_succ _ _ _)).trans ((congrArg (mk _) (Tm.subst_itG_cases _ _ _)).trans
        ((sound ?_).trans ((congrArg (app (Syn.subst (up fun i => var i.succ) h')) ih).trans
          (iterate_succ _ (mk _ (var 0)) (mk _ (shift a))).symm)))
      rw [subst_subst, subst_subst]
      exact (hh.subst _).ofNil)
  simpa only [Tm.subst_prc, Tm.subst_itG, Tm.subst_iter, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, Syn.subst_up_inst_up_shift] using key

/-- The iterator respects provable equality in all three arguments. -/
theorem iter_congr {c c' a a' : Tm n} {h h' : Tm (n + 1)} (hc : Γ ⊢[TeqAx] c ≐ c')
    (ha : Γ ⊢[TeqAx] a ≐ a') (hh : [] ⊢[TeqAx] h ≐ h') :
    Γ ⊢[TeqAx] Tm.iter c a h ≐ Tm.iter c' a' h' :=
  Prf.eqTrans (Teq.iterCongr h hc ha)
    (Prf.eqTrans (Prf.eqSymm (prc_itG c' a' (Prf.eqRefl h))) (prc_itG c' a' hh))

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

/-- Compiling a term of `iPRA` to a function symbol and translating the symbol
gives the translation of the term. -/
theorem code_pcode (t : PTm n) : FromPRA.code (ToPRA.pcode t) = FromPRA.sigma t := by
  induction t with
  | var i => rfl
  | app f ts ih => exact congrArg (fun ρ => Syn.subst ρ (FromPRA.code f)) (funext ih)

/-- The round trip `T_eq → iPRA → T_eq` is provably the identity on terms. -/
theorem sigma_tau (t : Tm n) : [] ⊢[TeqAx] FromPRA.sigma (ToPRA.tau t) ≐ t := by
  induction t with
  | var i => exact Prf.eqRefl _
  | zero => exact Prf.eqRefl _
  | succ t ih => exact Q.exact (congrArg Q.succ (Q.sound ih))
  | iter c a h ihc iha ihh =>
    rw [ToPRA.tau, FromPRA.sigma_app, FromPRA.sigma_inst, subst_code_iterSym, code_pcode,
      code_pcode]
    exact Prf.eqTrans (Q.prc_itG _ _ ihh) (Teq.iterCongr h ihc iha)

end RoundTrip

end LeanProofs.ConciseIPRA

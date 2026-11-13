import ConciseIPRA.RoundTripScalar

/-!
# The round trip `iPRA → T_eq → iPRA`

The translation `sigma` of `iPRA` into `T_eq` replaces a function symbol `f` by
its code, a term of `T_eq`, and the translation `tau` back turns that term into
a term of `iPRA`.  The key fact is

  `iPRA ⊢ tau (code f) = f(x₀, …, x_{k-1})`

for every primitive recursive function symbol `f`, proved by induction on `f`.
For a recursion the two sides satisfy the same recursion equations: those of
the left side are the recursion equations of `Tm.prc`, transported from `T_eq`
by the interpretation of `T_eq` in `iPRA`, and quantifier-free induction in
`iPRA` identifies the two.  Hence `iPRA ⊢ tau (sigma t) = t` for every term `t`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m k : ℕ}

namespace RoundTrip

/-! ### The translation `tau` and the two substitutions of induction -/

theorem tau_subst_inst (a : Tm n) (t : Tm (n + 1)) {Γ : List (Fm PTm n)} :
    Γ ⊢[PRAAx] Syn.subst (inst (ToPRA.tau a)) (ToPRA.tau t)
      ≐ ToPRA.tau (Syn.subst (inst a) t) := by
  have h := ToPRA.morph.f_subst (inst a) t
  rw [ToPRA.morph.f_inst] at h
  exact Prf.ofNil (Prf.eqSymm h)

theorem tau_subst_repl (s t : Tm (n + 1)) {Γ : List (Fm PTm (n + 1))} :
    Γ ⊢[PRAAx] Syn.subst (repl (ToPRA.tau s)) (ToPRA.tau t)
      ≐ ToPRA.tau (Syn.subst (repl s) t) := by
  have h := ToPRA.morph.f_subst (repl s) t
  rw [ToPRA.morph.f_repl] at h
  exact Prf.ofNil (Prf.eqSymm h)

/-! ### The recursion equations of the code of a recursion, in `T_eq` -/

theorem code_prec_zero (f : PR k) (g : PR (k + 2)) :
    [] ⊢[TeqAx] Syn.subst (inst Tm.zero) (FromPRA.code (.prec f g)) ≐ FromPRA.code f := by
  rw [FromPRA.code_prec, Tm.subst_prc, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
  exact Q.prc_zero _ _

theorem code_prec_succ (f : PR k) (g : PR (k + 2)) :
    [] ⊢[TeqAx] Syn.subst (repl (Tm.succ (Syn.var 0))) (FromPRA.code (.prec f g))
      ≐ Syn.subst (Fin.cases (Syn.var 0) (repl (FromPRA.code (.prec f g))))
          (FromPRA.code g) := by
  have h := FromPRA.ax_precSucc f g
  rw [FromPRA.sigma_app, FromPRA.sigma_repl, FromPRA.sigma_succ, FromPRA.sigma_var,
    FromPRA.sigma_app] at h
  convert h using 3
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j <;> simp [FromPRA.sigma_app_var]

/-! ### The code of a function symbol denotes the symbol -/

/-- A substitution instance of a code, given what the code denotes. -/
theorem tau_subst_code {f : PR k}
    (e : [] ⊢[PRAAx] ToPRA.tau (FromPRA.code f) ≐ PTm.app f Syn.var) (σ : Fin k → Tm n) :
    [] ⊢[PRAAx] ToPRA.tau (Syn.subst σ (FromPRA.code f)) ≐ PTm.app f fun j => ToPRA.tau (σ j) := by
  have h := e.subst fun j => ToPRA.tau (σ j)
  simp only [Fm.subst_eq, List.map_nil, PTm.subst_app, Syn.subst_var] at h
  exact Prf.eqTrans (ToPRA.tau_subst σ _) h

/-- The code of a function symbol denotes the symbol, provably in `iPRA`. -/
theorem tau_code (f : PR k) :
    [] ⊢[PRAAx] ToPRA.tau (FromPRA.code f) ≐ PTm.app f Syn.var := by
  induction f with
  | zero =>
    show [] ⊢[PRAAx] PTm.app PR.zero Fin.elim0 ≐ PTm.app PR.zero Syn.var
    exact ToPRA.congr PR.zero (fun i => i.elim0)
  | succ =>
    show [] ⊢[PRAAx] PTm.app PR.succ (fun _ => Syn.var 0) ≐ PTm.app PR.succ Syn.var
    refine ToPRA.congr PR.succ (fun i => ?_)
    exact Fin.cases (Prf.eqRefl _) (fun l => l.elim0) i
  | proj i => exact Prf.eqSymm (PRA.proj i Syn.var)
  | comp f gs ihf ihg =>
    rw [FromPRA.code_comp]
    exact Prf.eqTrans (tau_subst_code ihf _)
      (Prf.eqTrans (ToPRA.congr f ihg) (Prf.eqSymm (PRA.comp f gs Syn.var)))
  | prec f g ihf ihg =>
    have h := ToPRA.prec_uniq (σ := Syn.var) (ToPRA.tau (FromPRA.code (.prec f g)))
      (Prf.eqTrans (tau_subst_inst Tm.zero _)
        (Prf.eqTrans (ToPRA.interp.sound (code_prec_zero f g)) ihf))
      (Prf.eqTrans (tau_subst_repl (Tm.succ (Syn.var 0)) _)
        (Prf.eqTrans (ToPRA.interp.sound (code_prec_succ f g))
          (Prf.eqTrans (tau_subst_code ihg _) (ToPRA.congr g fun j => by
            refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j <;>
              exact Prf.eqRefl _))))
    rwa [Syn.up_var] at h

/-- The round trip `iPRA → T_eq → iPRA` is provably the identity on terms. -/
theorem tau_sigma (t : PTm n) : [] ⊢[PRAAx] ToPRA.tau (FromPRA.sigma t) ≐ t := by
  induction t with
  | var i => exact Prf.eqRefl _
  | app f ts ih =>
    rw [FromPRA.sigma_app]
    exact Prf.eqTrans (tau_subst_code (tau_code f) _) (ToPRA.congr f ih)

end RoundTrip

end LeanProofs.ConciseIPRA

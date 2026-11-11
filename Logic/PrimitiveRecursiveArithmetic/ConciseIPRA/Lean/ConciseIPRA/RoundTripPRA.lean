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

namespace Syn

variable {T : ℕ → Type} [Syn T]

/-- Feeding the counter and the previous value to a step weakened under its two
binders. -/
theorem subst_cases_up_up_shift (c p : T (n + 1)) (h : T (n + 2)) :
    subst (Fin.cases c (Fin.cases p var)) (subst (up (up (fun i => var i.succ))) h)
      = subst (Fin.cases c (repl p)) h := by
  rw [subst_subst]
  refine congrArg (fun ρ => subst ρ h) (funext fun j => ?_)
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j
  · simp only [Fin.cases_zero, up_zero, subst_var]
  · simp only [Fin.cases_succ, Fin.cases_zero, repl_zero, up_succ, up_zero, shift_var,
      subst_var]
  · simp only [Fin.cases_succ, repl_succ, up_succ, shift_var, subst_var]

end Syn

/-- A closed equation of `iPRA` holds under every substitution, in every
context. -/
theorem PRA.substNil {s t : PTm k} (h : [] ⊢[PRAAx] s ≐ t) {Γ : List (Fm PTm n)}
    (σ : Fin k → PTm n) : Γ ⊢[PRAAx] Syn.subst σ s ≐ Syn.subst σ t :=
  Prf.ofNil (h.subst σ)

theorem PTm.subst_app_var (f : PR k) (σ : Fin k → PTm n) :
    Syn.subst σ (PTm.app f Syn.var) = PTm.app f σ :=
  (PTm.subst_app σ f Syn.var).trans
    (congrArg (PTm.app f) (funext fun i => Syn.subst_var σ i))

namespace RoundTrip

/-! ### The translation `tau` and the two substitutions of induction -/

theorem tau_inst (a : Tm n) : (fun i => ToPRA.tau (inst a i)) = inst (ToPRA.tau a) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem tau_repl (s : Tm (n + 1)) : (fun i => ToPRA.tau (repl s i)) = repl (ToPRA.tau s) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem tau_subst_inst (a : Tm n) (t : Tm (n + 1)) {Γ : List (Fm PTm n)} :
    Γ ⊢[PRAAx] Syn.subst (inst (ToPRA.tau a)) (ToPRA.tau t)
      ≐ ToPRA.tau (Syn.subst (inst a) t) := by
  have h := ToPRA.tau_subst (inst a) t
  rw [tau_inst] at h
  exact Prf.ofNil (Prf.eqSymm h)

theorem tau_subst_repl (s t : Tm (n + 1)) {Γ : List (Fm PTm (n + 1))} :
    Γ ⊢[PRAAx] Syn.subst (repl (ToPRA.tau s)) (ToPRA.tau t)
      ≐ ToPRA.tau (Syn.subst (repl s) t) := by
  have h := ToPRA.tau_subst (repl s) t
  rw [tau_repl] at h
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
  have e1 : Syn.subst (repl (Tm.succ (Syn.var 0))) (FromPRA.code (.prec f g))
      = Tm.prc (Tm.succ (Syn.var 0)) (shift (FromPRA.code f))
          (Syn.subst (up (up (fun i => Syn.var i.succ))) (FromPRA.code g)) := by
    rw [FromPRA.code_prec, Tm.subst_prc, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift,
      Syn.subst_up_up_repl_up_up_shift]
  rw [e1, ← Syn.subst_cases_up_up_shift (Syn.var 0) (FromPRA.code (.prec f g))
    (FromPRA.code g)]
  exact Q.prc_succ _ _ _

/-! ### The code of a function symbol denotes the symbol -/

theorem tau_code_prec_zero (f : PR k) (g : PR (k + 2))
    (ihf : [] ⊢[PRAAx] ToPRA.tau (FromPRA.code f) ≐ PTm.app f Syn.var)
    {Γ : List (Fm PTm k)} :
    Γ ⊢[PRAAx] (ToPRA.tau (FromPRA.code (.prec f g))
      ≐ PTm.app (.prec f g) Syn.var).subst (inst PTm.zero) := by
  show Γ ⊢[PRAAx] Syn.subst (inst PTm.zero) (ToPRA.tau (FromPRA.code (.prec f g)))
    ≐ Syn.subst (inst PTm.zero) (PTm.app (.prec f g) Syn.var)
  rw [PTm.subst_app_var]
  have a1 : Γ ⊢[PRAAx] Syn.subst (inst PTm.zero) (ToPRA.tau (FromPRA.code (.prec f g)))
      ≐ ToPRA.tau (Syn.subst (inst Tm.zero) (FromPRA.code (.prec f g))) :=
    tau_subst_inst Tm.zero _
  have s := ToPRA.interp.sound (code_prec_zero f g)
  have a2 : Γ ⊢[PRAAx] ToPRA.tau (Syn.subst (inst Tm.zero) (FromPRA.code (.prec f g)))
      ≐ ToPRA.tau (FromPRA.code f) := Prf.ofNil s
  exact Prf.eqTrans a1 (Prf.eqTrans a2
    (Prf.eqTrans (Prf.ofNil ihf) (Prf.eqSymm (PRA.precZero f g Syn.var))))

theorem tau_code_prec_succ (f : PR k) (g : PR (k + 2))
    (ihg : [] ⊢[PRAAx] ToPRA.tau (FromPRA.code g) ≐ PTm.app g Syn.var)
    {Γ : List (Fm PTm (k + 1))}
    (ih : Γ ⊢[PRAAx] ToPRA.tau (FromPRA.code (.prec f g)) ≐ PTm.app (.prec f g) Syn.var) :
    Γ ⊢[PRAAx] (ToPRA.tau (FromPRA.code (.prec f g))
      ≐ PTm.app (.prec f g) Syn.var).subst (repl (PTm.succ (Syn.var 0))) := by
  show Γ ⊢[PRAAx]
    Syn.subst (repl (PTm.succ (Syn.var 0))) (ToPRA.tau (FromPRA.code (.prec f g)))
      ≐ Syn.subst (repl (PTm.succ (Syn.var 0))) (PTm.app (.prec f g) Syn.var)
  rw [PTm.subst_app_var]
  have a1 : Γ ⊢[PRAAx]
      Syn.subst (repl (PTm.succ (Syn.var 0))) (ToPRA.tau (FromPRA.code (.prec f g)))
        ≐ ToPRA.tau (Syn.subst (repl (Tm.succ (Syn.var 0))) (FromPRA.code (.prec f g))) :=
    tau_subst_repl (Tm.succ (Syn.var 0)) _
  have s := ToPRA.interp.sound (code_prec_succ f g)
  have a2 : Γ ⊢[PRAAx]
      ToPRA.tau (Syn.subst (repl (Tm.succ (Syn.var 0))) (FromPRA.code (.prec f g)))
        ≐ ToPRA.tau (Syn.subst
            (Fin.cases (Syn.var 0) (repl (FromPRA.code (.prec f g)))) (FromPRA.code g)) :=
    Prf.ofNil s
  have a3 : Γ ⊢[PRAAx]
      ToPRA.tau (Syn.subst
          (Fin.cases (Syn.var 0) (repl (FromPRA.code (.prec f g)))) (FromPRA.code g))
        ≐ Syn.subst (fun j => ToPRA.tau ((Fin.cases (Syn.var 0)
              (repl (FromPRA.code (.prec f g))) : Fin (k + 2) → Tm (k + 1)) j))
            (ToPRA.tau (FromPRA.code g)) :=
    Prf.ofNil (ToPRA.tau_subst _ _)
  have a4 : Γ ⊢[PRAAx]
      Syn.subst (fun j => ToPRA.tau ((Fin.cases (Syn.var 0)
            (repl (FromPRA.code (.prec f g))) : Fin (k + 2) → Tm (k + 1)) j))
          (ToPRA.tau (FromPRA.code g))
        ≐ PTm.app g (fun j => ToPRA.tau ((Fin.cases (Syn.var 0)
            (repl (FromPRA.code (.prec f g))) : Fin (k + 2) → Tm (k + 1)) j)) := by
    have h := PRA.substNil ihg (Γ := Γ) (fun j => ToPRA.tau ((Fin.cases (Syn.var 0)
      (repl (FromPRA.code (.prec f g))) : Fin (k + 2) → Tm (k + 1)) j))
    rwa [PTm.subst_app_var] at h
  have a5 : Γ ⊢[PRAAx]
      PTm.app g (fun j => ToPRA.tau ((Fin.cases (Syn.var 0)
          (repl (FromPRA.code (.prec f g))) : Fin (k + 2) → Tm (k + 1)) j))
        ≐ PTm.app g (Fin.cases (Syn.var 0) (repl (PTm.app (.prec f g) Syn.var))) := by
    refine ToPRA.congr g (fun j => ?_)
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j
    · exact Prf.eqRefl _
    · exact ih
    · exact Prf.eqRefl _
  exact Prf.eqTrans a1 (Prf.eqTrans a2 (Prf.eqTrans a3 (Prf.eqTrans a4 (Prf.eqTrans a5
    (Prf.eqSymm (Prf.axm (PRAAx.precSucc f g)))))))

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
    refine Fin.cases ?_ (fun l => l.elim0) i
    exact Prf.eqRefl _
  | proj i => exact Prf.eqSymm (PRA.proj i Syn.var)
  | comp f gs ihf ihg =>
    rw [FromPRA.code_comp]
    have h1 := ToPRA.tau_subst (fun j => FromPRA.code (gs j)) (FromPRA.code f)
    have h2 : [] ⊢[PRAAx]
        Syn.subst (fun j => ToPRA.tau (FromPRA.code (gs j))) (ToPRA.tau (FromPRA.code f))
          ≐ PTm.app f (fun j => ToPRA.tau (FromPRA.code (gs j))) := by
      have h := PRA.substNil ihf (Γ := []) (fun j => ToPRA.tau (FromPRA.code (gs j)))
      rwa [PTm.subst_app_var] at h
    exact Prf.eqTrans h1 (Prf.eqTrans h2
      (Prf.eqTrans (ToPRA.congr f ihg) (Prf.eqSymm (PRA.comp f gs Syn.var))))
  | prec f g ihf ihg =>
    refine Prf.allOpen (Γ := []) (PRA.qfInd
      (ToPRA.tau (FromPRA.code (.prec f g)) ≐ PTm.app (.prec f g) Syn.var) trivial ?_ ?_)
    · exact tau_code_prec_zero f g ihf
    · exact tau_code_prec_succ f g ihg Prf.hyp0

/-- The round trip `iPRA → T_eq → iPRA` is provably the identity on terms. -/
theorem tau_sigma (t : PTm n) : [] ⊢[PRAAx] ToPRA.tau (FromPRA.sigma t) ≐ t := by
  induction t with
  | var i => exact Prf.eqRefl _
  | app f ts ih =>
    rw [FromPRA.sigma_app]
    have h1 := ToPRA.tau_subst (fun i => FromPRA.sigma (ts i)) (FromPRA.code f)
    have h2 : [] ⊢[PRAAx]
        Syn.subst (fun i => ToPRA.tau (FromPRA.sigma (ts i))) (ToPRA.tau (FromPRA.code f))
          ≐ PTm.app f (fun i => ToPRA.tau (FromPRA.sigma (ts i))) := by
      have h := PRA.substNil (tau_code f) (Γ := [])
        (fun i => ToPRA.tau (FromPRA.sigma (ts i)))
      rwa [PTm.subst_app_var] at h
    exact Prf.eqTrans h1 (Prf.eqTrans h2 (ToPRA.congr f ih))

end RoundTrip

end LeanProofs.ConciseIPRA

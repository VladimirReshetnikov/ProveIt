import ConciseIPRA.Scalar
import ConciseIPRA.PR
import ConciseIPRA.Interpretation

/-!
# Interpreting `T_eq` in `iPRA`

An iterator term `I(c, a; u.h)` binds a variable in its step term, whereas a
term of `iPRA` has no binders.  The interpretation therefore compiles every
iterator term `t` over `n` variables into a primitive recursive function symbol
`code t` of arity `n`; the iterator becomes primitive recursion whose step
ignores the counter.  The term translation `tau` uses these symbols:

`tau (I(c, a; u.h)) = iterSym (code a) (code h) (tau c, x⃗)`.

`code_eval` relates the two: `code t` applied to arguments is provably the
translation `tau t` with those arguments substituted.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open PTm (app)

namespace ToPRA

variable {n m k : ℕ}

/-- The step of the primitive recursion simulating an iterator: from the
arguments `(counter, previous, x⃗)` it passes `(previous, x⃗)` on to `g`. -/
def stepSym (g : PR (n + 1)) : PR (n + 2) :=
  .comp g (Fin.cases (.proj 1) (fun l => .proj l.succ.succ))

/-- The function symbol `(c, x⃗) ↦ I(c, a(x⃗); u.h(u, x⃗))`. -/
def iterSym (a : PR n) (h : PR (n + 1)) : PR (n + 1) := .prec a (stepSym h)

/-- An iterator term as a primitive recursive function symbol of its free
variables. -/
def code : {n : ℕ} → Tm n → PR n
  | _, .var i => .proj i
  | _, .zero => .comp .zero Fin.elim0
  | _, .succ t => .comp .succ (fun _ => code t)
  | _, .iter c a h => .comp (iterSym (code a) (code h)) (Fin.cases (code c) .proj)

/-- The translation of iterator terms into terms of `iPRA`. -/
def tau : {n : ℕ} → Tm n → PTm n
  | _, .var i => PTm.var i
  | _, .zero => PTm.zero
  | _, .succ t => PTm.succ (tau t)
  | _, .iter c a h => app (iterSym (code a) (code h)) (Fin.cases (tau c) PTm.var)

variable {Γ : List (Fm PTm n)}

/-- Function symbols respect provable equality of their arguments. -/
theorem congr (f : PR k) {ts ts' : Fin k → PTm n} (h : ∀ i, Γ ⊢[PRAAx] ts i ≐ ts' i) :
    Γ ⊢[PRAAx] app f ts ≐ app f ts' := by
  simpa using Prf.eqCongr (app f Syn.var) h

/-- The simulated iterator at zero. -/
theorem iterSym_zero (a : PR k) (h : PR (k + 1)) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] app (iterSym a h) (Fin.cases PTm.zero xs) ≐ app a xs :=
  PRA.precZero a (stepSym h) xs

/-- The simulated iterator at a successor. -/
theorem iterSym_succ (a : PR k) (h : PR (k + 1)) (y : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] app (iterSym a h) (Fin.cases (PTm.succ y) xs)
      ≐ app h (Fin.cases (app (iterSym a h) (Fin.cases y xs)) xs) := by
  refine Prf.eqTrans (PRA.precSucc a (stepSym h) y xs) ?_
  refine Prf.eqTrans (PRA.comp h _ _) ?_
  refine congr h (Fin.cases ?_ fun l => ?_)
  · exact PRA.proj 1 _
  · exact PRA.proj l.succ.succ _

/-- The function symbol of a term, applied to arguments, is the translation of
the term with the arguments substituted. -/
theorem code_eval (t : Tm k) :
    ∀ {n : ℕ} (ts : Fin k → PTm n) (Γ : List (Fm PTm n)),
      Γ ⊢[PRAAx] app (code t) ts ≐ Syn.subst ts (tau t) := by
  induction t with intro n ts Γ
  | var i => exact PRA.proj i ts
  | zero =>
    exact Prf.eqTrans (PRA.comp PR.zero Fin.elim0 ts) (congr PR.zero (fun j => j.elim0))
  | succ t ih =>
    exact Prf.eqTrans (PRA.comp PR.succ (fun _ => code t) ts)
      (congr PR.succ (fun _ => ih ts Γ))
  | iter c a h ihc _ _ =>
    refine Prf.eqTrans (PRA.comp _ _ ts) ?_
    refine congr _ (Fin.cases ?_ fun l => ?_)
    · exact ihc ts Γ
    · exact PRA.proj l ts

/-! ### Extensionality of the simulated iterator -/

theorem subst_inst_up (t : PTm m) (σ : Fin k → PTm m) :
    (fun i => Syn.subst (inst t) (Syn.up σ i)) = Fin.cases t σ := by
  refine funext (Fin.cases ?_ fun j => ?_)
  · simp
  · simp [Syn.shift, Syn.subst_subst]

theorem subst_repl_up (s : PTm (m + 1)) (σ : Fin k → PTm m) :
    (fun i => Syn.subst (repl s) (Syn.up σ i)) = Fin.cases s (fun j => Syn.shift (σ j)) := by
  refine funext (Fin.cases ?_ fun j => ?_)
  · simp
  · simp [Syn.shift, Syn.subst_subst]

/-- Two simulated iterators whose bases and steps agree along a substitution
agree at every count.  This is an induction inside `iPRA`. -/
theorem iterSym_ext {a' : PR m} {h' : PR (m + 1)} {a : PR k} {h : PR (k + 1)}
    {σ : Fin k → PTm m}
    (ha : [] ⊢[PRAAx] app a' Syn.var ≐ app a σ)
    (hh : [] ⊢[PRAAx] app h' Syn.var ≐ app h (Syn.up σ)) (t : PTm m) :
    [] ⊢[PRAAx] app (iterSym a' h') (Fin.cases t Syn.var)
      ≐ app (iterSym a h) (Fin.cases t σ) := by
  have e : (repl (Syn.var 0) : Fin (m + 1) → PTm (m + 1)) = Syn.var := by
    refine funext (Fin.cases ?_ fun j => ?_) <;> simp
  have key : [] ⊢[PRAAx]
      Fm.all (app (iterSym a' h') Syn.var ≐ app (iterSym a h) (Syn.up σ)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, PTm.subst_app, Syn.subst_var]
      rw [subst_inst_up]
      exact Prf.eqTrans (iterSym_zero a' h' Syn.var)
        (Prf.eqTrans ha (Prf.eqSymm (iterSym_zero a h σ)))
    · have hL := iterSym_succ
        (Γ := [app (iterSym a' h') Syn.var ≐ app (iterSym a h) (Syn.up σ)])
        a' h' (Syn.var 0) (fun i => Syn.var i.succ)
      have hM := (hh.subst (repl (app (iterSym a' h') Syn.var))).ofNil
        (Γ := [app (iterSym a' h') Syn.var ≐ app (iterSym a h) (Syn.up σ)])
      simp only [Fm.subst_eq, PTm.subst_app, Syn.subst_var] at hM ⊢
      rw [subst_repl_up] at hM ⊢
      rw [show (Fin.cases (Syn.var 0) fun i => Syn.var i.succ : Fin (m + 1) → PTm (m + 1))
        = Syn.var from e] at hL
      refine Prf.eqTrans hL (Prf.eqTrans hM (Prf.eqTrans (congr h (fun i => ?_))
        (Prf.eqSymm (iterSym_succ a h (Syn.var 0) (fun j => Syn.shift (σ j))))))
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Prf.hyp0
      · exact Prf.eqRefl _
  have h₁ := Prf.allE t key
  simp only [Fm.subst_eq, PTm.subst_app, Syn.subst_var] at h₁
  rwa [subst_inst_up] at h₁

/-! ### The translation commutes with substitution -/

/-- The translation commutes, provably, with every renaming of every value of
`ρ`.  It is shown below that every substitution has this property. -/
def Good (ρ : Fin n → Tm m) : Prop :=
  ∀ (i : Fin n) (k : ℕ) (r : Fin m → Fin k),
    [] ⊢[PRAAx] tau (Syn.subst (fun j => (Syn.var (r j) : Tm k)) (ρ i))
      ≐ Syn.subst (fun j => (Syn.var (r j) : PTm k)) (tau (ρ i))

theorem Good.up {ρ : Fin n → Tm m} (hρ : Good ρ) : Good (Syn.up ρ) := by
  intro i k r
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Prf.eqRefl _
  · have h3 : [] ⊢[PRAAx]
        Syn.subst (fun l => (Syn.var (r l) : PTm k)) (tau (Syn.shift (ρ j)))
          ≐ Syn.subst (fun l => (Syn.var (r l) : PTm k)) (Syn.shift (tau (ρ j))) :=
      (hρ j (m + 1) Fin.succ).subst (fun l => (Syn.var (r l) : PTm k))
    rw [Syn.subst_shift] at h3
    rw [Syn.up_succ, Syn.subst_shift]
    exact Prf.eqTrans (hρ j k (fun l => r l.succ)) (Prf.eqSymm h3)

theorem tau_subst_of_good (t : Tm n) :
    ∀ {m : ℕ} (ρ : Fin n → Tm m), Good ρ →
      ([] ⊢[PRAAx] tau (Syn.subst ρ t) ≐ Syn.subst (fun i => tau (ρ i)) (tau t)) := by
  induction t with
  | var i => intro m ρ _; exact Prf.eqRefl _
  | zero => intro m ρ _; exact congr PR.zero (fun i => i.elim0)
  | succ t ih => intro m ρ hρ; exact congr PR.succ (fun _ => ih ρ hρ)
  | iter c a h ihc iha ihh =>
    intro m ρ hρ
    rw [Tm.subst_iter]
    refine Prf.eqTrans
      (iterSym_ext (a := code a) (h := code h) (σ := fun i => tau (ρ i)) ?_ ?_ _)
      (congr _ (fun i => ?_))
    · have h1 := code_eval (Syn.subst ρ a) Syn.var ([] : List (Fm PTm m))
      rw [Syn.subst_id] at h1
      exact Prf.eqTrans h1 (Prf.eqTrans (iha ρ hρ) (Prf.eqSymm (code_eval a _ _)))
    · have h1 := code_eval (Syn.subst (Syn.up ρ) h) Syn.var ([] : List (Fm PTm (m + 1)))
      rw [Syn.subst_id] at h1
      refine Prf.eqTrans h1 (Prf.eqTrans (ihh (Syn.up ρ) hρ.up) ?_)
      refine Prf.eqTrans (Prf.eqSymm (code_eval h _ _)) (congr _ (Fin.cases ?_ fun j => ?_))
      · exact Prf.eqRefl _
      · simp only [Syn.up_succ]
        exact hρ j (m + 1) Fin.succ
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact ihc ρ hρ
      · exact Prf.eqRefl _

theorem good_ren (ξ : Fin n → Fin m) : Good (fun i => (Syn.var (ξ i) : Tm m)) := by
  intro i k r
  exact Prf.eqRefl _

/-- The translation commutes with renaming. -/
theorem tau_ren (t : Tm n) (r : Fin n → Fin m) :
    [] ⊢[PRAAx] tau (Syn.subst (fun j => (Syn.var (r j) : Tm m)) t)
      ≐ Syn.subst (fun j => (Syn.var (r j) : PTm m)) (tau t) :=
  tau_subst_of_good t _ (good_ren r)

theorem good (ρ : Fin n → Tm m) : Good ρ := fun i _ r => tau_ren (ρ i) r

/-- The translation commutes with substitution, provably in `iPRA`. -/
theorem tau_subst (ρ : Fin n → Tm m) (t : Tm n) :
    [] ⊢[PRAAx] tau (Syn.subst ρ t) ≐ Syn.subst (fun i => tau (ρ i)) (tau t) :=
  tau_subst_of_good t ρ (good ρ)

/-- The translation of iterator terms as a term morphism into `iPRA`. -/
def morph : TmMorph Tm PRAAx where
  f _ := tau
  f_var _ := rfl
  f_subst := tau_subst

/-! ### The axioms of `T_eq` hold in `iPRA` under the translation -/

theorem ax_iterZero (a : Tm n) (h : Tm (n + 1)) :
    [] ⊢[PRAAx] tau (Tm.iter Tm.zero a h) ≐ tau a := by
  have h1 := code_eval a Syn.var ([] : List (Fm PTm n))
  rw [Syn.subst_id] at h1
  exact Prf.eqTrans (iterSym_zero (code a) (code h) Syn.var) h1

theorem ax_iterSucc (c a : Tm n) (h : Tm (n + 1)) :
    [] ⊢[PRAAx] tau (Tm.iter (Tm.succ c) a h)
      ≐ tau (Syn.subst (inst (Tm.iter c a h)) h) := by
  have h1 := iterSym_succ (Γ := ([] : List (Fm PTm n))) (code a) (code h) (tau c) Syn.var
  have h2 := code_eval h (Fin.cases (tau (Tm.iter c a h)) Syn.var) ([] : List (Fm PTm n))
  have h3 := morph.f_subst (inst (Tm.iter c a h)) h
  rw [morph.f_inst] at h3
  exact Prf.eqTrans h1 (Prf.eqTrans h2 (Prf.eqSymm h3))

theorem ax_sep :
    [] ⊢[PRAAx] ((PTm.zero : PTm 0) ≐ PTm.succ PTm.zero) ⟶ Fm.bot :=
  Prf.impI (Prf.impE (PRA.succNeZero _) (Prf.eqSymm Prf.hyp0))

/-- The predecessor function symbol. -/
def pd : PR 1 := .prec .zero (.proj 0)

theorem pd_succ (y : PTm n) : Γ ⊢[PRAAx] app pd (fun _ => PTm.succ y) ≐ y :=
  Prf.eqTrans (congr pd fun i => by refine Fin.cases ?_ (fun j => j.elim0) i; exact Prf.eqRefl _)
    (Prf.eqTrans (PRA.precSucc PR.zero (PR.proj 0) y Fin.elim0) (PRA.proj 0 _))

/-- Every number is zero or the successor of its predecessor. -/
theorem pred_cases : ([] : List (Fm PTm n)) ⊢[PRAAx]
    Fm.all (((Syn.var 0 : PTm (n + 1)) ≐ PTm.zero)
      ⋎ ((Syn.var 0 : PTm (n + 1)) ≐ PTm.succ (app pd (fun _ => Syn.var 0)))) := by
  refine PRA.qfInd _ (by simp [Fm.QF]) ?_ ?_
  · simp only [Fm.subst_or, Fm.subst_eq, Syn.subst_var, Syn.inst_zero, PTm.subst_zero]
    exact Prf.orI₁ (Prf.eqRefl _)
  · simp only [Fm.subst_or, Fm.subst_eq, Syn.subst_var, Syn.repl_zero, PTm.subst_zero]
    exact Prf.orI₂ (congr PR.succ (fun _ => Prf.eqSymm (pd_succ _)))

theorem ax_cover : ([] : List (Fm PTm 1)) ⊢[PRAAx]
    ((Syn.var 0 : PTm 1) ≐ PTm.zero)
      ⋎ Fm.ex ((Syn.var 1 : PTm 2) ≐ PTm.succ (Syn.var 0)) := by
  have h := Prf.allE (Syn.var 0 : PTm 1) (pred_cases (n := 1))
  simp only [Fm.subst_or, Fm.subst_eq, Syn.subst_var, Syn.inst_zero, PTm.subst_zero] at h
  refine Prf.orE h (Prf.orI₁ Prf.hyp0) (Prf.orI₂ ?_)
  exact Prf.exI (app pd (fun _ => Syn.var 0)) Prf.hyp0

theorem ax_ind (s t : Tm (n + 1)) :
    [] ⊢[PRAAx] (((s ≐ t).subst (inst Tm.zero) ⟶
      Fm.all ((s ≐ t) ⟶ (s ≐ t).subst (repl (Tm.succ (Syn.var 0)))) ⟶
        Fm.all (s ≐ t)).map morph.f) :=
  Prf.iffMpr (morph.map_ind (s ≐ t) Tm.zero (Tm.succ (Syn.var 0)) [])
    (Prf.axm (PRAAx.ind (tau s ≐ tau t) trivial))

/-- The interpretation of `T_eq` in `iPRA`: iterator terms become primitive
recursive function symbols, and every axiom of `T_eq` becomes a theorem. -/
def interp : Interp TeqAx PRAAx where
  toTmMorph := morph
  f_ax := by
    intro k φ hφ
    cases hφ with
    | iterZero a h => exact ax_iterZero a h
    | iterSucc c a h => exact ax_iterSucc c a h
    | cover => exact ax_cover
    | sep => exact ax_sep
    | ind s t => exact ax_ind s t

end ToPRA

end LeanProofs.ConciseIPRA

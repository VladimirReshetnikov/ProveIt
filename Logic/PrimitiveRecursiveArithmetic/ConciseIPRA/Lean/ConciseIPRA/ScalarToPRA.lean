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

@[simp] theorem tau_var (i : Fin n) : tau (Syn.var i : Tm n) = Syn.var i := rfl

@[simp] theorem tau_zero : tau (Tm.zero : Tm n) = PTm.zero := rfl

@[simp] theorem tau_succ (t : Tm n) : tau (Tm.succ t) = PTm.succ (tau t) := rfl

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
  refine congr h (fun j => ?_)
  refine Fin.cases ?_ (fun l => ?_) j
  · exact PRA.proj 1 _
  · have := PRA.proj (Γ := Γ) l.succ.succ
      (Fin.cases y (Fin.cases (app (iterSym a h) (Fin.cases y xs)) xs))
    simp only [Fin.cases_succ] at this ⊢
    exact this

/-- The function symbol of a term, applied to arguments, is the translation of
the term with the arguments substituted. -/
theorem code_eval (t : Tm k) :
    ∀ {n : ℕ} (ts : Fin k → PTm n) (Γ : List (Fm PTm n)),
      Γ ⊢[PRAAx] app (code t) ts ≐ Syn.subst ts (tau t) := by
  induction t with
  | var i => intro n ts Γ; exact PRA.proj i ts
  | zero =>
    intro n ts Γ
    have e : Syn.subst ts (tau (Tm.zero : Tm _)) = PTm.zero := PTm.subst_zero ts
    rw [e]
    exact Prf.eqTrans (PRA.comp PR.zero Fin.elim0 ts) (congr PR.zero (fun j => j.elim0))
  | succ t ih =>
    intro n ts Γ
    exact Prf.eqTrans (PRA.comp PR.succ (fun _ => code t) ts)
      (congr PR.succ (fun _ => ih ts Γ))
  | iter c a h ihc _ _ =>
    intro n ts Γ
    refine Prf.eqTrans (PRA.comp _ _ ts) ?_
    refine congr _ (fun j => ?_)
    refine Fin.cases ?_ (fun l => ?_) j
    · exact ihc ts Γ
    · have := PRA.proj (Γ := Γ) l ts
      simp only [Fin.cases_succ] at this ⊢
      exact this

/-! ### Extensionality of the simulated iterator -/

theorem subst_inst_up (t : PTm m) (σ : Fin k → PTm m) :
    (fun i => Syn.subst (Fin.cases t Syn.var : Fin (m + 1) → PTm m) (Syn.up σ i))
      = Fin.cases t σ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Syn.shift, Syn.subst_subst]

theorem subst_cases_up (s : PTm (m + 1)) (σ : Fin k → PTm m) :
    (fun i => Syn.subst (Fin.cases s (fun j => Syn.var j.succ) : Fin (m + 1) → PTm (m + 1))
        (Syn.up σ i))
      = Fin.cases s (fun j => Syn.shift (σ j)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
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
  have key : [] ⊢[PRAAx]
      Fm.all (app (iterSym a' h') Syn.var ≐ app (iterSym a h) (Syn.up σ)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · show [] ⊢[PRAAx] app (iterSym a' h') (Fin.cases PTm.zero Syn.var)
        ≐ app (iterSym a h)
          (fun i => Syn.subst (Fin.cases PTm.zero Syn.var : Fin (m + 1) → PTm m) (Syn.up σ i))
      rw [subst_inst_up]
      exact Prf.eqTrans (iterSym_zero a' h' Syn.var)
        (Prf.eqTrans ha (Prf.eqSymm (iterSym_zero a h σ)))
    · have e5 : (Fin.cases (Syn.var 0) (fun i => Syn.var i.succ) : Fin (m + 1) → PTm (m + 1))
          = Syn.var := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      have hL := iterSym_succ
        (Γ := [app (iterSym a' h') Syn.var ≐ app (iterSym a h) (Syn.up σ)])
        a' h' (Syn.var 0) (fun i => Syn.var i.succ)
      rw [e5] at hL
      have hR := iterSym_succ
        (Γ := [app (iterSym a' h') Syn.var ≐ app (iterSym a h) (Syn.up σ)])
        a h (Syn.var 0) (fun j => Syn.shift (σ j))
      have hM : [app (iterSym a' h') Syn.var ≐ app (iterSym a h) (Syn.up σ)] ⊢[PRAAx]
          app h' (Fin.cases (app (iterSym a' h') Syn.var) (fun i => Syn.var i.succ))
            ≐ app h (fun i => Syn.subst
                (Fin.cases (app (iterSym a' h') Syn.var) (fun j => Syn.var j.succ)
                  : Fin (m + 1) → PTm (m + 1)) (Syn.up σ i)) :=
        (hh.subst (Fin.cases (app (iterSym a' h') Syn.var) (fun i => Syn.var i.succ))).ofNil
      rw [subst_cases_up] at hM
      show [app (iterSym a' h') Syn.var ≐ app (iterSym a h) (Syn.up σ)] ⊢[PRAAx]
        app (iterSym a' h') (Fin.cases (PTm.succ (Syn.var 0)) (fun i => Syn.var i.succ))
          ≐ app (iterSym a h) (fun i => Syn.subst
              (Fin.cases (PTm.succ (Syn.var 0)) (fun j => Syn.var j.succ)
                : Fin (m + 1) → PTm (m + 1)) (Syn.up σ i))
      rw [subst_cases_up]
      refine Prf.eqTrans hL (Prf.eqTrans hM (Prf.eqTrans (congr h (fun i => ?_)) (Prf.eqSymm hR)))
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Prf.hyp0
      · simp only [Fin.cases_succ]
        exact Prf.eqRefl _
  have h1 : [] ⊢[PRAAx] app (iterSym a' h') (Fin.cases t Syn.var)
      ≐ app (iterSym a h)
        (fun i => Syn.subst (Fin.cases t Syn.var : Fin (m + 1) → PTm m) (Syn.up σ i)) :=
    Prf.allE t key
  rwa [subst_inst_up] at h1

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
  · have e1 : Syn.up ρ j.succ = Syn.shift (ρ j) := Syn.up_succ ρ j
    rw [e1]
    have h1 := hρ j k (fun l => r l.succ)
    have h3 : [] ⊢[PRAAx]
        Syn.subst (fun l => (Syn.var (r l) : PTm k)) (tau (Syn.shift (ρ j)))
          ≐ Syn.subst (fun l => (Syn.var (r l) : PTm k)) (Syn.shift (tau (ρ j))) :=
      (hρ j (m + 1) Fin.succ).subst (fun l => (Syn.var (r l) : PTm k))
    rw [Syn.subst_shift] at h3
    have e2 : Syn.subst (fun l => (Syn.var (r l) : Tm k)) (Syn.shift (ρ j))
        = Syn.subst (fun l => (Syn.var (r l.succ) : Tm k)) (ρ j) := Syn.subst_shift _ _
    rw [e2]
    exact Prf.eqTrans h1 (Prf.eqSymm h3)

theorem tau_subst_of_good (t : Tm n) :
    ∀ {m : ℕ} (ρ : Fin n → Tm m), Good ρ →
      ([] ⊢[PRAAx] tau (Syn.subst ρ t) ≐ Syn.subst (fun i => tau (ρ i)) (tau t)) := by
  induction t with
  | var i => intro m ρ _; exact Prf.eqRefl _
  | zero =>
    intro m ρ _
    have e : Syn.subst (fun i => tau (ρ i)) (tau (Tm.zero : Tm _)) = PTm.zero :=
      PTm.subst_zero _
    rw [e]
    exact Prf.eqRefl _
  | succ t ih =>
    intro m ρ hρ
    show [] ⊢[PRAAx] PTm.succ (tau (Syn.subst ρ t))
      ≐ PTm.succ (Syn.subst (fun i => tau (ρ i)) (tau t))
    exact congr PR.succ (fun _ => ih ρ hρ)
  | iter c a h ihc iha ihh =>
    intro m ρ hρ
    have e : (fun i => Syn.subst (fun i => tau (ρ i))
        ((Fin.cases (tau c) Syn.var : Fin (_ + 1) → PTm _) i))
        = Fin.cases (Syn.subst (fun i => tau (ρ i)) (tau c)) (fun i => tau (ρ i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [Tm.subst_iter]
    show [] ⊢[PRAAx]
      app (iterSym (code (Syn.subst ρ a)) (code (Syn.subst (Syn.up ρ) h)))
          (Fin.cases (tau (Syn.subst ρ c)) Syn.var)
        ≐ app (iterSym (code a) (code h))
          (fun i => Syn.subst (fun i => tau (ρ i))
            ((Fin.cases (tau c) Syn.var : Fin (_ + 1) → PTm _) i))
    rw [e]
    refine Prf.eqTrans
      (iterSym_ext (a := code a) (h := code h) (σ := fun i => tau (ρ i)) ?_ ?_ _)
      (congr _ (fun i => ?_))
    · have h1 := code_eval (Syn.subst ρ a) Syn.var ([] : List (Fm PTm m))
      rw [Syn.subst_id] at h1
      exact Prf.eqTrans h1 (Prf.eqTrans (iha ρ hρ) (Prf.eqSymm (code_eval a _ _)))
    · have h1 := code_eval (Syn.subst (Syn.up ρ) h) Syn.var ([] : List (Fm PTm (m + 1)))
      rw [Syn.subst_id] at h1
      refine Prf.eqTrans h1 (Prf.eqTrans (ihh (Syn.up ρ) hρ.up) ?_)
      refine Prf.eqTrans (Prf.eqSymm (code_eval h _ _)) (congr _ (fun i => ?_))
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Prf.eqRefl _
      · simp only [Syn.up_succ]
        exact hρ j (m + 1) Fin.succ
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact ihc ρ hρ
      · simp only [Fin.cases_succ]
        exact Prf.eqRefl _

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
  have h3 := tau_subst (inst (Tm.iter c a h)) h
  have e : (fun i => tau (inst (Tm.iter c a h) i))
      = Fin.cases (tau (Tm.iter c a h)) Syn.var := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [e] at h3
  exact Prf.eqTrans h1 (Prf.eqTrans h2 (Prf.eqSymm h3))

theorem ax_sep :
    [] ⊢[PRAAx] ((PTm.zero : PTm 0) ≐ PTm.succ PTm.zero) ⟶ Fm.bot :=
  Prf.impI (Prf.impE (PRA.succNeZero _) (Prf.eqSymm Prf.hyp0))

/-- The predecessor function symbol. -/
def pd : PR 1 := .prec .zero (.proj 0)

theorem pd_succ (y : PTm n) : Γ ⊢[PRAAx] app pd (fun _ => PTm.succ y) ≐ y := by
  have e : (fun _ : Fin 1 => PTm.succ y) = Fin.cases (PTm.succ y) Fin.elim0 := by
    funext i
    refine Fin.cases ?_ (fun j => j.elim0) i
    rfl
  rw [e]
  exact Prf.eqTrans (PRA.precSucc PR.zero (PR.proj 0) y Fin.elim0) (PRA.proj 0 _)

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

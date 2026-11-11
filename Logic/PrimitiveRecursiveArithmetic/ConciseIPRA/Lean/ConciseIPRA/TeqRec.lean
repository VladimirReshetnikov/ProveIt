import ConciseIPRA.TeqPair

/-!
# Primitive recursion in `T_eq`

Primitive recursion is a derived binder of `T_eq`.  For a base `a` and a step
`g` with two bound variables (the counter and the previous value),

  `prc c a g = psnd (I(c, pair 0 a; u. pair (S (pfst u)) g[pfst u, psnd u]))`.

The iterator carries the pair of the counter and the value.  One equation
induction shows that the first component of the accumulator is the count, and
the recursion equations follow:

  `prc 0 a g = a`,  `prc (S c) a g = g[c, prc c a g]`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

namespace Syn

variable {T : ℕ → Type} [Syn T]

theorem subst_repl_var_succ (s : T (n + 1)) :
    (fun i : Fin n => subst (repl s) (var i.succ : T (n + 1))) = fun i => var i.succ := by
  funext i; simp

/-- Weakening under a binder is unaffected by replacing the outer variable. -/
theorem subst_up_repl_up_shift (s : T (n + 1)) (h : T (n + 1)) :
    subst (up (repl s)) (subst (up (fun i => var i.succ)) h)
      = subst (up (fun i => var i.succ)) h := by
  rw [subst_subst, up_comp, subst_repl_var_succ]

/-- Weakening under two binders is unaffected by replacing the outer variable. -/
theorem subst_up_up_repl_up_up_shift (s : T (n + 1)) (h : T (n + 2)) :
    subst (up (up (repl s))) (subst (up (up (fun i => var i.succ))) h)
      = subst (up (up (fun i => var i.succ))) h := by
  rw [subst_subst, up_comp, up_comp, subst_repl_var_succ]

end Syn

/-- The substitution feeding the step of a recursion from the accumulator:
the counter, the previous value, and the parameters. -/
def Tm.recσ : Fin (n + 2) → Tm (n + 1) :=
  Fin.cases (Tm.pfst (Syn.var 0)) (Fin.cases (Tm.psnd (Syn.var 0)) (fun i => Syn.var i.succ))

/-- The step of the iterator simulating a recursion. -/
def Tm.recStep (g : Tm (n + 2)) : Tm (n + 1) :=
  Tm.pair (Tm.succ (Tm.pfst (Syn.var 0))) (Syn.subst Tm.recσ g)

/-- The accumulator of a recursion: the pair of the counter and the value. -/
def Tm.recAcc (c a : Tm n) (g : Tm (n + 2)) : Tm n :=
  Tm.iter c (Tm.pair Tm.zero a) (Tm.recStep g)

/-- Primitive recursion `R(c, a; y p. g)`. -/
def Tm.prc (c a : Tm n) (g : Tm (n + 2)) : Tm n := Tm.psnd (Tm.recAcc c a g)

theorem Tm.subst_recσ (σ : Fin n → Tm m) :
    (fun j => Syn.subst (Syn.up σ) (Tm.recσ j))
      = fun j => Syn.subst Tm.recσ (Syn.up (Syn.up σ) j) := by
  have e : (fun l : Fin m => (Tm.recσ l.succ.succ : Tm (m + 1))) = fun l => var l.succ := by
    funext l; simp [Tm.recσ]
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j
  · simp [Tm.recσ]
  · simp [Tm.recσ]
  · have e1 : Syn.subst (Syn.up σ) (Tm.recσ i.succ.succ) = shift (σ i) := by
      simp [Tm.recσ]
    have e2 : Syn.subst Tm.recσ (Syn.up (Syn.up σ) i.succ.succ) = shift (σ i) := by
      rw [up_succ, up_succ, subst_shift, subst_shift, e]
      rfl
    rw [e1, e2]

@[simp] theorem Tm.subst_prc (σ : Fin n → Tm m) (c a : Tm n) (g : Tm (n + 2)) :
    Syn.subst σ (Tm.prc c a g)
      = Tm.prc (Syn.subst σ c) (Syn.subst σ a) (Syn.subst (Syn.up (Syn.up σ)) g) := by
  unfold Tm.prc Tm.recAcc Tm.recStep
  simp only [Tm.subst_psnd, Tm.subst_iter, Tm.subst_pair, Tm.subst_zero, Tm.subst_succ,
    Tm.subst_pfst, Syn.subst_var, Syn.up_zero, Syn.subst_subst]
  rw [Tm.subst_recσ]

theorem Tm.subst_inst_recStep (v : Tm n) (g : Tm (n + 2)) :
    Syn.subst (inst v) (Tm.recStep g)
      = Tm.pair (Tm.succ (Tm.pfst v))
          (Syn.subst (Fin.cases (Tm.pfst v) (Fin.cases (Tm.psnd v) Syn.var)) g) := by
  have e : (fun j => Syn.subst (inst v) (Tm.recσ j))
      = (Fin.cases (Tm.pfst v) (Fin.cases (Tm.psnd v) Syn.var) : Fin (n + 2) → Tm n) := by
    funext j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j <;> simp [Tm.recσ]
  simp only [Tm.recStep, Tm.subst_pair, Tm.subst_succ, Tm.subst_pfst, Syn.subst_var,
    Syn.inst_zero, Syn.subst_subst, e]

namespace Q

variable {Γ : List (Fm Tm n)}

/-- A step of the accumulator increments its first component. -/
theorem pfst_app_step (R : Tm (n + 1)) (x : Q Γ) :
    pfst (app (Tm.pair (Tm.succ (Tm.pfst (var 0))) R) x) = succ (pfst x) := by
  induction x using Q.ind with | _ a
  simp [app_mk]

/-- The first component of the accumulator is the count. -/
theorem pfst_iterate_step (R : Tm (n + 1)) (c a : Q Γ) :
    pfst (iterate (Tm.pair (Tm.succ (Tm.pfst (var 0))) R) c (pair 0 a)) = c := by
  induction c using Q.ind with | _ c
  induction a using Q.ind with | _ a
  have h := eqInd (Γ := Γ)
    (Tm.pfst (Tm.iter (var 0) (Tm.pair Tm.zero (shift a))
      (Tm.pair (Tm.succ (Tm.pfst (var 0))) (Syn.subst (up (fun i => var i.succ)) R))))
    (var 0)
    (by simp [mk_iter])
    (fun ih => by
      simp [mk_iter] at ih
      simp [mk_iter, Syn.subst_up_repl_up_shift, pfst_app_step, ih]) c
  simpa [mk_iter, Syn.subst_up_inst_up_shift] using h

theorem pfst_recAcc (c a : Tm n) (g : Tm (n + 2)) :
    mk Γ (Tm.pfst (Tm.recAcc c a g)) = mk Γ c :=
  pfst_iterate_step (Γ := Γ) (Syn.subst Tm.recσ g) (mk Γ c) (mk Γ a)

/-- Primitive recursion at zero. -/
theorem prc_zero (a : Tm n) (g : Tm (n + 2)) : Γ ⊢[TeqAx] Tm.prc Tm.zero a g ≐ a := by
  refine exact ?_
  show psnd (iterate (Tm.recStep g) 0 (pair 0 (mk Γ a))) = mk Γ a
  rw [iterate_zero, psnd_pair]

/-- Primitive recursion at a successor. -/
theorem prc_succ (c a : Tm n) (g : Tm (n + 2)) :
    Γ ⊢[TeqAx] Tm.prc (Tm.succ c) a g
      ≐ Syn.subst (Fin.cases c (Fin.cases (Tm.prc c a g) Syn.var)) g := by
  refine exact ?_
  have h1 : mk Γ (Tm.prc (Tm.succ c) a g)
      = psnd (mk Γ (Syn.subst (inst (Tm.recAcc c a g)) (Tm.recStep g))) := by
    show psnd (iterate (Tm.recStep g) (succ (mk Γ c)) (pair 0 (mk Γ a))) = _
    rw [iterate_succ]
    rfl
  rw [h1, Tm.subst_inst_recStep, mk_pair, psnd_pair]
  refine sound (Prf.eqCongr g (fun j => ?_))
  refine Fin.cases ?_ (fun j => ?_) j
  · exact exact (pfst_recAcc c a g)
  · simp only [Fin.cases_succ]
    exact Prf.eqRefl _

end Q

end LeanProofs.ConciseIPRA

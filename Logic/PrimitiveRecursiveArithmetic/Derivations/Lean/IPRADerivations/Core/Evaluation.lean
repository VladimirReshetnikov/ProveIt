import IPRADerivations.Core.Basic

/-!
# Evaluation of closed primitive-recursive terms

Every closed instance of a primitive-recursive symbol is provably equal to the numeral of its value:
the defining equations of `iPRA` suffice, unrolled finitely many times. With the Lean-side evaluator
`PR.ev : PR k → (Fin k → ℕ) → ℕ` (zero, successor, projection, composition, and recursion on the
first argument):

* `eval_app`: `app f (num ∘ a) ≐ num (ev f a)` for every symbol `f` and arguments `a`, by structural
  recursion on `f`; for `prec f g` the recursion argument is unrolled by a meta-level induction using
  `precZero` and `precSucc`;
* `PTm.ev`, `eval_term`: a term with its variables valued by numerals, `t[num ∘ ρ] ≐ num (ev t ρ)`;
* `eval_eq`: two terms with the same value are provably equal at those numerals.

This is the finite-computation tool: any closed equation whose two sides compute to the same number is
derivable, uniformly in the context.
-/

namespace LeanProofs.ConciseIPRA

namespace PR

/-- The standard value of a primitive-recursive symbol. -/
def ev : {k : ℕ} → PR k → (Fin k → ℕ) → ℕ
  | _, .zero, _ => 0
  | _, .succ, a => a 0 + 1
  | _, .proj i, a => a i
  | _, .comp f gs, a => ev f (fun j => ev (gs j) a)
  | _, PR.prec f g, a =>
      Nat.rec (motive := fun _ => ℕ) (ev f (Fin.tail a))
        (fun y r => ev g (Fin.cons y (Fin.cons r (Fin.tail a)))) (a 0)

end PR

namespace PTm

/-- The value of a term under a valuation of its variables. -/
def ev {n : ℕ} (ρ : Fin n → ℕ) : PTm n → ℕ
  | var i => ρ i
  | app f ts => PR.ev f (fun i => ev ρ (ts i))

end PTm

end LeanProofs.ConciseIPRA

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The recursion unrolled at a numeral recursion argument. -/
theorem evalRec {k : ℕ} (f : PR k) (g : PR (k + 2))
    (hf : ∀ a : Fin k → ℕ, Γ ⊢[PRAAx] app f (fun i => num (a i)) ≐ num (PR.ev f a))
    (hg : ∀ a : Fin (k + 2) → ℕ, Γ ⊢[PRAAx] app g (fun i => num (a i)) ≐ num (PR.ev g a))
    (a' : Fin k → ℕ) (y : ℕ) :
    Γ ⊢[PRAAx] app (PR.prec f g) (Fin.cases (num y) (fun i => num (a' i))) ≐
      num (PR.ev (PR.prec f g) (Fin.cons y a')) := by
  induction y with
  | zero =>
    refine (PRA.precZero f g _).eqTrans ?_
    have e : PR.ev (PR.prec f g) (Fin.cons 0 a') = PR.ev f a' := by simp [PR.ev]
    rw [e]; exact hf a'
  | succ y ih =>
    refine (PRA.precSucc f g (num y) _).eqTrans ?_
    have e : PR.ev (PR.prec f g) (Fin.cons (y + 1) a') =
        PR.ev g (Fin.cons y (Fin.cons (PR.ev (PR.prec f g) (Fin.cons y a')) a')) := by simp [PR.ev]
    rw [e]
    refine (congrApp g (us := fun i => num ((Fin.cons y (Fin.cons (PR.ev (PR.prec f g) (Fin.cons y a')) a') :
      Fin (k + 2) → ℕ) i)) ?_).eqTrans (hg _)
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact .eqRefl _
    · refine Fin.cases ?_ (fun l => ?_) j
      · simpa using ih
      · simpa using (Prf.eqRefl (num (a' l)) : Γ ⊢[PRAAx] num (a' l) ≐ num (a' l))

/-- `eval_app`: a symbol applied to numerals equals the numeral of its value. -/
theorem eval_app : ∀ {k : ℕ} (f : PR k) (a : Fin k → ℕ),
    Γ ⊢[PRAAx] app f (fun i => num (a i)) ≐ num (PR.ev f a)
  | _, .zero, a => by
    have e : (fun i => num (a i) : Fin 0 → PTm n) = Fin.elim0 := funext fun i => i.elim0
    rw [e]; exact .eqRefl _
  | _, .succ, a => by
    have e : (fun i => num (a i) : Fin 1 → PTm n) = fun _ => num (a 0) := funext fun i => by
      rw [Subsingleton.elim i 0]
    rw [e]; exact .eqRefl _
  | _, .proj i, a => PRA.proj i _
  | _, PR.comp f gs, a =>
    (PRA.comp f gs _).eqTrans ((congrApp f (fun j => eval_app (gs j) a)).eqTrans (eval_app f _))
  | _, PR.prec f g, a => by
    have e : (fun i => num (a i) : Fin _ → PTm n) = Fin.cases (num (a 0)) (fun i => num (Fin.tail a i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
    have e' : a = Fin.cons (a 0) (Fin.tail a) := (Fin.cons_self_tail a).symm
    rw [e]
    have h := evalRec f g (eval_app f) (eval_app g) (Fin.tail a) (a 0)
    rwa [← e'] at h

/-- `eval_term`: a term with numeral-valued variables equals the numeral of its value. -/
theorem eval_term {m : ℕ} (ρ : Fin m → ℕ) : ∀ t : PTm m,
    Γ ⊢[PRAAx] Syn.subst (fun i => num (ρ i)) t ≐ num (PTm.ev ρ t)
  | .var i => .eqRefl _
  | .app f ts => by
    show Γ ⊢[PRAAx] app f (fun i => Syn.subst (fun i => num (ρ i)) (ts i)) ≐ num (PR.ev f (fun i => PTm.ev ρ (ts i)))
    exact (congrApp f (fun j => eval_term ρ (ts j))).eqTrans (eval_app f _)

/-- `eval_eq`: terms with equal values are provably equal at the numerals. -/
theorem eval_eq {m : ℕ} (ρ : Fin m → ℕ) (s t : PTm m) (h : PTm.ev ρ s = PTm.ev ρ t) :
    Γ ⊢[PRAAx] Syn.subst (fun i => num (ρ i)) s ≐ Syn.subst (fun i => num (ρ i)) t :=
  (eval_term ρ s).eqTrans (h ▸ (eval_term ρ t).eqSymm)

/-- Closed terms (no variables): `t ≐ num (ev t)`. -/
theorem eval_closed (t : PTm 0) : ([] : List (Fm PTm 0)) ⊢[PRAAx] t ≐ num (PTm.ev Fin.elim0 t) := by
  have h := eval_term (n := 0) (Γ := []) (Fin.elim0 : Fin 0 → ℕ) t
  have e : Syn.subst (fun i => num ((Fin.elim0 : Fin 0 → ℕ) i)) t = t := by
    have : (fun i => num ((Fin.elim0 : Fin 0 → ℕ) i) : Fin 0 → PTm 0) = Syn.var := funext fun i => i.elim0
    rw [this]; exact Syn.subst_id t
  rwa [e] at h

/-- `eval_ground`: a ground term, written over no variables and substituted into any context, equals
the numeral of its value; `hv` is typically closed by `decide`. -/
theorem eval_ground (t : PTm 0) (v : ℕ) (hv : PTm.ev Fin.elim0 t = v) :
    Γ ⊢[PRAAx] Syn.subst (Fin.elim0 : Fin 0 → PTm n) t ≐ num v := by
  have h := eval_term (Γ := Γ) (Fin.elim0 : Fin 0 → ℕ) t
  have e : (fun i => num ((Fin.elim0 : Fin 0 → ℕ) i) : Fin 0 → PTm n) = Fin.elim0 := funext fun i => i.elim0
  rw [e, hv] at h
  exact h

end LeanProofs.IPRA

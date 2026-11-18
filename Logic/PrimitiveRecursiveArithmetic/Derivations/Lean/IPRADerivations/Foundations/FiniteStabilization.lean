import IPRADerivations.Foundations.IterationFusion
import IPRADerivations.Core.OrderCertificates

/-!
# Finite stabilization of ranked iterations

Packet: `foundations/FINER-iPRA-framework-2026-11-16`, `paper/sections/07_demand_closure.tex`:
Lemma `lem:demand-inflation` ("Inflation and bounded rank"), Theorem `thm:demand-stabilization`
("Finite stabilization", `eq:demand-stable`: `x^{H+1} = x^H`, hence `F(x^H) ≤ x^H`) and the induction of
Theorem `thm:demand-least` ("Least prefixed point").

The state is one number (a packed vector), the update is a unary step term `f`, the iterate is
`IterationFusion.iter f t x = f^t(x)`, and the rank is a unary term `ρ`. The content of
`lem:demand-inflation` enters as the rule `hstep`: at every state `s`, either `f(s) = s` or
`ρ(s) < ρ(f(s))` (a state that changes gains rank; equality of states is decidable).

* `stab`: for every `t`, `x^{t+1} = x^t` or `t + 1 ≤ ρ(x^{t+1})`. This is the invariant of the paper's
  `eq:demand-invariant` without the stored strict count: an iteration that has not stalled has rank at
  least its clock. It is a quantifier-free disjunction, proved by `ind`; no contradiction is used.
* `stable_at` (`eq:demand-stable`): if `ρ(x^{H+1}) ≤ H`, then `x^{H+1} = x^H`. Only the rank bound at time
  `H + 1` is needed.
* `fixed_at`: then `f(x^H) = x^H`, which for `f(x) = x ∨ F(x)` is `F(x^H) ≤ x^H`.
* `stable_after`: a stalled iteration stays stalled, `x^{H+j} = x^H` for every `j`.
* `stable_inflationary`: the case `ρ(s) = s` of a numerical inflationary map, `s ≤ f(s)`.
* `invariant`: a quantifier-free relation `R(s, y)` that holds at `x` and is preserved by `f` holds at
  every iterate; with `R(s, y) = (s ≤ y)` and a prefixed point `y` this is the induction of
  `thm:demand-least`, so `x^H ≤ y`.

The packed-vector instance (componentwise join, rank as a bounded sum, capacities) is not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteStabilization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.ClockedDescent (subst_QF')
open LeanProofs.IPRA.Foundations.IterationFusion
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Stabilization

variable {f ρ : PTm 1}

/-- The invariant at time `t`: stalled, or the rank is at least the clock. -/
abbrev Stab (f ρ : PTm 1) (t x : PTm k) : Fm PTm k :=
  (iter f (succ t) x ≐ iter f t x) ⋎ le (succ t) (app1 ρ (iter f (succ t) x))

/-- A strict step raises the rank above the clock. -/
theorem rank_up {t x : PTm k} (hlow : Γ ⊢[PRAAx] le t (app1 ρ (iter f t x)))
    (h : Γ ⊢[PRAAx] lt (app1 ρ (iter f t x)) (app1 ρ (app1 f (iter f t x)))) :
    Γ ⊢[PRAAx] le (succ t) (app1 ρ (iter f (succ t) x)) := by
  have h' : Γ ⊢[PRAAx] le (succ (app1 ρ (iter f t x))) (app1 ρ (app1 f (iter f t x))) := h
  have c := natEq (congrApp1 ρ (iter_succ (Γ := Γ) f t x))
  ipra_le sl h' + sl hlow using rw [c]; ring

theorem advance
    (hstep : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (s : PTm k),
      Γ ⊢[PRAAx] (app1 f s ≐ s) ⋎ lt (app1 ρ s) (app1 ρ (app1 f s)))
    {t x : PTm k} (hlow : Γ ⊢[PRAAx] le t (app1 ρ (iter f t x))) : Γ ⊢[PRAAx] Stab f ρ t x :=
  .orE (hstep (iter f t x)) (.orI₁ ((iter_succ f t x).eqTrans Prf.hyp0)) (.orI₂ (rank_up hlow.wk Prf.hyp0))

theorem stab_step
    (hstep : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (s : PTm k),
      Γ ⊢[PRAAx] (app1 f s ≐ s) ⋎ lt (app1 ρ s) (app1 ρ (app1 f s)))
    {t x : PTm k} (ih : Γ ⊢[PRAAx] Stab f ρ t x) : Γ ⊢[PRAAx] Stab f ρ (succ t) x := by
  refine .orE ih ?_ ?_
  · exact .orI₁ ((iter_succ f (succ t) x).eqTrans ((congrApp1 f Prf.hyp0).eqTrans (iter_succ f t x).eqSymm))
  · exact advance hstep Prf.hyp0

/-- Variables: `0 = t` (induction), `1 = x`. -/
private theorem stab₀
    (hstep : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (s : PTm k),
      Γ ⊢[PRAAx] (app1 f s ≐ s) ⋎ lt (app1 ρ s) (app1 ρ (app1 f s))) :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] Stab f ρ (var 0) (var 1) := by
  refine ind _ ⟨trivial, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_or, Fm.subst_eq, subst_le, subst_ap2, subst_app1, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact advance hstep (zero_le _)
  · simp only [Fm.subst_or, Fm.subst_eq, subst_le, subst_ap2, subst_app1, Syn.subst_var, Syn.repl_zero,
      repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact stab_step hstep Prf.hyp0

/-- For every `t`: `x^{t+1} = x^t`, or `t + 1 ≤ ρ(x^{t+1})`. -/
theorem stab
    (hstep : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (s : PTm k),
      Γ ⊢[PRAAx] (app1 f s ≐ s) ⋎ lt (app1 ρ s) (app1 ρ (app1 f s)))
    (t x : PTm k) : Γ ⊢[PRAAx] Stab f ρ t x := by
  have h := inst (Γ := Γ) (stab₀ hstep) (![t, x] : Fin 2 → PTm k)
  simpa using h

/-- `eq:demand-stable`: if the rank of `x^{H+1}` is at most `H`, the iteration is stable at time `H`. -/
theorem stable_at
    (hstep : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (s : PTm k),
      Γ ⊢[PRAAx] (app1 f s ≐ s) ⋎ lt (app1 ρ s) (app1 ρ (app1 f s)))
    {x H : PTm k} (hbound : Γ ⊢[PRAAx] le (app1 ρ (iter f (succ H) x)) H) :
    Γ ⊢[PRAAx] iter f (succ H) x ≐ iter f H x :=
  .orE (stab hstep H x) Prf.hyp0 (le_lt_absurd _ hbound.wk Prf.hyp0)

/-- The stable iterate is a fixed point of the step: `f(x^H) = x^H`. -/
theorem fixed_at
    (hstep : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (s : PTm k),
      Γ ⊢[PRAAx] (app1 f s ≐ s) ⋎ lt (app1 ρ s) (app1 ρ (app1 f s)))
    {x H : PTm k} (hbound : Γ ⊢[PRAAx] le (app1 ρ (iter f (succ H) x)) H) :
    Γ ⊢[PRAAx] app1 f (iter f H x) ≐ iter f H x :=
  (iter_succ f H x).eqSymm.eqTrans (stable_at hstep hbound)

end Stabilization

/-! ## A stalled iteration stays stalled -/

section After

variable {f : PTm 1}

theorem after_step {H j x : PTm k} (e : Γ ⊢[PRAAx] iter f (succ H) x ≐ iter f H x)
    (ih : Γ ⊢[PRAAx] iter f (H + j) x ≐ iter f H x) : Γ ⊢[PRAAx] iter f (H + succ j) x ≐ iter f H x :=
  (congrAp2 (rec2 (var 0) (iterStep f)) (add_succ H j) (.eqRefl x)).eqTrans
    ((iter_succ f (H + j) x).eqTrans ((congrApp1 f ih).eqTrans ((iter_succ f H x).eqSymm.eqTrans e)))

/-- Variables: `0 = j` (induction), `1 = H`, `2 = x`. -/
private abbrev afterF (f : PTm 1) : Fm PTm 3 :=
  (iter f (succ (var 1)) (var 2) ≐ iter f (var 1) (var 2)) ⟶
    (iter f (var 1 + var 0) (var 2) ≐ iter f (var 1) (var 2))

private theorem after₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] afterF f := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (congrAp2 (rec2 (var 0) (iterStep f)) (add_zero _) (.eqRefl _))
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero,
      repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (after_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- If `x^{H+1} = x^H`, then `x^{H+j} = x^H` for every `j`. -/
theorem stable_after {H x : PTm k} (e : Γ ⊢[PRAAx] iter f (succ H) x ≐ iter f H x) (j : PTm k) :
    Γ ⊢[PRAAx] iter f (H + j) x ≐ iter f H x := by
  have h := inst (Γ := Γ) (after₀ (f := f)) (![j, H, x] : Fin 3 → PTm k)
  simp at h
  exact .impE h e

end After

/-! ## Numerical inflationary maps -/

theorem app1_var (s : PTm k) : app1 (var 0) s = s := by
  simp [app1]

/-- An inflationary map of numbers, `s ≤ f(s)`, whose iterate at time `H + 1` is at most `H`, is stable at
time `H`: the rank is the state itself. -/
theorem stable_inflationary {f : PTm 1}
    (hinfl : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (s : PTm k), Γ ⊢[PRAAx] le s (app1 f s))
    {x H : PTm k} (hbound : Γ ⊢[PRAAx] le (iter f (succ H) x) H) :
    Γ ⊢[PRAAx] iter f (succ H) x ≐ iter f H x := by
  refine stable_at (ρ := var 0) (fun {k} {Γ} s => ?_) (by rw [app1_var]; exact hbound)
  rw [app1_var, app1_var]
  exact .orE (lt_or_eq_of_le (hinfl s)) (.orI₂ Prf.hyp0) (.orI₁ Prf.hyp0.eqSymm)

/-! ## Invariants of the iteration (`thm:demand-least`) -/

section Invariant

variable {R : Fm PTm 2} {f : PTm 1}

/-- Variables: `0 = t`, `1 = x`, `2 = y`. -/
private def invF (R : Fm PTm 2) (f : PTm 1) : Fm PTm 3 :=
  rel R (var 1) (var 2) ⟶ rel R (iter f (var 0) (var 1)) (var 2)

private theorem inv₀ (hqf : R.QF)
    (hloc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s y : PTm k},
      (Γ ⊢[PRAAx] rel R s y) → (Γ ⊢[PRAAx] rel R (app1 f s) y)) :
    ([] : List (Fm PTm 3)) ⊢[PRAAx] invF R f := by
  refine ind _ ⟨subst_QF' hqf _, subst_QF' hqf _⟩ ?_ ?_
  · simp only [invF, Fm.subst_imp, subst_rel, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero]
    exact .impI (rel_congr R (iter_zero f _).eqSymm (.eqRefl _) Prf.hyp0)
  · simp only [invF, Fm.subst_imp, subst_rel, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [invF R f] ⊢[PRAAx]
        rel R (var 1) (var 2) ⟶ rel R (iter f (var 0) (var 1)) (var 2) :=
      Prf.hyp0
    exact .impI (rel_congr R (iter_succ f _ _).eqSymm (.eqRefl _) (hloc (.impE ih.wk Prf.hyp0)))

/-- A quantifier-free relation `R(s, y)` that holds at `x` and is preserved by the step holds at every
iterate. For `R(s, y) = (s ≤ y)` and `f(s) = s ∨ F(s)` with `F(y) ≤ y`, this is `x^t ≤ y`. -/
theorem invariant (hqf : R.QF)
    (hloc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s y : PTm k},
      (Γ ⊢[PRAAx] rel R s y) → (Γ ⊢[PRAAx] rel R (app1 f s) y))
    {x y : PTm k} (h : Γ ⊢[PRAAx] rel R x y) (t : PTm k) :
    Γ ⊢[PRAAx] rel R (iter f t x) y := by
  have i := inst (Γ := Γ) (inv₀ hqf hloc) (![t, x, y] : Fin 3 → PTm k)
  simp [invF] at i
  exact .impE i h

end Invariant

end LeanProofs.IPRA.Foundations.FiniteStabilization

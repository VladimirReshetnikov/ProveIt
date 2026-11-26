import IPRADerivations.Core.Pairing
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The trace kernel: invariants of primitive-recursive runs

The framework packets compile a loop to a primitive-recursive run and reason about it through a
quantifier-free invariant (`ipra_cbip_framework_2026-11-16`, `ipra_kifc_framework_2026-11-15` and
its later editions, `pcfm_ipra_framework_2026-11-16`, `tapir_ipra_framework_2026-11-16`: the
"trace reflection" or "loop" kernel).

For a step body `step(s, x)` (state `s`, parameter `x`), the run is

  `run 0 s₀ x = s₀`,   `run (k + 1) s₀ x = step(run k s₀ x, x)`.

An invariant is a bit body `inv(s, x)`, read as true when `inv(s, x) = 1`; this is a
quantifier-free formula.

* `run_zero`, `run_succ`: the defining equations;
* `trace_invariant`: if `inv(s₀, x) = 1` and `∀ s, inv(s, x) = 1 → inv(step(s, x), x) = 1`, then
  `inv(run k s₀ x, x) = 1` for every `k`. The preservation hypothesis is an object-level
  statement and may depend on the assumptions of the context;
* `trace_invariant_all`: the same conclusion as a universal statement over `k`;
* `run_add`: `run (j + k) s₀ x = run k (run j s₀ x) x`.

A bounded-formula invariant is covered through its bit (`Foundations/BoundedFormulas`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.TraceInvariant

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The run -/

section Run

variable (step : PTm 2)

/-- The step of the run; variables `0 = k`, `1 = r_k`, `2 = ⟨s₀, x⟩`. -/
abbrev runStep : PTm 3 := Syn.subst ![var 1, sndT (var 2)] step
abbrev runF : PR 2 := rec2 (fstT (var 0)) (runStep step)
/-- `run k s₀ x`: the state after `k` steps from `s₀`. -/
abbrev run (k s₀ x : PTm n) : PTm n := ap2 (runF step) k (pairT s₀ x)

theorem run_zero (s₀ x : PTm n) : Γ ⊢[PRAAx] run step zero s₀ x ≐ s₀ := by
  have h := rec2_zero (Γ := Γ) (fstT (var 0)) (runStep step) (pairT s₀ x)
  simp only [subst_fstT, Syn.subst_var, Matrix.cons_val_zero] at h
  exact h.eqTrans (fst_pair _ _)

theorem run_succ (k s₀ x : PTm n) :
    Γ ⊢[PRAAx] run step (succ k) s₀ x ≐ inst2 step (run step k s₀ x) x := by
  have h := rec2_succ (Γ := Γ) (fstT (var 0)) (runStep step) k (pairT s₀ x)
  have e : Syn.subst ![k, ap2 (runF step) k (pairT s₀ x), pairT s₀ x] (runStep step) =
      inst2 step (run step k s₀ x) (sndT (pairT s₀ x)) := by
    simp only [inst2, Syn.subst_subst]
    congr 1; funext j; fin_cases j <;> simp
  rw [e] at h
  exact h.eqTrans (congrInst2 step (.eqRefl _) (snd_pair _ _))

end Run

/-! ## Substitution lemmas under a binder -/

theorem subst_up_shift' {m k : ℕ} (σ : Fin m → PTm k) (t : PTm m) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

theorem subst_repl_shift' {m : ℕ} (s : PTm (m + 1)) (t : PTm m) :
    Syn.subst (Syn.repl s) (Syn.shift t) = Syn.shift t := by
  rw [Syn.subst_shift]; simp [Syn.shift]

/-! ## Preservation -/

section Invariant

variable (step inv : PTm 2)

/-- `∀ s, inv(s, x) = 1 → inv(step(s, x), x) = 1`. -/
abbrev presF (x : PTm n) : Fm PTm n :=
  Fm.all ((inst2 inv (var 0) (Syn.shift x) ≐ one) ⟶
    (inst2 inv (inst2 step (var 0) (Syn.shift x)) (Syn.shift x) ≐ one))

theorem shift_presF (x : PTm n) : Fm.shift (presF step inv x) = presF step inv (Syn.shift x) := by
  simp only [Fm.shift, Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_inst2, Syn.subst_var, Syn.up_zero,
    subst_up_shift', ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rfl

/-- The preservation hypothesis at a state `s`. -/
theorem pres_at {x : PTm n} (h : Γ ⊢[PRAAx] presF step inv x) (s : PTm n) :
    Γ ⊢[PRAAx] (inst2 inv s x ≐ one) ⟶ (inst2 inv (inst2 step s x) x ≐ one) := by
  simpa using Prf.allE s h

/-- The invariant along the run; variable `0 = k`. -/
abbrev invF (s₀ x : PTm n) : Fm PTm (n + 1) :=
  inst2 inv (run step (var 0) (Syn.shift s₀) (Syn.shift x)) (Syn.shift x) ≐ one

/-- An invariant that holds initially and is preserved by one step holds along the whole run. -/
theorem trace_invariant_all {s₀ x : PTm n} (h₀ : Γ ⊢[PRAAx] inst2 inv s₀ x ≐ one)
    (hs : Γ ⊢[PRAAx] presF step inv x) : Γ ⊢[PRAAx] Fm.all (invF step inv s₀ x) := by
  refine PRA.qfInd _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_inst2, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    exact (congrInst2 inv (run_zero step s₀ x) (.eqRefl _)).eqTrans h₀
  · simp only [Fm.subst_eq, subst_inst2, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero,
      subst_repl_shift', ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    have hsh : Γ.map Fm.shift ⊢[PRAAx] presF step inv (Syn.shift x) := by
      have h := hs.shift
      rw [shift_presF] at h
      exact h
    exact (congrInst2 inv (run_succ step (var 0) (Syn.shift s₀) (Syn.shift x)) (.eqRefl _)).eqTrans
      (Prf.impE (pres_at step inv hsh.wk _) Prf.hyp0)

/-- `inv(run k s₀ x, x) = 1` for every `k`. -/
theorem trace_invariant {s₀ x : PTm n} (h₀ : Γ ⊢[PRAAx] inst2 inv s₀ x ≐ one)
    (hs : Γ ⊢[PRAAx] presF step inv x) (k : PTm n) :
    Γ ⊢[PRAAx] inst2 inv (run step k s₀ x) x ≐ one := by
  simpa using Prf.allE k (trace_invariant_all step inv h₀ hs)

end Invariant

/-! ## Composition of runs -/

section Add

variable (step : PTm 2)

/-- Variables: `0 = k`, `1 = j`, `2 = s₀`, `3 = x`. -/
private abbrev addF : Fm PTm 4 :=
  run step (var 1 + var 0) (var 2) (var 3) ≐ run step (var 0) (run step (var 1) (var 2) (var 3)) (var 3)

theorem add_step {j k s₀ x : PTm n}
    (ih : Γ ⊢[PRAAx] run step (j + k) s₀ x ≐ run step k (run step j s₀ x) x) :
    Γ ⊢[PRAAx] run step (j + succ k) s₀ x ≐ run step (succ k) (run step j s₀ x) x :=
  (congrAp2 (runF step) (add_succ j k) (.eqRefl _)).eqTrans
    ((run_succ step (j + k) s₀ x).eqTrans
      ((congrInst2 step ih (.eqRefl _)).eqTrans (run_succ step k (run step j s₀ x) x).eqSymm))

private theorem add₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] addF step := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact (congrAp2 (runF step) (add_zero _) (.eqRefl _)).eqTrans (run_zero step _ _).eqSymm
  · exact add_step step Prf.hyp0

/-- `run (j + k) s₀ x = run k (run j s₀ x) x`. -/
theorem run_add (j k s₀ x : PTm n) :
    Γ ⊢[PRAAx] run step (j + k) s₀ x ≐ run step k (run step j s₀ x) x := by
  have h := inst (Γ := Γ) (add₀ step) (![k, j, s₀, x] : Fin 4 → PTm n)
  simpa using h

end Add

end LeanProofs.IPRA.Foundations.TraceInvariant

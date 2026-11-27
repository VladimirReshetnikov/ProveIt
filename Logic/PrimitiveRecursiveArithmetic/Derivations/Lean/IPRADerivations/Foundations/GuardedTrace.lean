import IPRADerivations.Foundations.TraceReflection

/-!
# Trace reflection with a guarded step

Packets:

* `topology/ipra_topology_framework_2026-11-15`, `paper/sections/05_carrier_theorems.tex`, Theorem `thm:trace`
  ("Finite-trace reflection"): from `I(0, s₀(x), x)` and `t < T(x) ∧ I(t, s, x) → I(t + 1, F(t, s, x), x)`,
  `I(T(x), s(T(x), x), x)`;
* `foundations/ipra_cfp_contract_compiler_2026-11-15`, Theorem "Finite-trace reflection": a base sequent and a
  step sequent "uniformly in `t < N`" give the invariant at `N`.

* `foundations/ipra_finite_observation`, `tex/compiler.tex`, Theorem `thm:safety` ("Finite safety
  compilation"): from the base and the step for `j < H`, `∀ j ≤ H. I(x, j, s_j)`.

In all of them the step is required only below the fuel, unlike `Foundations/TraceReflection`, whose step
obligation is unguarded.

* `guarded_loop`: for a quantifier-free `I(t)` in a context `Γ` and a term `T`: from `Γ ⊢ I(0)` and
  `t < T, I(t), Γ↑ ⊢ I(t + 1)`, `Γ ⊢ I(T)`. The induction is on `t ≤ T → I(t)`.
* `guarded_trace`: for the run `Run(0, u) = init(u)`, `Run(t + 1, u) = step(t, Run(t, u), u)` of
  `Foundations/TraceReflection` and a quantifier-free invariant `Inv(t, s, u)`: from `Inv(0, init(u), u)` and
  the rule `t < fuel(v), Inv(t, s, v) ⊢ Inv(t + 1, step(t, s, v), v)` (at arbitrary terms and hypotheses),
  `Inv(fuel(u), Run(fuel(u), u), u)`;
* `guarded_loop_all`, `guarded_trace_all`: the same conclusions at every stage, `∀ t ≤ T. I(t)` and
  `∀ t ≤ fuel(u). Inv(t, Run(t, u), u)` (the form of `thm:safety`).
-/

namespace LeanProofs.IPRA.Foundations.GuardedTrace

open_ipra exports
open LeanProofs.IPRA.ClockedDescent (subst_QF')
open LeanProofs.IPRA.Foundations.TraceReflection (Run I3 subst_I3 subst_Run run_zero run_succ I3_congr)

variable {n : ℕ}

/-- The guarded loop rule at every stage up to the bound: `∀ t ≤ T. I(t)`. -/
theorem guarded_loop_all {Γ : List (Fm PTm n)} (I : Fm PTm (n + 1)) (hI : I.QF) (T : PTm n)
    (h0 : Γ ⊢[PRAAx] I.subst (Syn.inst zero))
    (hS : (lt (var 0) (Syn.shift T) :: I :: Γ.map Fm.shift) ⊢[PRAAx] I.subst (Syn.repl (succ (var 0)))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift T) ⟶ I) := by
  refine PRA.qfInd _ ⟨le_QF _ _, hI⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact .impI h0.wk
  · simp only [Fm.subst_imp, subst_le, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
    refine .impI ?_
    have hk : (le (succ (var 0)) (Syn.shift T) :: (le (var 0) (Syn.shift T) ⟶ I) :: Γ.map Fm.shift)
        ⊢[PRAAx] le (succ (var 0)) (Syn.shift T) := Prf.hyp0
    have hJ : (le (succ (var 0)) (Syn.shift T) :: (le (var 0) (Syn.shift T) ⟶ I) :: Γ.map Fm.shift)
        ⊢[PRAAx] (le (var 0) (Syn.shift T) ⟶ I) := Prf.hyp1
    have hi := Prf.impE hJ (le_trans (le_succ_self _) hk)
    exact Prf.impE (Prf.impE (Prf.impI (Prf.impI hS)).wk.wk hi) hk

/-- A loop rule whose step is assumed only below the bound `T`. -/
theorem guarded_loop {Γ : List (Fm PTm n)} (I : Fm PTm (n + 1)) (hI : I.QF) (T : PTm n)
    (h0 : Γ ⊢[PRAAx] I.subst (Syn.inst zero))
    (hS : (lt (var 0) (Syn.shift T) :: I :: Γ.map Fm.shift) ⊢[PRAAx] I.subst (Syn.repl (succ (var 0)))) :
    Γ ⊢[PRAAx] I.subst (Syn.inst T) := by
  have hall := guarded_loop_all I hI T h0 hS
  have a := Prf.allE T hall
  simp only [Fm.subst_imp, subst_le, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at a
  exact .impE a (le_refl T)

theorem shift_at (β : PTm 1) (b : PTm n) : Syn.shift (inst1 β b) = inst1 β (Syn.shift b) := by
  simp [Syn.shift]

section Trace

variable {init : PTm 1} {step : PTm 3} {fuel : PTm 1} {Inv : Fm PTm 3}

/-- One guarded step along the run. -/
theorem run_step
    (hstep : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (t s v : PTm k), (Θ ⊢[PRAAx] lt t (inst1 fuel v)) →
      (Θ ⊢[PRAAx] I3 Inv t s v) → (Θ ⊢[PRAAx] I3 Inv (succ t) (Syn.subst ![t, s, v] step) v))
    {k : ℕ} {Θ : List (Fm PTm k)} {t v : PTm k} (hg : Θ ⊢[PRAAx] lt t (inst1 fuel v))
    (hi : Θ ⊢[PRAAx] I3 Inv t (Run init step t v) v) :
    Θ ⊢[PRAAx] I3 Inv (succ t) (Run init step (succ t) v) v :=
  I3_congr (run_succ t v).eqSymm (hstep t _ v hg hi)

/-- Trace reflection with the step assumed only for `t < fuel(v)`. -/
theorem guarded_trace (hqf : Inv.QF)
    (hstep : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (t s v : PTm k), (Θ ⊢[PRAAx] lt t (inst1 fuel v)) →
      (Θ ⊢[PRAAx] I3 Inv t s v) → (Θ ⊢[PRAAx] I3 Inv (succ t) (Syn.subst ![t, s, v] step) v))
    {Δ : List (Fm PTm n)} (u : PTm n) (hbase : Δ ⊢[PRAAx] I3 Inv zero (Syn.subst ![u] init) u) :
    Δ ⊢[PRAAx] I3 Inv (inst1 fuel u) (Run init step (inst1 fuel u) u) u := by
  have h0 : Δ ⊢[PRAAx]
      (I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u)).subst (Syn.inst zero) := by
    simp only [subst_I3, Syn.subst_var, Syn.inst_zero, subst_Run, Syn.subst_shift, Syn.inst, Fin.cases_succ,
      Syn.subst_id, ConciseIPRA.PTm.subst_zero, Fin.cases_zero]
    exact I3_congr (run_zero u).eqSymm hbase
  have hS : (lt (var 0) (Syn.shift (inst1 fuel u)) ::
        I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u) :: Δ.map Fm.shift) ⊢[PRAAx]
      (I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u)).subst
        (Syn.repl (succ (var 0))) := by
    rw [shift_at]
    simp only [subst_I3, Syn.subst_var, Syn.repl_zero, subst_Run, Syn.subst_shift, Syn.repl, Fin.cases_succ,
      Syn.subst_id, ConciseIPRA.PTm.subst_succ, Fin.cases_zero]
    exact run_step hstep Prf.hyp0 Prf.hyp1
  have g := guarded_loop (I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u))
    (subst_QF' hqf _) (inst1 fuel u) h0 hS
  simpa only [subst_I3, Syn.subst_var, Syn.inst_zero, subst_Run, Syn.subst_shift, Syn.inst, Fin.cases_succ,
    Syn.subst_id, Fin.cases_zero] using g

/-- Trace reflection at every stage up to the fuel: `∀ t ≤ fuel(u). Inv(t, Run(t, u), u)`
(`foundations/ipra_finite_observation`, `thm:safety`, "Finite safety compilation"). -/
theorem guarded_trace_all (hqf : Inv.QF)
    (hstep : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (t s v : PTm k), (Θ ⊢[PRAAx] lt t (inst1 fuel v)) →
      (Θ ⊢[PRAAx] I3 Inv t s v) → (Θ ⊢[PRAAx] I3 Inv (succ t) (Syn.subst ![t, s, v] step) v))
    {Δ : List (Fm PTm n)} (u : PTm n) (hbase : Δ ⊢[PRAAx] I3 Inv zero (Syn.subst ![u] init) u) :
    Δ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift (inst1 fuel u)) ⟶
      I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u)) := by
  have h0 : Δ ⊢[PRAAx]
      (I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u)).subst (Syn.inst zero) := by
    simp only [subst_I3, Syn.subst_var, Syn.inst_zero, subst_Run, Syn.subst_shift, Syn.inst, Fin.cases_succ,
      Syn.subst_id, ConciseIPRA.PTm.subst_zero, Fin.cases_zero]
    exact I3_congr (run_zero u).eqSymm hbase
  have hS : (lt (var 0) (Syn.shift (inst1 fuel u)) ::
        I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u) :: Δ.map Fm.shift) ⊢[PRAAx]
      (I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u)).subst
        (Syn.repl (succ (var 0))) := by
    rw [shift_at]
    simp only [subst_I3, Syn.subst_var, Syn.repl_zero, subst_Run, Syn.subst_shift, Syn.repl, Fin.cases_succ,
      Syn.subst_id, ConciseIPRA.PTm.subst_succ, Fin.cases_zero]
    exact run_step hstep Prf.hyp0 Prf.hyp1
  exact guarded_loop_all (I3 Inv (var 0) (Run init step (var 0) (Syn.shift u)) (Syn.shift u))
    (subst_QF' hqf _) (inst1 fuel u) h0 hS

end Trace

end LeanProofs.IPRA.Foundations.GuardedTrace

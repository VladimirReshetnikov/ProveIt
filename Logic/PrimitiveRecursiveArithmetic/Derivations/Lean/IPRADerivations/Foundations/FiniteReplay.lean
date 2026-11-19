import IPRADerivations.Foundations.GuardedTrace

/-!
# Finite replay

Packet: `foundations/ipra_framework`, `paper/sections/03_representations.tex`, Lemma `lem:replay`
("Finite replay"): "If two input tables agree on every query recorded in a valid trace of `T` steps, the
same trace of states, branches, and output is obtained from the second table for those `T` steps."

A machine that consults an input table is a step term in which the table is built in; two tables give two
step terms `step₁(i, s, u)`, `step₂(i, s, u)` with the same initial state `init(u)`. The runs are those of
`Foundations/TraceReflection`, `Run(0, u) = init(u)`, `Run(i + 1, u) = step(i, Run(i, u), u)`.

* `replay`: if the two steps agree on the states of the first run below `T`,
  `∀ i < T. step₁(i, Run₁(i, u), u) = step₂(i, Run₁(i, u), u)`, then the two runs coincide up to `T`:
  `∀ t ≤ T. Run₁(t, u) = Run₂(t, u)`.
* `replay_at`: the instance at a stage `t ≤ T`; anything computed from the state (branch, output) is then
  equal by congruence.

The invariant is the equation between the two states, and the step is required only below `T`, so the
induction is the guarded loop of `Foundations/GuardedTrace`. The agreement hypothesis is used only at the
states that the first run actually visits.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteReplay

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.TraceReflection (Run subst_Run run_zero run_succ)
open LeanProofs.IPRA.Foundations.GuardedTrace (guarded_loop_all)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)} {init : PTm 1} {step₁ step₂ : PTm 3}

/-- One replayed step: equal states and agreement of the steps at the first state give equal next
states. -/
theorem replay_step {t u : PTm n}
    (hag : Γ ⊢[PRAAx] Syn.subst ![t, Run init step₁ t u, u] step₁ ≐
      Syn.subst ![t, Run init step₁ t u, u] step₂)
    (ih : Γ ⊢[PRAAx] Run init step₁ t u ≐ Run init step₂ t u) :
    Γ ⊢[PRAAx] Run init step₁ (succ t) u ≐ Run init step₂ (succ t) u := by
  have c : Γ ⊢[PRAAx] Syn.subst ![t, Run init step₁ t u, u] step₂ ≐
      Syn.subst ![t, Run init step₂ t u, u] step₂ :=
    Prf.eqCongr step₂ (fun j => by
      fin_cases j
      · exact .eqRefl t
      · exact ih
      · exact .eqRefl u)
  exact (run_succ t u).eqTrans (hag.eqTrans (c.eqTrans (run_succ t u).eqSymm))

/-- `lem:replay`: two runs whose steps agree on the first run below `T` coincide up to `T`. -/
theorem replay {T u : PTm n}
    (hagree : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift T) ⟶
      (Syn.subst ![var 0, Run init step₁ (var 0) (Syn.shift u), Syn.shift u] step₁ ≐
        Syn.subst ![var 0, Run init step₁ (var 0) (Syn.shift u), Syn.shift u] step₂))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift T) ⟶
      (Run init step₁ (var 0) (Syn.shift u) ≐ Run init step₂ (var 0) (Syn.shift u))) := by
  refine guarded_loop_all
    (Run init step₁ (var 0) (Syn.shift u) ≐ Run init step₂ (var 0) (Syn.shift u)) trivial T ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_zero]
    exact (run_zero u).eqTrans (run_zero u).eqSymm
  · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
      ConciseIPRA.PTm.subst_succ]
    exact replay_step (Prf.impE hagree.allOpen.wk.wk Prf.hyp0) Prf.hyp1

/-- The two runs agree at every stage `t ≤ T`. -/
theorem replay_at {T u t : PTm n}
    (hagree : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift T) ⟶
      (Syn.subst ![var 0, Run init step₁ (var 0) (Syn.shift u), Syn.shift u] step₁ ≐
        Syn.subst ![var 0, Run init step₁ (var 0) (Syn.shift u), Syn.shift u] step₂)))
    (ht : Γ ⊢[PRAAx] le t T) : Γ ⊢[PRAAx] Run init step₁ t u ≐ Run init step₂ t u := by
  have a := Prf.allE t (replay hagree)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at a
  exact Prf.impE a ht

end LeanProofs.IPRA.Foundations.FiniteReplay

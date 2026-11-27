import IPRADerivations.Foundations.StriveCompilation
import IPRADerivations.Foundations.FiniteQueryTable
import IPRADerivations.Foundations.IterationFusion
import IPRADerivations.Core.Header
import IPRADerivations.Core.BoundedSums

/-!
# Reflection of deterministic trace certificates

Packets: `foundations/ipra_finite_use_framework_2026-11-15` and its `_v2` edition,
`sections/04_deterministic.tex`, Proposition `prop:det-cert-reflection` ("Certificate reflection"): for a
fixed trace language iPRA proves `TraceOK(u, c) = 1 → Accept(u, last(c)) = 1` and, with the transitions
checked, `last(c) = Run(u, bound(u))`. "Fold elimination yields each checked field. For equality with the
recomputed run, use quantifier-free induction on the list index with invariant `s_i = Run(u, i)`."

The certificate lists states `s(i, u)`, `i ≤ L`; the run is `Run(u, i) = T^i(s₀)` (`IterationFusion.iter`).
The checked transition fields are the bits `[s(i + 1) = T(s(i))]` (`chkB`), and
`TraceOK = [s(0) = s₀] · ∏_{i<L} [s(i + 1) = T(s(i))] · Accept(s(L))`.

* `trace_run`: checked initialization and transitions give `s(i) = Run(u, i)` for `i ≤ L`, in particular
  `last = s(L) = Run(u, L)`;
* `transitions_of_fold`: `∏_{i<L} chk(i) = 1` gives every transition (fold elimination,
  `FiniteQueryTable.table_entry`);
* `cert_accept`, `cert_run` (`prop:det-cert-reflection`): `TraceOK = 1` gives `Accept(last) = 1` and
  `last = Run(u, L)`.
-/

namespace LeanProofs.IPRA.Foundations.TraceCertificate

open_ipra exports
open LeanProofs.IPRA.Foundations.FiniteQueryTable (table_entry)
open LeanProofs.IPRA.Foundations.StriveCompilation (bits_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (s : PTm 2) (T : PTm 1)

/-- The checked transition field `[s(i + 1) = T(s(i))]`. -/
def chkB : PTm 2 := eqb (Syn.subst ![succ (Syn.var 0), Syn.var 1] s) (Syn.subst ![s] T)

theorem inst2_chkB (i u : PTm n) :
    inst2 (chkB s T) i u = eqb (inst2 s (succ i) u) (app1 T (inst2 s i u)) := by
  simp [inst2, chkB, app1, Syn.subst_subst]
  congr 1
  · congr 1; funext t; fin_cases t <;> simp
  · congr 1; funext t; fin_cases t; simp

/-- The certificate check `[s(0) = s₀] · ∏_{i<L} chk(i) · Accept(s(L))`. -/
abbrev traceOK (Acc : PTm 1) (u L s₀ : PTm n) : PTm n :=
  eqb (inst2 s zero u) s₀ * ap2 (prodF (chkB s T)) L u * app1 Acc (inst2 s L u)

variable {s T}

/-- Checked initialization and transitions: `s(i) = T^i(s₀)` for `i ≤ L`. -/
theorem trace_run {u L s₀ : PTm n} (hinit : Γ ⊢[PRAAx] inst2 s zero u ≐ s₀)
    (htr : Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift L) ⟶
      (inst2 s (succ (Syn.var 0)) (Syn.shift u) ≐ app1 T (inst2 s (Syn.var 0) (Syn.shift u))))) :
    Γ ⊢[PRAAx] inst2 s L u ≐ iter T L s₀ := by
  let P : Fm PTm (n + 1) :=
    inst2 s (Syn.var 0) (Syn.shift u) ≐ iter T (Syn.var 0) (Syn.shift s₀)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst L) := by
    refine qfIndUpTo L trivial ?_ ?_
    · simpa [P] using hinit.eqTrans (iter_zero T s₀).eqSymm
    · ipra_ind_simp [P, subst_inst2, subst_ap2, subst_repl_shift]
      refine .impI ?_
      let Δ := lt (Syn.var 0) (Syn.shift L) :: P :: Γ.map Fm.shift
      have st : Δ ⊢[PRAAx] inst2 s (succ (Syn.var 0)) (Syn.shift u) ≐
          app1 T (inst2 s (Syn.var 0) (Syn.shift u)) := .impE htr.allOpen.wk.wk Prf.hyp0
      exact st.eqTrans ((congrApp1 T Prf.hyp1).eqTrans (iter_succ T _ _).eqSymm)
  simpa [P] using atBound

/-- Fold elimination: a good transition fold gives every transition. -/
theorem transitions_of_fold {u L : PTm n} (h : Γ ⊢[PRAAx] ap2 (prodF (chkB s T)) L u ≐ one) :
    Γ ⊢[PRAAx] Fm.all (lt (Syn.var 0) (Syn.shift L) ⟶
      (inst2 s (succ (Syn.var 0)) (Syn.shift u) ≐ app1 T (inst2 s (Syn.var 0) (Syn.shift u)))) := by
  refine .allI (.impI ?_)
  have h' := h.shift
  simp only [Fm.shift, Fm.subst_eq, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h'
  have hj : (lt (Syn.var 0) (Syn.shift L) :: Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.var 0) (Syn.shift L) := Prf.hyp0
  have hbit : (lt (Syn.var 0) (Syn.shift L) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (inst2 (chkB s T) (Syn.var 0) (Syn.shift u)) one := by
    refine .orE (eqb_cases (inst2 s (succ (Syn.var 0)) (Syn.shift u))
      (app1 T (inst2 s (Syn.var 0) (Syn.shift u)))) ?_ ?_ <;> rw [inst2_chkB]
    · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)
    · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl _)
  have e := table_entry (chkB s T) hbit hj h'.wk
  rw [inst2_chkB] at e
  exact eq_of_eqb e

/-- `prop:det-cert-reflection`, acceptance: `TraceOK = 1 → Accept(last) = 1` (for a bit-valued `Accept`). -/
theorem cert_accept {Acc : PTm 1} {u L s₀ : PTm n}
    (hacc : Γ ⊢[PRAAx] (app1 Acc (inst2 s L u) ≐ zero) ⋎ (app1 Acc (inst2 s L u) ≐ one))
    (hfold : Γ ⊢[PRAAx] (eqb (inst2 s zero u) s₀ * ap2 (prodF (chkB s T)) L u ≐ zero) ⋎
      (eqb (inst2 s zero u) s₀ * ap2 (prodF (chkB s T)) L u ≐ one))
    (h : Γ ⊢[PRAAx] traceOK s T Acc u L s₀ ≐ one) : Γ ⊢[PRAAx] app1 Acc (inst2 s L u) ≐ one :=
  Prf.andE₂ (bits_one hfold hacc h)

/-- `prop:det-cert-reflection`, the run: with the initialization and transitions checked,
`last = s(L) = Run(u, L)`. -/
theorem cert_run {u L s₀ : PTm n} (hinit : Γ ⊢[PRAAx] eqb (inst2 s zero u) s₀ ≐ one)
    (hfold : Γ ⊢[PRAAx] ap2 (prodF (chkB s T)) L u ≐ one) : Γ ⊢[PRAAx] inst2 s L u ≐ iter T L s₀ :=
  trace_run (eq_of_eqb hinit) (transitions_of_fold hfold)

end LeanProofs.IPRA.Foundations.TraceCertificate

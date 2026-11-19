import IPRADerivations.Foundations.GuardedTrace
import IPRADerivations.Foundations.LeastBoundedWitness
import IPRADerivations.Core.Descent

/-!
# Finite dependent choice from seriality

Packet: `foundations/ipra_unified_finitary_framework_2026-11-15`, Theorem `thm:finite-dependent-choice`
("Finite dependent choice is primitive recursive"): from

* (I) `∃ a < B(p, 0). Good(p, 0, a)` and
* (E) `∀ k < h ∀ a. Good(p, k, a) → ∃ b < B(p, k + 1). Good(p, k + 1, b) ∧ Compat(p, k, a, b)`,

"a primitive-recursively constructed compatible good path through levels `0, …, h`". (When a viability
table is available instead of seriality, the path is `Foundations/LeastViablePath`.)

The data are zero tests: `g0(a, x) = 0` for "`a` is good at level `0`" and
`sT(b, ⟨a, ⟨t, x⟩⟩) = 0` for "`b` is good at level `t + 1` and compatible with `a`"; bounds `B0(x)` and
`Bd(level, x)`; a horizon term `fuel(x)`; and a quantifier-free formula `Good(t, a, x)`, with the rules

* `g0(a, x) = 0 ⊢ Good(0, a, x)` and `sT(b, ⟨a, ⟨t, x⟩⟩) = 0 ⊢ Good(t + 1, b, x)`;
* seriality (E): `t < fuel(x), Good(t, a, x) ⊢ ∃ b < Bd(t + 1, x). sT(b, ⟨a, ⟨t, x⟩⟩) = 0`.

The path is the primitive recursion `c(0) = μ a < B0. g0(a) = 0`, `c(t + 1) = μ b < Bd(t + 1). sT(b, ⟨c(t),
⟨t, x⟩⟩) = 0` (`sInit`, `sStep`), a term in `t`.

* `serial_path`: from (I), `∀ t ≤ fuel(x). Good(t, c(t), x)`;
* `serial_good`: the instance at a stage `t ≤ fuel(x)`;
* `serial_edge`: for `t < fuel(x)`, `sT(c(t + 1), ⟨c(t), ⟨t, x⟩⟩) = 0`, i.e. consecutive members are
  compatible, and `c(t + 1) < Bd(t + 1, x)`.

The induction is the guarded loop of `Foundations/GuardedTrace` (the seriality premise is needed only
below the horizon), and every choice is a bounded least search; no choice principle is used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.SerialChoice

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Search (mu)
open LeanProofs.IPRA.Foundations.LeastBoundedWitness (ExW lt_of_exists)
open LeanProofs.IPRA.Foundations.TraceReflection (Run I3 subst_I3 run_succ)
open LeanProofs.IPRA.Foundations.GuardedTrace (guarded_trace_all)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)} {g0 sT Bd : PTm 2} {B0 fuel : PTm 1} {Good : Fm PTm 3}

/-- The first member: the least good candidate of level `0`; variable `0 = x`. -/
def sInit (g0 : PTm 2) (B0 : PTm 1) : PTm 1 := mu g0 (inst1 B0 (var 0)) (var 0)

theorem sInit_at (u : PTm n) : Syn.subst ![u] (sInit g0 B0) = mu g0 (inst1 B0 u) u := by
  simp [sInit]

/-- The next member: the least good compatible successor; variables `0 = t`, `1 = c(t)`, `2 = x`. -/
def sStep (sT Bd : PTm 2) : PTm 3 :=
  mu sT (inst2 Bd (succ (var 0)) (var 2)) (pairT (var 1) (pairT (var 0) (var 2)))

theorem sStep_at (t s v : PTm n) :
    Syn.subst ![t, s, v] (sStep sT Bd) = mu sT (inst2 Bd (succ t) v) (pairT s (pairT t v)) := by
  simp [sStep]

/-- The path `c(t)`. -/
abbrev path (g0 sT Bd : PTm 2) (B0 : PTm 1) (t u : PTm n) : PTm n :=
  Run (sInit g0 B0) (sStep sT Bd) t u

section Path

variable
  (hgood0 : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (a v : PTm k),
    (Θ ⊢[PRAAx] inst2 g0 a v ≐ zero) → (Θ ⊢[PRAAx] I3 Good zero a v))
  (hgoodS : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (t a b v : PTm k),
    (Θ ⊢[PRAAx] inst2 sT b (pairT a (pairT t v)) ≐ zero) → (Θ ⊢[PRAAx] I3 Good (succ t) b v))
  (hser : ∀ {k : ℕ} {Θ : List (Fm PTm k)} (t a v : PTm k), (Θ ⊢[PRAAx] lt t (inst1 fuel v)) →
    (Θ ⊢[PRAAx] I3 Good t a v) → (Θ ⊢[PRAAx] ExW sT (inst2 Bd (succ t) v) (pairT a (pairT t v))))

include hgoodS hser in
/-- One step of the path preserves goodness, below the horizon. -/
theorem serial_step {k : ℕ} {Θ : List (Fm PTm k)} (t s v : PTm k)
    (hlt : Θ ⊢[PRAAx] lt t (inst1 fuel v)) (hg : Θ ⊢[PRAAx] I3 Good t s v) :
    Θ ⊢[PRAAx] I3 Good (succ t) (Syn.subst ![t, s, v] (sStep sT Bd)) v := by
  rw [sStep_at]
  exact hgoodS t s _ v (Prf.andE₂ (lt_of_exists (hser t s v hlt hg)))

include hgood0 hgoodS hser in
/-- `thm:finite-dependent-choice`: every member of the path up to the horizon is good. -/
theorem serial_path (hqf : Good.QF) {u : PTm n}
    (hinit : Γ ⊢[PRAAx] ExW g0 (inst1 B0 u) u) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift (inst1 fuel u)) ⟶
      I3 Good (var 0) (path g0 sT Bd B0 (var 0) (Syn.shift u)) (Syn.shift u)) := by
  refine guarded_trace_all hqf (serial_step hgoodS hser) u ?_
  rw [sInit_at]
  exact hgood0 _ u (Prf.andE₂ (lt_of_exists hinit))

include hgood0 hgoodS hser in
/-- The member of stage `t ≤ fuel(u)` is good. -/
theorem serial_good (hqf : Good.QF) {u t : PTm n}
    (hinit : Γ ⊢[PRAAx] ExW g0 (inst1 B0 u) u) (ht : Γ ⊢[PRAAx] le t (inst1 fuel u)) :
    Γ ⊢[PRAAx] I3 Good t (path g0 sT Bd B0 t u) u := by
  have a := Prf.allE t (serial_path hgood0 hgoodS hser hqf hinit)
  have e : (le (var 0) (Syn.shift (inst1 fuel u)) ⟶
        I3 Good (var 0) (path g0 sT Bd B0 (var 0) (Syn.shift u)) (Syn.shift u)).subst (Syn.inst t) =
      (le t (inst1 fuel u) ⟶ I3 Good t (path g0 sT Bd B0 t u) u) := by
    simp [subst_I3]
  rw [e] at a
  exact Prf.impE a ht

include hgood0 hgoodS hser in
/-- Consecutive members are compatible: for `t < fuel(u)`, the next member is in range and passes the
successor test from the current one. -/
theorem serial_edge (hqf : Good.QF) {u t : PTm n}
    (hinit : Γ ⊢[PRAAx] ExW g0 (inst1 B0 u) u) (ht : Γ ⊢[PRAAx] lt t (inst1 fuel u)) :
    Γ ⊢[PRAAx] lt (path g0 sT Bd B0 (succ t) u) (inst2 Bd (succ t) u) ⋏
      (inst2 sT (path g0 sT Bd B0 (succ t) u) (pairT (path g0 sT Bd B0 t u) (pairT t u)) ≐ zero) := by
  have hg := serial_good hgood0 hgoodS hser hqf hinit (le_trans (le_succ_self t) ht)
  have w := lt_of_exists (hser t (path g0 sT Bd B0 t u) u ht hg)
  have r := run_succ (init := sInit g0 B0) (step := sStep sT Bd) (Δ := Γ) t u
  rw [sStep_at] at r
  exact .andI (lt_congr r.eqSymm (.eqRefl _) (Prf.andE₁ w))
    ((congrInst2 sT r (.eqRefl _)).eqTrans (Prf.andE₂ w))

end Path

end LeanProofs.IPRA.Foundations.SerialChoice

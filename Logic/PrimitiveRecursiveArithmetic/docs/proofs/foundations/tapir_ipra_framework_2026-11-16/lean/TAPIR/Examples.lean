import IPRADerivations.Foundations.TAPIR.Schedule
import IPRADerivations.Foundations.TAPIR.Certificates
import IPRADerivations.Foundations.TAPIR.Reflection
import IPRADerivations.Foundations.TAPIR.Trace

/-!
# TAPIR example targets (formalization blueprint)

The examples are intentionally small.  Their purpose is to exercise the typed
compiler, not to add another large theorem packet before the infrastructure is
elaborated.
-/

namespace LeanProofs.IPRA.TAPIR.Examples

open LeanProofs.ConciseIPRA LeanProofs.IPRA LeanProofs.IPRA.TAPIR
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

/-- Example 1 target: a two-node schedule where the second theorem uses the
first and the final endpoint has no hypotheses. -/
example {n : ℕ} (φ ψ : Fm PTm n)
    (hφ : ([] : List (Fm PTm n)) ⊢[PRAAx] φ)
    (hψ : [φ] ⊢[PRAAx] ψ) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] ψ := by
  exact Prf.trans hψ (fun χ h => by simpa using hφ)

/-- Example 2 target: local existential certificate with no public selector. -/
theorem local_certificate {n : ℕ} {Γ : List (Fm PTm n)}
    {cert : Fm PTm (n + 1)} {goal : Fm PTm n}
    (hex : Γ ⊢[PRAAx] Fm.ex cert)
    (hgoal : cert :: Γ.map Fm.shift ⊢[PRAAx] goal.shift) :
    Γ ⊢[PRAAx] goal := by
  exact Prf.exE hex hgoal

/-- Example 3 target: close a one-residual schedule. -/
theorem one_residual {n : ℕ} {B φ : Fm PTm n}
    (conditional : [B] ⊢[PRAAx] φ)
    (producer : ([] : List (Fm PTm n)) ⊢[PRAAx] B) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] φ := by
  exact Prf.trans conditional (fun ψ h => by simpa using producer)

/-- Remaining examples: finite minimum and bounded strategy, after the generic
reflection packages are elaborated. -/
theorem finite_minimum_blueprint : True := by
  trivial

theorem bounded_strategy_blueprint : True := by
  trivial

end LeanProofs.IPRA.TAPIR.Examples

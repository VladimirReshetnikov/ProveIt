import IPRADerivations.Foundations.TAPIR.Kernel

/-!
# TAPIR sequential schedules

A schedule is a topological ordering of a finite proof graph.  `R` is the fixed
residual context.  The list `outs` contains previously produced formulas in
reverse chronological order.  A new local node may depend on all earlier
outputs plus `R`; `Schedule.proveAll` compiles every output to a plan from `R`
alone by simultaneous cut.

Formal status in this archive: no intentional placeholders, but unelaborated
because Lean/Lake was unavailable in the build runtime.
-/

namespace LeanProofs.IPRA.TAPIR

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- A typed topological schedule. -/
inductive Schedule {n : ℕ} (R : List (Fm PTm n)) : List (Fm PTm n) → Type
  | nil : Schedule R []
  | cons {outs : List (Fm PTm n)} {φ : Fm PTm n}
      (tail : Schedule R outs)
      (local : Plan (outs ++ R) φ) : Schedule R (φ :: outs)

namespace Schedule

variable {n : ℕ} {R outs : List (Fm PTm n)} {φ : Fm PTm n}

/-- Discharge a context `outs ++ R`: earlier outputs use the induction
hypothesis; residuals use the corresponding object-theory hypothesis. -/
private def dischargeAppend
    (ih : ∀ ψ, ψ ∈ outs → Plan R ψ) :
    ∀ ψ, ψ ∈ outs ++ R → Plan R ψ := by
  intro ψ hψ
  rcases List.mem_append.mp hψ with hOut | hR
  · exact ih ψ hOut
  · exact .prf (.hyp hR)

/-- Compile every output of a schedule to a plan from the residual context. -/
def proveAll : (s : Schedule R outs) → ∀ ψ, ψ ∈ outs → Plan R ψ
  | .nil, ψ, h => by simp at h
  | .cons tail local, ψ, h => by
      rcases List.mem_cons.mp h with rfl | hTail
      · exact .cut local (dischargeAppend (proveAll tail))
      · exact proveAll tail ψ hTail

/-- The newest (head) output is derivable from residuals alone. -/
def head (s : Schedule R (φ :: outs)) : Plan R φ :=
  proveAll s φ List.mem_cons_self

/-- Literal ordinary iPRA endpoint of the schedule compiler. -/
theorem sound (s : Schedule R (φ :: outs)) : R ⊢[PRAAx] φ :=
  Plan.run (head s)

end Schedule

end LeanProofs.IPRA.TAPIR

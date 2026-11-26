import IPRADerivations.Foundations.GuardedLoop
import IPRADerivations.Foundations.BoundedFormulas
import IPRADerivations.Core.Header

/-! Imported from the packet `foundations/ipra_coupled_refinement_2026-11-19`, `lean/ObjectAdapter.lean`: the namespace is placed under `LeanProofs.IPRA.Foundations` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-!
# Object-level export adapter (integration outline)

This module targets ProveIt commit
3ee850b4c2d650cf01263823fd5415963747c5d0 and its Lean v4.32.0 toolchain.
The names and types below were checked against the source files at that commit.
This module has NOT been compiled against the repository in this artifact.

Unlike `AffineBounds.lean`, the conclusion here is an object-level derivability
judgment. The input `certificate` requires actual iPRA proof objects for the
base, one-step preservation, and final implication. Host-Lean arithmetic proofs
cannot be inserted into those fields.
-/

namespace LeanProofs.IPRA.Foundations.CoupledObjectAdapter

open_ipra
open LeanProofs.IPRA.ClockedDescent (Pat)
open LeanProofs.IPRA.Foundations.TraceReflection
open LeanProofs.IPRA.Foundations.GuardedLoop
open LeanProofs.IPRA.Foundations.BoundedFormulas

/-- Pack time, state, and the input parameter for the bounded-formula compiler. -/
def packedState : PTm 3 := pairT (var 0) (pairT (var 1) (var 2))

/-- A bounded invariant is reflected to one equation before induction. -/
def invariant (body : BF) : Fm PTm 3 := bitAt body 3 packedState ≐ one

theorem invariant_qf (body : BF) : (invariant body).QF := by trivial

/-- All computational syntax and proof obligations are explicit. -/
structure Package where
  init : PTm 1
  step : PTm 3
  fuel : PTm 1
  invariantBody : BF
  guard : Fm PTm 1
  result : Fm PTm 2
  certificate : Loop init step fuel (invariant invariantBody) guard result

/-- Conditional export. This is not an internal soundness/reflection principle. -/
theorem export_at (P : Package) {n : Nat} {Γ : List (Fm PTm n)}
    (u : PTm n) (hguard : Γ ⊢[PRAAx] Pat P.guard u) :
    Γ ⊢[PRAAx] A2 P.result
      (Run P.init P.step (Syn.subst ![u] P.fuel) u) u :=
  loop_at P.certificate u hguard

/-- Closed export by the existing trace theorem. -/
theorem export_closed (P : Package) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (P.guard ⟶ A2 P.result
        (Run P.init P.step (Syn.subst ![var 0] P.fuel) (var 0)) (var 0)) :=
  trace (obligations P.certificate)

end LeanProofs.IPRA.Foundations.CoupledObjectAdapter

import KIFCR.KernelCore

/-!
# Residual normalization and conditional closure blueprint

Residual reachability, duplicate removal, and provenance are metalevel
computations.  Their trusted output is a `ConditionalTheorem` whose proof is
checked by Lean.  This file intentionally contains no theorem-reflection axiom.
-/

namespace LeanProofs.KIFCR

open LeanProofs.ConciseIPRA
open scoped Fm

/-- Metadata for a proof-producing node.  `build` is left to the eventual
syntax generator; every accepted build must end in a `KernelRule.sound`. -/
structure ProofNode (n : ℕ) where
  name : String
  proofParents : List Nat
  boundaries : List (Boundary n)
  conclusion : Fm PTm n
  deriving Repr

/-- Output metadata of backward residual analysis. -/
structure ResidualPlan (n : ℕ) where
  reachableNodes : List Nat
  residuals : List (Boundary n)
  sinkNodes : List Nat
  deriving Repr

/-!
Metalevel algorithm:

1. Mark nodes backward-reachable from the requested sinks through proof edges.
2. Collect boundaries of reachable nodes.
3. Normalize formulas/variable layouts and deduplicate by `Boundary.key`.
4. Topologically order reachable executable nodes after certified recursive
   components have been collapsed to one node.
5. Generate a `Schedule` in context
   `residuals.map Boundary.formula ++ permanent`.
6. Package `Schedule.compile` as `ConditionalTheorem.proof`.
7. Close the theorem only with `ConditionalTheorem.close` and actual residual
   derivations.

A future verified metadata theorem may prove the reachability algorithm
correct, but the generated object proof is already independently kernel
checked.
-/

end LeanProofs.KIFCR

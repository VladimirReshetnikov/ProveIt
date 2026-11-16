import KIFCR.KernelCore
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Order

/-!
# Capped cyclic demand-closure blueprint

The semantic finite-lattice algorithm is executable at the metalevel.  For
object soundness, each fixed generated demand system emits PR terms and a QF
loop certificate.  Cap overflow is proved absent or retained as a residual.
-/

namespace LeanProofs.KIFCR

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- Object-facing certificate for one generated capped demand system. -/
structure DemandClosureCertificate (n : ℕ) where
  pre : Fm PTm n
  seed : PTm n
  caps : PTm n
  fuel : PTm n
  closedVector : PTm n
  fixedPoint : Fm PTm n
  leastness : Fm PTm n
  noOverflow : Fm PTm n
  loop : LoopCertificate n
  fixedProof : [pre] ⊢[PRAAx] fixedPoint
  leastProof : [pre] ⊢[PRAAx] leastness
  rawAdequacy : [pre, noOverflow] ⊢[PRAAx] fixedPoint

/-!
For a fixed arity and edge set, generate:

* nested-pair vector lookup/update terms;
* seed/cap terms and monotone edge-demand terms;
* `update`, `changed`, `overflow`, and rank terms;
* fuel `1 + sum_i (cap_i ∸ seed_i)`;
* one frozen-after-stability primitive recursion;
* a QF invariant proving bounds, inflation, rank increase on change, and
  frozen behavior after stability;
* a second QF induction proving leastness below every pre-fixed candidate;
* raw edge adequacy from `overflow = 0`.

The generic theorem is a code generator producing this record.  It is not an
object-level interpreter of an arbitrary demand graph.
-/

end LeanProofs.KIFCR

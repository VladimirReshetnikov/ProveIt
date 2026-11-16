# Source audit

## Snapshot

Primary repository: `VladimirReshetnikov/ProveIt`

Pinned commit: `7fa3ba48e8f62e8018ed954faaa48b908217eaf1`

Observed: 16 November 2026.

## Inspected current sources

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/UNIFICATION-PLAN.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_kifcr_framework_2026-11-16/`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_cbip_framework_2026-11-16/`

## Reused checked interfaces

- ordinary `Prf PRAAx` derivability;
- `Prf.trans`, `Prf.subst`, `Prf.weaken`;
- `PRA.qfInd`;
- checked arithmetic, search, pairing, simultaneous recursion, finite sums,
  Fubini, descent, and linear algebra in `IPRADerivations`;
- `pra_iff_native`.

## Relationship to earlier packets

KIFC-S is a conservative integration refinement.  It retains KIFC-R's
Boolean/search, trace, demand, viability, observer, guarded, finite-net, and
height interfaces.  It incorporates CBIP's normalized trace kernel and
bounded strategy viewpoint.  Its new contribution is the open-contract
calculus, query-minimal multi-sink compilation in that calculus, and the
three-level coherence theorem.

## Verification boundary

The artifact runtime did not contain Lean, so no new Lean build is claimed.
Python tests, JSON parsing, LaTeX compilation, PDF preflight, text extraction,
and render inspection were executed locally.  Source candidates and
blueprints contain no theorem-specific `axiom`, `sorry`, or `admit`.

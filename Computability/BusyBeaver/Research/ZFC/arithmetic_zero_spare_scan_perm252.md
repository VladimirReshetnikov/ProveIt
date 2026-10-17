# Internal scan over zero spare blocks

[`ArithmeticZeroSpareScanPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticZeroSpareScanPerm252.lean)
crosses an arbitrary internal number of zero register blocks in the actual
frozen252 arithmetic evaluator. Write

```
reverseZeroBlocks k left = zeroBlocks k (2*left) / 2
frame q left right = cantor q (cantor left right)
```

The exact endpoint is

```
runFrom (2*k) (frame seek left (zeroBlocks k suffix))
  = frame seek (reverseZeroBlocks k left) suffix
```

The count and both complete tape halves range over every IΣ1 model. The fixed
Σ1 graph uses the checked zero-block graph and the relational graph of division
by two; its total interpretation is Δ1. Pointwise Σ1 induction proves evenness,
including count zero, and hence the reverse-block successor and push laws.
The scan uses a Π1 induction predicate quantifying both entire halves. One
successor first takes the two literal steps for a value-zero block, then applies
the induction hypothesis to the changed left half `4*left+1`.

The generic theorem retains three actual transition equations. Unconditional
instances bind seek/probe pairs `(43,59)`, `(72,82)` and `(84,96)` to the frozen
table through the [register-forward contracts](arithmetic_register_forward_perm252.md).
The audit includes counts zero and one and a suffix starting with one. The
suffix is retained without a first-exit assertion. Absolute head coordinates,
a register-file/spare-growth invariant, decoder preservation and the full
internal binary/scheduler comparison remain separate.

This arithmetic proof follows the attributed register-box framework of
Mira-Cult, Jeff and Wade, including mira-emmy PR20 head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, `ZF/m253/coq/tm/Box.v`.
It proves the scan for arbitrary internal values rather than importing an
external finite-list theorem.

The [original fresh check](results/arithmetic-zero-spare-scan-perm252-verification.json)
passes eleven named axiom reports and twelve callers, using standard Lean
axioms with zero new warnings. Source and audit took 4.700 and 2.272 seconds
on pinned Lean 4.32.0. Thirty project providers, five external first providers,
toolchain Omega, all 81 original input identities and the fresh object were
checked. Existing dependencies were reused without rebuilding or downloading.
The imported zero-block module's three style warnings are recorded in its own
checkpoint. The [independent review](results/arithmetic-zero-spare-scan-perm252-review.json)
binds the final source, audit, portable guard and exact evidence.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_zero_spare_scan_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --forward-evidence /outside/successful-forward/verification.json \
  --zero-evidence /outside/successful-zero-blocks/verification.json \
  --output /outside/new-empty-zero-spare-check
```

The portable checker freshly checks only this module and its exact audit.
`--cache` relocates all thirty prerequisite objects while preserving their
required hashes; repeated `--library-path` supplies the complete dependency
library list. `--prepare-only` checks sources, providers and snapshots without
building proofs. The maintained-default preparation is **PREPARED_NOT_BUILT**,
separate from the successful original proof. The
[publication record](results/arithmetic-zero-spare-scan-perm252-publication.json)
keeps these statuses distinct and records the three guard rejection controls.
The first source attempt's quotation error and the initial incorrectly scoped
Omega-shadow test are retained as nonpasses; neither is accepted proof evidence.

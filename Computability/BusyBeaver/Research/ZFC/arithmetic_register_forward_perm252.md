# Internal forward crossing of an actual register block

[`ArithmeticRegisterForwardPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticRegisterForwardPerm252.lean)
crosses one unmarked unary register block in the actual frozen252 arithmetic
evaluator. In the least-significant-first encoding, define

```
registerBlock value suffix = 2 * bitPrefix true (value+1) suffix
reverseBlock value left = bitPrefix true (value+1) (2*left)
```

The fixed Σ1 graphs represent the whole separator-and-ones block and its
reversal onto the left half. For `frame q L R = cantor q (cantor L R)`,
the main endpoint is

```
runFrom (value+2) (frame seek left (registerBlock value suffix))
  = frame seek (reverseBlock value left) suffix
```

All values and both complete numeric tape halves range over every IΣ1 model.
Two literal rows cross the zero separator and first unary one; the checked
[uniform scan](arithmetic_machine_uniform_scans_perm252.md) crosses the remaining
`value` ones. The generic theorem keeps its three actual lookup equations
explicit. Unconditional instances use numeric seek/probe pairs `(43,59)`,
`(72,82)` and `(84,96)` for decrement, increment and the positive-decrement
suffix. Their finite row facts use the frozen table and the checked all-model
static-key bridge. No second table or assumed box oracle is introduced.

The generic one-step helper separates read bit, write bit and target state,
retaining the final write and move when the target is halt state zero. Audit
callers cover that literal halting edge, a zero-valued register, and a suffix
starting with one. The suffix is retained without a first-exit assertion.
Absolute head coordinates, a complete spare/register-file invariant, dispatch
preservation and the full internal binary/scheduler comparison are separate.

This ports the attributed contracts in `RegisterBoxesPerm252`,
`RegisterIncrementPerm252` and `RegisterDecrementPerm252`, originating in
mira-emmy PR20 head `0d544f2a2e3c18f12278441a74b7879f31cbe856`,
`ZF/m253/coq/tm/Box.v`. Mira-Cult, Jeff and Wade retain the machine,
verification and framework attributions. The new proof works with internal
arithmetic values rather than transferring an ordinary finite-list proof.

The [original fresh check](results/arithmetic-register-forward-perm252-verification.json)
passes ten named axiom reports and twelve callers, using standard Lean axioms
with zero warnings. Source and audit took 3.140 and 2.379 seconds on pinned
Lean 4.32.0. Twenty-eight project providers, five external first providers,
toolchain Omega, all 76 input identities and the fresh object were checked.
The [compact independent review](results/arithmetic-register-forward-perm252-review.json)
binds the final bytes, original evidence and maintained preparation.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_register_forward_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --uniform-evidence /outside/successful-uniform-scans/verification.json \
  --output /outside/new-empty-register-forward-check
```

The portable checker freshly checks only this module and its exact audit;
`--cache` relocates the 28 selected prerequisite objects without changing
their required hashes. Existing dependencies are reused without rebuilding
or downloading. `--prepare-only` verifies sources, providers and snapshots
without building proofs. The maintained-default preparation is explicitly
**PREPARED_NOT_BUILT**, separate from the unchanged successful original proof.
The [publication record](results/arithmetic-register-forward-perm252-publication.json)
keeps those statuses and all final wrapper identities distinct.

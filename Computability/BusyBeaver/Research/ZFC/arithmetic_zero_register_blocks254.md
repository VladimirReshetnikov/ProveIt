# Internal repetition of zero-valued register blocks

[`ArithmeticZeroRegisterBlocks254`](../../Lean/BusyBeaver/ZFC/ArithmeticZeroRegisterBlocks254.lean)
represents an internal number of `[false, true]` blocks followed by an
arbitrary numeric suffix. A fixed primitive-recursion blueprint defines

```
zeroBlocks 0 suffix = suffix
zeroBlocks (count+1) suffix = 4 * zeroBlocks count suffix + 2
```

The function is total in every IΣ1 model and has fixed Σ1 and Δ1 graphs.
Addition and push identities describe concatenation of the repeated blocks.
For a nonempty count, two arithmetic reads return zero, then one, and leave
exactly the previous suffix. A separate theorem identifies the ordinary-Nat
values with the actual maintained `ArithmeticMachinePerm252.bitsCode` of
the repeated two-bit list followed by any finite suffix.

This is a substrate for the growing spare-register suffix: the existing
instruction semantics appends zero registers on positive decrement. It does
not yet prove that invariant internally or simulate any machine row.

The [fresh check](results/arithmetic-zero-register-blocks254-verification.json)
passes fourteen axiom reports and fifteen callers with standard Lean axioms.
There are three unused-simplifier warnings in the source and none in the
audit. The exact checked bytes are retained. Fifteen project prerequisites,
four external providers and toolchain Omega are identified. The
[independent review](results/arithmetic-zero-register-blocks254-review.json)
binds the final source, audit, providers and fresh object.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_zero_register_blocks254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --run-from-evidence /outside/successful-run-from/verification.json \
  --output /outside/new-empty-zero-register-blocks-check
```

The checker uses the exact required subset of the successful RunFrom
prerequisites and freshly checks only this source and audit. Maintained
preparation is recorded separately from the successful proof check; it
does not rebuild Lean dependencies.

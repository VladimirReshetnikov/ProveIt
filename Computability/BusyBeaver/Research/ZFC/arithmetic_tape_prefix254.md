# Internal arithmetic tape prefixes

[`ArithmeticTapePrefix254`](../../Lean/BusyBeaver/ZFC/ArithmeticTapePrefix254.lean)
represents a block of ones of any internal length followed by an arbitrary
numeric suffix:

```
onesPrefix n suffix = Exp.exp n * (suffix + 1) - 1
```

Foundation's total internal base-two exponential makes this meaningful for
every element of every IΣ1 model. The successor, push, low-bit and quotient
identities retain the entire suffix. The fixed Σ0 graph bounds its power
witness by `out + 1`, covering the zero output as well.

The [fresh check](results/arithmetic-tape-prefix254-verification.json) passes
ten axiom reports and ten callers with standard Lean axioms and no warnings.
It reuses eleven project modules and three identified external providers.
The [independent review](results/arithmetic-tape-prefix254-review.json)
binds the final source, audit and object identities. This algebra is used by
the [actual binary scan](arithmetic_machine_scan_perm252.md).

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_tape_prefix254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --cantor-evidence /outside/successful-cantor/verification.json \
  --output /outside/new-empty-tape-prefix-check
```

The portable checker needs the successful Cantor check and its existing
objects; it does not require a previous TapePrefix result. `--cache` relocates
the eleven project objects. The older Cantor record identifies the compiler
version but lacks a historical compiler-binary hash; the checker records the
current pinned compiler before and after. Portable preparation is recorded
separately from the successful kernel check and builds no dependencies.

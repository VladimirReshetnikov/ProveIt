# PAeq formula recognizer witness bounds

This package adapts the arithmetic formula-recognizer witness argument to the
current PAeq target language. In every candidate-PRA model, it proves `WB`
for the exact PAeq formula recognizer in its positive polarity and for the
negation of its negative-polarity formula. The previously checked target
term-vector recognizer bounds discharge both explicit core assumptions.

These are model-level monotone witness bounds. They are prerequisites for
bounding formula-recursion graphs; they do not yet bound the PAeq formula
substitution graph or the arithmetic-to-PAeq formula-translation graph, and
they do not prove either translation compatibility or a machine reduction.
The upstream hashes identify the adapted arithmetic input proofs.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-formula-witness/check.sh
```

The final module passed a fresh suffix check against the checked PAeq term
witness modules and retained prerequisites; printed dependencies contain no
`sorryAx`. The full standalone replay remains pending.

# PAeq term-recursion witness bounds

This package adapts the arithmetic witness-bound proofs to the current PAeq
target language. In every candidate-PRA model, it establishes witness bounds
for the exact target function- and relation-symbol recognizers, and for the
actual term and term-vector recognizers in both positive and negative
polarities. Using the checked target recursion ranks, it proves witness bounds
for all six target term operations: variable shift, bound-variable shift,
and substitution, both for individual terms and for vectors.

The `WB` bounds are model-level monotone witness bounds; this package does not
extract fixed finite codes for the bounding functions. The result does not yet
bound the full target formula-substitution graph, the arithmetic-to-PAeq
formula-translation graph, or prove substitution compatibility. The upstream
hashes identify the adapted arithmetic input proofs.

From the repository root, with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-term-witness/check.sh
```

The four new modules passed ordered suffix checks against the checked PAeq
formula and term-rank modules plus retained project/Foundation prerequisites;
their printed axioms contain no `sorryAx`. The full standalone replay also
passed with the pinned audited overlays.

An independent ordered suffix replay rebuilt all four term witness-bound
modules against separately checked PAeq/qVec prerequisites and retained deeper
overlays. It passed without `sorryAx`; this was not a full prefix replay.

# Arithmetic columns for the actual literal control program

`ArithmeticControlData254.lean` derives fixed arithmetic control columns from
`FiniteControlTable254`'s actual 6,460 source leaves and proved native resolver.
It supplies compact constant syntax and coherent lookups for every arithmetic
model input. It does not define a represented control step/run or prove an
internal L2/scheduler simulation.

`natBits` computes the least-significant-first binary digits of a fixed external
natural. Its `bitsCode` theorem proves the needed roundtrip on all naturals;
there is no claim that arbitrary bit lists are canonical. Thus the previously
checked binary constant syntax can represent each key or field without a unary
numeral expansion. `compact_lookup_agrees` identifies the resulting arithmetic
lookup with the existing finite native-numeral lookup, in every `IOpen` model
and at every internal key and branch input.

Uniform consecutive keys ensure that all columns have a common source index.
A nonzero lookup result forces an internal key to equal the cast of one fixed
external row index; this conclusion does not assume the input key is standard.
At that index, `fieldValue_at` identifies every column, including zero-valued
fields. Branch zero selects the zero row, while every nonzero input selects the
positive row. Missing keys return zero.

The actual columns are derived from imported source pairs, rather than a second
Python table. Inc/Dec/no-op/halt opcodes are 1/2/3/4; the accepted-source theorem
excludes decoder-node leaves. Physical register selectors use the existing
permutation and are below nine. Successor numbers use the actual
`incPath`/`breakPath`/`continuePath` followed by `resolveControl`. Successor zero
occurs exactly at the genuine halt source. Overflow, positive-Dec spare delta,
and PC bits retain the actual path conventions. A PC integer increment is not
substituted for the source path operation.

For any two externally fixed maps on the actual control catalogue, `fieldDef`
is a fixed parameter-free bounded graph for their paired column lookup. The
actual `opcodeDef` has such a graph and satisfies, in every `IOpen` model,
`opcodeValue(q) != 0` exactly when `q` names a live catalogue control. In
particular, genuine halt opcode four remains distinct from absent lookup zero.
No graph oracle or arbitrary semantic relation is supplied as a hypothesis.

The final 257-line source and 77-line audit passed the pinned Lean 4.32 check in
2.860708s and 2.519770s: 16 ordered axiom probes, 20 callers, standard axioms only,
and zero warnings. Exact provider hashes are recorded in the accompanying
verification JSON. The guard reuses the source/object-matched union of 81 project
modules and six external boundaries from the checked compact-lookup and actual
catalogue records. It verifies actual first providers, Init/Omega and all inputs
before/after; it does not rebuild dependencies, 233 coverage chunks, 8,391 binary
guards or the 82,552-step bootstrap.

One unsuccessful source attempt is preserved: a recursive `simp` expanded a dead
`natBits` branch, two conditionals needed explicit normalization, and an index
bound needed explicit successor cancellation. A successful second run is also
preserved. One trailing space was subsequently removed, requiring a final check
of the resulting exact source bytes. The source-derived data, graph definitions
and theorem contracts did not change in these repairs. Original records,
executed guards and source/audit snapshots remain separate from publication
metadata; no incomplete attempt is counted as a pass.

A portable focused replay uses matching existing objects:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_data254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/Proofs \
  --control-evidence /path/to/arithmetic-finite-control254-verification.json \
  --catalogue-evidence /path/to/finite-control-table254-verification.json \
  --output /outside/new-empty-directory
```

`--prepare-only` validates and snapshots providers without compiling the source
or audit; compiler version discovery may run. `--cache` and repeated
`--library-path` permit explicit relocation only when the selected objects match
the recorded hashes. There are no downloads or dependency builds.
The maintained-default preflight passed without proof compilation. Four guard
controls rejected optimized Python, nonempty output, and shadowed first Init and
Omega providers; these are metadata/preflight rejections, not logical counterexamples.

The next runtime layer must define a fixed nine-register coded state and its
represented step, relate that step to actual checked binary sites, and then
supply iteration and a genuine internal scheduler connection. For canonical
successor identification it should retain `next_checked`'s actual walk witness
and apply `resolve_source`; the convenience reentry wrappers alone do not export
that witness. No new machine size, calculus reduction, PA consistency endpoint,
or whole binary internalization follows from this finite-data checkpoint.

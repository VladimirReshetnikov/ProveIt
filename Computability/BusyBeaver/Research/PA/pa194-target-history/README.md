# Partial target proof-history interpreter

`PA194TargetStep.lean` defines a fixed finite candidate-PRA interpreter for a
new, independently chosen proof-line encoding. The program is a Foundation
pair-encoded vector; at stage `n`, the interpreter reads `program.[n]` and
appends the result to a pair-plus-one reverse history. The line forms are:

- `pair 0 (pair a b)`: the target h1 axiom with parameters `a,b`;
- `pair 1 (pair label offset)`: generalization from a reverse-history offset;
- `pair 2 (pair conclusion (pair minorOffset majorOffset))`: modus ponens from
  two reverse-history offsets.

A rule returns zero on rejection and theorem number plus one on acceptance.
The generalization and modus-ponens branches explicitly require every
referenced offset to be smaller than the current stage. `leaf_step`,
`gen_step`, and `mp_step` identify the three branches with the previously
checked rule-specific codes. `history_base` and `history_step` prove the exact
primitive-recursive history equations, while `history_newest` and
`history_earlier` prove the corresponding reverse-history access equations.
They hold in every candidate-PRA model with an IΣ₁ arithmetic reduct, including
nonstandard stages, indices, programs and values.

This interpreter does not check a vector-length bound before reading nth:
Foundation's total nth operation supplies the value for every index, including
out-of-range positions. The encoding is independent of the upstream checker.
Global soundness of histories, completeness, the remaining target rules,
full source proof compilation, PA calibration, and a machine reduction are
not yet established.

The final module passed a fresh Lean 4.32 suffix build against the retained
rule-step and Foundation-vector suffixes and audited project and Foundation
overlays. Its printed main theorem axiom dependencies are `[propext,
Classical.choice, Quot.sound]`, without `sorryAx`. The full nested two-chain
replay below is pending, including checking that its two independently rebuilt
source-shift dependency chains compose in one overlay.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-target-history/check.sh
```

The script rebuilds the prerequisite chains under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.

An independent suffix replay recompiled the history module against separately
checked target step and source-search objects, reusing other prerequisite
overlays. Its reported axioms did not include `sorryAx`.

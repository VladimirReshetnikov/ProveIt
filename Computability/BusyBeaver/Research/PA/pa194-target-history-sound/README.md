# Internal soundness invariant for the partial target history

`history_sound` proves an invariant of `pa194-target-history` by internal IΣ₁
induction. Let `G` be a Σ₁-definable predicate on target theorem numbers. The
explicit hypotheses say:

1. Every output of the fixed h1 axiom constructor satisfies `G`.
2. If `G a`, then `G (allValue label a)` for every label.
3. If `G a` and `G (impValue a b)`, then `G b`.

Under these hypotheses, every result in the reverse history is either the
rejection value zero or the successor of a theorem satisfying `G`.
`accepted_sound` states the latter directly for an accepted history entry.
The theorem applies in every candidate-PRA model with an IΣ₁ arithmetic reduct,
including nonstandard program data, stage lengths and indices. The proof first
establishes that the invariant is Σ₁-definable, proves preservation for the
actual h1/generalization/modus-ponens branches and rejection of unknown tags,
and then invokes internal induction rather than external induction on model
elements.

The invariant is conditional on the three closure hypotheses; this package
does not identify or construct a particular target-provability predicate `G`.
The underlying interpreter does not guard program-vector length before using
total nth. Other target rules, a complete proof-history checker and its
soundness, source proof compilation, PA calibration and machine reductions
remain open.

The final module passed a fresh Lean 4.32 suffix rebuild against the retained
partial-history and earlier rule/source/target suffixes plus audited project
and Foundation overlays. The printed theorem axiom dependencies are `[propext,
Classical.choice, Quot.sound]`, without `sorryAx`. A full nested replay using
the script below is pending, including its two separately rebuilt prerequisite
chains.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-target-history-sound/check.sh
```

The script rebuilds the prerequisite chains under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.

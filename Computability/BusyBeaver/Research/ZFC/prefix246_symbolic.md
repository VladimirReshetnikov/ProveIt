# Sound symbolic execution for prefix246

`SymbolicPrefix246.lean` proves that every accepted finite symbolic trace describes actual execution of the exact 246-state table. Its affine runs cover every natural gap parameter, and its register boxes cover arbitrary natural values in nine primaries and a nonempty finite spare suffix. Increment appends a value-one spare; positive decrement retains all spare values and moves the file boundary one cell right; zero decrement restores the file through old112.

The entire tape is represented. Normalization discards only exterior zero padding on the left. A successful trace must include a literal machine transition, so it yields a strictly positive execution time; the final halting transition retains its write and movement. The nine regenerated selector IDs are checked in both directions. Fast lookup is identified with the exact table by the checked `FastTablePrefix246` equality.

Root's first source/audit run passed: 15 named axiom probes and 15 typed callers, using only standard Lean axioms and producing no warnings. Source took 4.226 seconds and audit 0.468 seconds. The bounded guard uses one thread, 4,096 MiB, a shared 120-second budget and default elaboration limits. It builds no dependencies and makes no version query.

The exact dependency closure contains 12 project providers, with Init and Lean.Elab.Tactic.Omega as toolchain boundaries. Independent review rechecked all 41 recorded input identities, the complete import closure, the actual first providers and the fresh object recorded before the audit. The sole successful attempt and raw source/audit/guard snapshots are retained; the history archive was assembled after success from those exact bytes.

From the repository root, using a new external output directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix246_symbolic.py \
  --repo "$PWD" \
  --boxes-evidence Computability/BusyBeaver/Research/ZFC/results/prefix246-boxes-verification.json \
  --mark-evidence Computability/BusyBeaver/Research/ZFC/results/prefix246-mark-verification.json \
  --fast-evidence Computability/BusyBeaver/Research/ZFC/results/fast-table-prefix246-verification.json \
  --output /tmp/zfc-prefix246-symbolic-check --prepare-only
```

Preparation checks bindings without running Lean or querying its version. Removing `--prepare-only` requests the bounded source/audit proof check. Publication preserves the successful source/audit bytes and changes only the guard's two default paths. The successful record retains the three actual scratch parent evidence paths used in that run; the byte-identical maintained records can be supplied above.

This executor soundness theorem does not establish acceptance of all 8,391 instruction cases, the actual blank bootstrap, the complete runtime equivalence, a binary consistency theorem or PA internalization. Attribution follows the checked 250-state implementation, Mira-Cult, Jeff Ketchersid and Wade's symbolic framework, source58's shared carry, source61's selector fold and source63's contextual pulse fold.

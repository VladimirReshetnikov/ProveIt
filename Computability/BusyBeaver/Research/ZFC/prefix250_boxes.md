# Exact prefix250 unbounded register boxes

`Prefix250Boxes.lean` proves the three changed register excursions on the exact 250 table. Prefix length, register values and finite left context are arbitrary; every endpoint specifies the whole infinite zero-exterior tape.

| Operation | Entry / exit old labels | Exact duration | File effect |
|---|---|---|---|
| Positive decrement |95 /48|`2*width(pre)+4`|Selected value decreases; file boundary shifts right 1; spare suffix unchanged|
| Zero decrement |95 /112|`2*width(pre)+7`|Entire file restored; following block required|
| Increment |73 /48|`2*width(file)+7`|Selected value increases; one value-one spare appended|

The output 112 for zero decrement is intentional. Its later phase-bit continuation belongs to the instruction simulation. The zero-case following block is guaranteed by a runtime file with nine primary registers and a nonempty spare suffix. Existing spare values may be arbitrary natural numbers.

The forward carry and rollback are proved by induction over every block. The exact final-table pulse supplies the zero test, and increment handles formerly implicit blank exterior cells explicitly. Core corollaries use the existing `ZipRep` soundness theorem; these are unbounded theorems, not finite test results. The old 252 modules supply only generic unary-list algebra and a table-parametric return scanner, instantiated with exact 250 rows.

The root's successful second attempt checked the 424-line source and 117-line audit, with 14 axiom probes and 19 callers. All probes use only `propext` and, where needed, `Quot.sound`. Seven unused-simp warnings in the source are retained; the audit has none. Run1 failed on two list-normalization goals; run2 changed only the corresponding proof lines, preserving every public contract and default proof budget. Full failed/successful records, snapshots, compiler outputs and the repair diff remain in the history artifact.

Successful record SHA256: `68624e0d456285c02175e95a9786d587a25aa6483dfab4af394988b3deb3478e`.
Source SHA256: `9b49c86335eef38378418a7611bfa89ef3d5fd2f03e9db82babc5674fedb5657`.
Audit SHA256: `baae6aba32d000ae1f6bdf3fb61c8f5b4b4bd04c1f64a74625438f7e2b1e73f9`.
Fresh object SHA256: `b8b78f621fea6923831b2afb8cf58235d867949121b05882eda78902b1e4b67c`.

The bounded checker reuses eight exact project providers and the supplied Init/Omega toolchain boundaries, builds only this source and audit, records its fresh object before the audit, and rechecks all inputs afterward. It uses one thread, 4096 MiB, a shared 120-second proof budget and default Lean elaboration limits. Prepare-only makes no compiler or version invocation. A root may inspect maintained defaults without a proof replay:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_prefix250_boxes.py \
  --repo "$PWD" \
  --pulse-evidence Computability/BusyBeaver/Research/ZFC/results/prefix250-pulse-verification.json \
  --output /tmp/prefix250-boxes-fresh-preparation --prepare-only
```

The evidence uses supplied, pinned provider objects; this command performs no dependency build. Publication retains the executed guard and changes only its default source/audit paths. The source-only independent reviewer read the original complete source; the final author/root review also covers the two-line repair and run evidence. Those review scopes are recorded separately.

Mira-Cult, Jeff Ketchersid and Wade retain their original machine, verification and compiler attribution. The new shared-carry construction is the ProveIt research contribution preserved from incoming source58 (`126d12e470`). This unit does not yet prove full instruction simulation, the blank bootstrap, the exact 250 consistency endpoint, or the requested equivalence internal to PA.

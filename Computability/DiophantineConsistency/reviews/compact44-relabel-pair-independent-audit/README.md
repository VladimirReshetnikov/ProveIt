# Independent paired finite-table correspondence audit

This audits the completed pair and evidence `b5a95621d2`. The final Lean
statement `CompactRelabelDraft.finite_table_correspondence` is the conjunction
of these exact finite-list statements:

1. `mappedOld = selectedNew`, where `mappedOld` maps the displayed
   horizontal/vertical arrays over the old `WangTiles942.orderedRows` and
   `selectedNew` indexes the Lean 943-row list using `rowIndices`.
2. The horizontal array is a permutation of `List.range 250`.
3. The vertical array is a permutation of `List.range 439`.
4. `rowIndices` is a permutation of `[0] ++ List.range' 2 941`, i.e. compact
   indices 0 and 2 through 942.

The selected compact row at index 1 is therefore absent from this finite
correspondence. The independently rerun external array and inverse checkers
bind the displayed arrays to the finite relabeling receipt. The JSON-to-Lean
943-row identification remains a separate external ordered-source check. These
facts do **not** prove that a matching neighbor exists in an arbitrary model
tiling, transport a whole tiling or machine simulation to that model,
calibrate the compact44 checker, or establish an iPRA endpoint.

The read-only artifact audit checks the recorded outer session 43986 exit 0,
all 116 compiler/dependency exits, all 58 frozen source bytes against their
individual committed anchors, corresponding objects and 116 retained logs,
full paired provider overlays, and exact same-side direct imports in
build order. It reconstructs and verifies the entire set of 1,190 direct
`.olean`/companion present-or-absent guards. Both side's source, object and
log hashes match for all 58 modules. It reruns all three parent audits
(342-module endpoint, finite relabeling and 943-row table), and separately
reruns the external array and inverse checks; both latter commands exited 0.

All 116 logs have no warnings, errors or `sorryAx`. Each side has 59 exact
named axiom reports: 17 list no Lean axioms, 2 list `propext` and
`Quot.sound`, and 40, including the final correspondence, list `propext`,
`Classical.choice` and `Quot.sound`. This is the inventory of printed
statements, not a complete inventory of all inherited declarations.

The first **reviewer-script** attempt exited 1 before any parent audit because
it looked for `observed_exit`; this packet records the actual field as
`actual_exit_code`. The corrected script checks the actual session, exit,
116-child and receipt fields and completed successfully. This was not a
failure of the paired Lean build.

The terminal receipt records an expected stable HEAD and clean-loader launch;
this audit checks the record, not a continuous external history. Inherited
Foundation outer-wrapper, package-transitive and dynamic ancestry limitations
remain. Sampled RSS is not a hard process-tree quota; `--deps` and audit
subprocess timeouts are not monitored whole-tree resource bounds. Hashes are
point-in-time checks; the original `/tmp` object trees are needed for replay.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-relabel-pair-independent-audit/audit.py
```

Actual independent audit session 77797 exited 0 and launched no Lean compiler.
See `CHECK.json` and `terminal-observation.json`.

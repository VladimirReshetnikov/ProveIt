# Exact Lean source and logical-seed interface

`check_source_interface.py` independently extracts the concrete data underlying
ProveIt's `SetTheory.BusyBeaver.ZFC.SourceRotation240.program`. It compares the
entire ordered unfolding with the pinned input source used by this research
delivery. This closes the identification of that JSON source with the calibrated
Lean program. It does not build Lean or replay the Lean kernel proofs.

## Result

The check passes for all **6,455 ordered `(path, opcode, argument)` triples** in
`../baseline/rotation240/sites_logical.json`, SHA-256
`74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d`.
The checker parses all 203 literal row declarations, parses and evaluates the
actual binary `rawLookup` if-tree for each of its 203 indices, verifies the
default lookup guard and program root, and applies the actual three overrides:
rows 5 and 6 in `ProgramRotation244`, then row 169 in `SourceRotation240`.

The unfolded root is 202. Exactly 202 internal rows are reachable; row 4 is
unreachable. Row 169 occurs four times. The source has 23 distinct leaf kinds,
maximum path length 51, maximum zero run 6, and 8,386 decrement-sensitive guards.
The 203-row storage bound and 225 total distinct source subtrees are source data
counts; the binary machine count is established separately.

The checker also extracts the declaration order of `L2.AS`, every branch of
`L2.enc`, and `LogicalSeed246.seed`, `registers`, and `initial`. The resulting
configuration has an empty program pointer, logical registers
`[3, 0, 0, 0, 3, 0, 0, 0, 0]`, and zero registers at all indices at least 9.
These values match `../candidate239/blank_prefix.json`. The imported
`BootstrapFrameRotation240` states the corresponding physical register vector
`[0, 0, 0, 3, 0, 0, 3, 0, 0]` and 167 spare blocks of value 1, also matched by the
blank-prefix artifact. Its literal frame parameters agree with the 409,691-step
startup target. The full binary startup execution and whole-tape equality are
verified by the separate candidate checker; this interface check does not claim
to replace those verifications.

## Replay

From the package root:

```sh
python source_interface/check_source_interface.py
```

The script uses only Python's standard library and rejects optimized Python
execution because its assertions are proof obligations. It can run from any
working directory. `--sites`, `--blank-prefix`, and `--output` override the
default relative inputs and output. The result is `interface_result.json`.

The final 239-state machine uses the reassociated source whose canonical
serialization is `../candidate239/sites_logical.json`, SHA-256
`7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6`.
The separate source control-flow certificate connects that source to the exact
input source identified here; this checker does not equate the two different
path lists.

## Provenance

All six included Lean files were fetched read-only from the archive's pinned
ProveIt commit
[`13ec39ed43148b1807f51ed6e6528e1c84659562`](https://github.com/VladimirReshetnikov/ProveIt/tree/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Lean/BusyBeaver/ZFC).
`source_pins.json` records exact URLs and Git blob SHA-1 values; the checker
recomputes those Git blob identifiers from the complete included bytes and
records their SHA-256 digests in its result. An initial read at commit
`71363997bcbad9212ca920e871c87f36c8312f76` returned identical blobs for all six
files. The final check and attribution use the archive's 13ec commit.

The Lean files are unchanged upstream sources and retain their notices. No
existing frozen research or candidate files were modified for this check.

# W6(A): exact packed Rotation240 table binding

This is an unexecuted source proposal. The first proof target is full equality
of the 6,455-row packed table and the actual decoder catalogue:

```lean
PackedTables.table BisimCertRotation240.tableR BisimCertRotation240.countR =
  (ControlCatalogue.leafEntries TreeRotation240.tree).map
    (ArithmeticControlTable.rowOf TreeRotation240.tree)
```

The left side is definitionally `ControlBisimRotation240.tableR`. The proposal
does not import that module's separate bisimulation/certificate proof. It does
not establish an internal binary simulation, a root DAG occurrence, the Enum
scheduler link, or the final internal consistency endpoint.

## Frozen proof candidates

`ControlTableBinding.lean` is the generic next proof, with six qualified axiom
probes and nine typed audit clients in `Audit.lean`. It has no proof-limit
override. `checkRow` compares all four row fields at the one-based control
`crank ct P + 1`. `rowCounted` uses the existing `edgeOpcode`, `registerOf`
(hence `physOf`) and `outgoingPathOf`; only the cached counted tree replaces
`annotate t` during evaluation. Its identity is an explicit hypothesis.

`crank_at_get` proves the numbered slot corresponds to its exact leaf path by
`entry_at_crank`, `leafEntries_nodup`, and structural `LeafAt` soundness. The
linear catalogue is used only in this generic proof, never by the executable
row test. `packed_table_eq` requires exact length equality, so extra rows
cannot be hidden. `checked_rank_resolves` uses `allSites_total` and
`entry_at_crank` to recover the actual successor leaf and consumed path,
including implicit trailing zeros. Halts retain two zero successor fields.

`ControlTableBindingRotation240.lean` is a four-probe/four-client conditional
adapter (`Rotation240Audit.lean`). It binds the literal packed data and actual
`SourceRotation240.program` decoder via `TreeRotation240.walk_eq_tree`. Its
counted-tree identity and closed all-sites theorem remain explicit premises.
This is not a completed concrete acceptance theorem.

Opening's independent source-only comparison checked all 6,455 rows, including
non-test `next1`, with no mismatch: initial control 1 is path `000`, `decnz 8`,
physical register 1, zero successor 3, positive successor 2; the only halt is
control 6321. It also checks raw register fields below 9, zero unused high
bits, and in-range successors. This supports the proposal but supplies no
kernel theorem. Its exact receipt is pinned in `prerequisite-inventory.json`.

## Concrete finite-check sequence

1. Compile/audit the missing upstream prerequisites described below, then the
   generic proof. Preserve each actual result separately. Do not start a
   production family before the generic source/audit has passed.
2. Prepare a counted-tree data unit from the exact 203 stored TreeRotation240
   definitions. Keep a matching private plain tree with the same 203 shared
   nodes and a counted node for each one. Prove each local leaf count and
   annotation equality using its two already-proved children. A final
   structural equality binds the plain root to `TreeRotation240.tree`; it
   must not assume that copied source text is a theorem. This supplies
   `counted_eq : counted = ControlCatalogue.annotate TreeRotation240.tree`.
   The mirror is finite data only; no new source semantics are introduced.
3. Reuse the *prefix partition data* of the completed coverage family: four
   pilot cuts plus 526 production cuts, 530 total. Each new check has exactly
   the form
   `allSites (check counted) prefix.reverse (descend TreeRotation240.tree prefix) = true`.
   Retain the complete root prefix; testing a subtree under the empty prefix
   would compute wrong source/successor ranks. Existing binary `checkSite`
   proof objects do not prove these new tests and must not be relabelled.
4. First root compiles one measured cut, preferably the largest existing
   guard-count cut (the old partition's maximum is 26 branch checks), under
   the normal shared 120-second, one-thread, 4096-MiB guard. Then select a
   grouping from the actual measurement. Every accepted leaf check uses
   packed arithmetic extraction and at most three rank descents through
   cached counts (source plus two successors). No timing is claimed yet.
5. Join successful cuts with the existing generic `allSites_join`, preserving
   literal path coverage and rejecting `.none`, then instantiate
   `table_eq_of_checked`. Keep the final length 6,455, complete prefix cover,
   all actual source/object pins, and every interruption/failure in the
   production manifest. No predetermined number of new compilation units is
   asserted before the measurement; 530 is a partition count.
6. Export the unconditional exact table equality and row-at-program-walk
   theorem. A tiny later alias adapter may expose the result using
   `ControlBisimRotation240.tableR` once that module has actual reusable
   provider evidence. This does not require replaying its certificate to
   establish the finite decoder-table identity itself.

No emitter or generator is included or invoked in this proposal. In
particular, no future object hashes or successful chunk records are invented.

## Actual prerequisite boundary

The own static inventory derives 46 project source modules including the two
new drafts. Thirty-eight existing selected pairs are current and have actual
record provenance; six upstream modules have no exact module occurrence in
the maintained `*verification.json` records searched. They require fresh,
bounded checks rather than an assumed cache:

| Order | Unit | Actual older prerequisites available | Required focused audit |
| --- | --- | --- | --- |
| 1 | ControlCatalogue | SiteCoverage and its closure | leafEntries soundness/nodup, entry_at_crank, BT.get_ofList |
| 1 | ArithmeticControlFile | ArithmeticCantor and its closure | projection/file inverse, write preservation, live decode |
| 1 | ArithmeticControlBisim | ArithmeticMachineGraphPerm252 and its closure | checkFrom_entry, entry_step, halts_iff_of_check |
| 2 | PackedTables | fresh ArithmeticControlBisim | rowsOf_some, table_length, literal extraction clients |
| 2 | ArithmeticControlTable | three fresh generic modules above; actual Permutation252Frame | rowOf, spec_get, run equations |
| 3 | BisimCertRotation240 | fresh PackedTables | exact count/packed-data declarations; no certificate acceptance claim |

Then compile the generic candidate and conditional concrete adapter. This is
an inventory/plan, not an executable guard or an assertion that all upstream
proofs were independently reviewed here. ArithmeticControlFile,
ArithmeticControlBisim and ArithmeticControlTable contain upstream options
`maxRecDepth 8192` and `maxHeartbeats 4000000`; the other three do not raise
proof limits. Preserve and disclose those exact upstream bytes if checked.
The new proposed modules have only `autoImplicit false`, and the proposed
closed chunks must use default proof limits. A timeout is evidence to retain,
not permission to increase limits silently.

The candidate actual boundary is formed from already completed Bootstrap240,
Tree240, GraphPrefix246 and final Sites240 records. Only needed provider pairs
are selected; the old coverage family is not a new proof dependency of the
checker. The inventory rehashes the 38 selected source/object pairs, but is
not a complete replacement for a strict guard's parent-log, first-provider,
pre-audit and post-input validation. A future root-run guard must add those
checks. No dependency build, download or version query is proposed.

## Integration limits

The binding closes W6(A)'s finite table identity, including the physical
register map. It does not itself port the internal frame simulation. Opening
owns that separate lane: Rotation240 needs dispatch state 84/code 85 and the
64-cell margin; old Perm252 frame updates cannot be copied without checking
the actual increment/decrement spare/gap conventions. The passed finite
bootstrap transports a concrete standard numeral and remains a separate
input to the eventual arbitrary-internal-time simulation. W4/W5 root DAG and
scheduler obligations remain with the broader PA lane.

Author: drop_contract. Opening owns the independent literal comparison.
Reflection's requested generic proof peer is pending; no peer approval or
compiler success is implied by this freeze. Own metadata-reader draft path
and provider omissions were caught before any inventory output and retained
under `history/`; they did not change proof sources.

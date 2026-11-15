# Current PA machine comparison

This comparison is pinned to ProveIt commit
`1e1a41f799d4658b829cdd0eabae3775a0c8c4a0` (14 November 2026).
It covers the literal and explicitly encoded machine tables in
`Computability/BusyBeaver/Research/PA` and `docs/incoming`.

## Freshly checked scope

The read-only scan selected every tracked `.tm`, `.json`, and `.zip` file in
those two paths: 695 literal table files, 9,790 JSON files, and 10 ZIP files,
or 10,495 Git payloads. Each payload was checked against its exact Git blob
identity. No selected blob was missing. ZIPs were inspected recursively;
duplicate ZIP payloads were read once and recorded as duplicate references.

Recognized explicit JSON forms are multiline five-column table strings,
arrays of five-field rows, arrays of row strings, and dictionaries keyed by
`(state,read)` with three-field transition arrays. Arbitrary generators,
prose and unevaluated Lean definitions were not executed to infer more tables.

The scan found 3,000 complete one-terminal table occurrences, 805 normalized
labeled tables, and 680 spanning transition-graph classes. The 194-state
slice has 908 occurrences, 184 normalized labeled tables, and **110 spanning
classes**. All 110 remain distinct under the broader structural comparison
below. Every one of them also has 194 classes in the coarsest ordinary
immediate-action control bisimulation. That last fact excludes only ordinary
control quotients; it is not a lower bound for context-dependent reductions.

The census contains 53 spanning 193-state classes. They include rejected
blank-start experiments and a logical coefficient-three proposal. Their
presence is not evidence of a 193-state PA consistency machine.

Six normalized tables have no spanning root and are recorded separately in
`summary.json`. Nineteen literal fragments have zero or multiple external
terminal labels; `excluded_literal_formats.json` records each one and its
actual state/terminal counts. None of those nineteen has 194 working states.
No archive failed to open and no selected source was unavailable.

## All 110 classes and all 86 current deliveries

`designs194.csv` and its JSON companion have one row for every historical
194-state spanning class. The categories describe how the source reports
present the tables; they are not new calibration theorems:

| Reported role | Classes |
|---|---:|
| Principal construction | 56 |
| Supplementary construction | 7 |
| Research auxiliary | 36 |
| Research seed | 4 |
| Rejected construction | 6 |
| Rejected diagnostic | 1 |

The 94 earlier classes are reconciled with the attributed mechanism ledger
in the incoming AX11G packet. Current incoming material adds five principal
classes (AX11G, AX11QH4L, AX11QH4R, GH and GHS) and eleven auxiliary graphs
(three four-increment local-search inputs and eight GH neutral edits).

`packets86.csv` and its JSON companion cover 82 filed deliveries and all four
current incoming archives. The incoming AX11H archive has the same stem as
an earlier filed packet but is a distinct updated delivery. Its stronger
written proof claim is recorded explicitly; duplicate names do not imply
identical report contents. Its principal machine graphs already occur in
the 94-class historical set.

The rows identify exact source locations, graph classes, original-byte
hashes, mechanism descriptions and evidence roles. `occurrences.csv` retains
the broader occurrence-level census, including occurrence-specific start
information and explicit JSON pointers. `classes.json` contains all 680
spanning classes, across all sizes.

## State names and starts

A comment declaring `start N` is honored. Otherwise state 0 is treated as
the conventional start only for a dense table numbered from 0 to n-1.
This convention is not a proof of the intended start; some research files
are dense renumberings of native tables with a different intended start.
The occurrence ledger distinguishes declared starts and conventions.

For structural novelty the comparison deliberately forgets the intended
start and considers **every control from which the complete table is
graph-reachable**. It minimizes the complete breadth-first transition tuple
over those spanning roots, visiting read-symbol 0 before 1. Two such canonical
tuples are equal exactly when the complete spanning tables are related by a
state renaming with an allowed choice of root. Tables without a spanning
root are excluded from this assertion and listed separately.

The broader comparison additionally allows left-right reflection, global
bit exchange, and arbitrary final writes/moves on transitions entering halt.
Bit exchange is used as a stronger structural test; it need not preserve
the all-zero initial tape. These tests are not a claim that all semantic
equivalences between different machines have been decided.

## The two new candidates

The `candidates/` directory contains the exact dense tables and recorded
novelty checks for PA194AX11GH and PA194AX11GHS. Both have 194 working states,
388 rows, start 0, halt label 194, and all 194 controls graph-reachable.
Their broad structural classes differ from all 110 prior classes and from
each other. This establishes novelty within the pinned recognized corpus;
it is not a worldwide priority claim.

## Offline replay

Python 3.10 or later and its standard library suffice. Keep assertions
enabled:

```sh
python3 -B verify_bundle.py --receipt /tmp/current-comparison-replay.json
```

This verifies all bundled file hashes, representative source-byte bindings,
the full canonical tuples and broad symmetries, the 110-way distinctness,
the ordinary bisimulations, and both candidate comparisons. The comparisons
are exact tuple comparisons, not merely digest lookups. The original
repository and source archives are unnecessary for that replay.

`source_manifest.json.gz` records every original selected Git payload.
The default offline replay verifies its internal integrity and the bundled
representative bindings. It cannot reread unbundled original bytes. To
independently recheck all 10,495 original payload identities against a local
copy of the pinned repository, add:

```sh
python3 -B verify_bundle.py --repository /path/to/ProveIt
```

This optional operation uses only locally available Git objects and fails
on missing objects; it does not implicitly download anything. To rebuild
the entire census from that snapshot, the inherited read-only `audit.py`
accepts `--repo`, `--pin`, and a new `--output` directory. It recognizes
tables only and never executes the programs found in the repository.

## Proof scope and attribution

The graph checks prove no consistency equivalence. Most reports supply
written PA calibrations, relative iPRA preservation results, executable
certificates, or conditional formal statements. The current project README
continues to describe its end-to-end Lean/iPRA machine calibration as open.
The **updated incoming AX11H manuscript** separately claims a complete
ordinary written iPRA calibration with explicit compiler and clock arguments;
this is a stronger mathematical claim than merely having not run Lean.
The main report of the new construction states exactly how that manuscript
is inherited and distinguishes it from the new relative preservation proof.

Historical mechanism annotations are attributed to the AX11G comparison
ledger, reconciled by freshly computed full graph identity. The current
incoming additions are classified from their own reports and search roles.
The initial census/graph implementation `audit.py` is inherited from the
GH packet and was inspected before fresh execution. The snapshot audit,
86-delivery/110-class reconciliation, source-byte bindings, new candidate
checks and portable replay are new to this comparison. `PROVENANCE.json`
records exact inputs. Original license and notice files are retained in
`licenses/`. Historical machines and mathematical ingredients remain
attributed to their source packets and authors.

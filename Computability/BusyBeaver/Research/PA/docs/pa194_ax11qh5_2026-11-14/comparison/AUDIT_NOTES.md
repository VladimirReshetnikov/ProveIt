# Current incoming PA-machine audit

Snapshot: `4be5c6e3a10292a7466f5d3687e3b39615ff049b`.

## Scope and evidence standard

The current repository contains 61 filed research deliveries under
`Computability/BusyBeaver/Research/PA/docs` and 11 incoming ZIPs: 72 deliveries
in all. This is different from the 66-delivery snapshot used by several
recent reports, which was pinned to `2337ce611a26e308697ccbddb2a1636f989f01c3`.
Every current incoming archive was obtained from the pinned Git tree, checked
as a ZIP, and extracted without accepting traversal paths or symlinks.
`archive_inventory.json` records the archive SHA-256 values and byte counts.

The reports distinguish ordinary mathematical PA-provability arguments from
kernel-checked end-to-end Lean/Rocq theorems. None of these eleven incoming
packets claims a new completed end-to-end kernel theorem. They often contain
universal symbolic source/tape certificates and a separate complete finite
blank-start trace; these do not on their own check the inherited PA-calculus
calibration. The official PA README states that the stronger iPRA endpoint
remains open. That stronger open endpoint is not itself a refutation of an
ordinary mathematical PA argument, and the two standards should not be
conflated.

Historical `supported packet construction` statuses below attribute the
reports, rather than claiming that every historical proof was independently
reconstructed in this session. Exact literal table counts, identities and
graph comparisons are independently recomputed.

## Current incoming contributions

| Incoming archive | Principal result | What changes | Status |
|---|---|---|---|
| pa194_ax11_research_2026-11-14 | PA194AX11; also PA194QH5 | AX pushes its gate, falls through the MP field reader, consumes a fourth operand z, and has eleven stacked entries. Successful MP no longer performs a dummy push. | Ordinary PA argument plus full independent literal checks supplied. QH5 duplicates the separate QH5 packet. |
| pa194_qh5_research_2026-11-14 | PA194QH5 | Coefficient five, exchanged quantifier-distribution premises, no-push visible-result MP, cache-only Shift. | Ordinary PA argument plus full independent literal checks supplied. |
| pa194h5_research_2026-11-14 | PA194H5; PA195EvenHX | H5 combines coefficient five and cache-only/no-push control with the original emitter. EvenHX permanently enumerates only one parity of fresh commands. | H5 is 194; EvenHX is 195. Both have ordinary PA arguments and independent physical checks in the packet. |
| pa194qh_conpa_2026-11-13 | PA194QH | Q emitter plus coefficient-four cache-only/no-push control. | Ordinary PA argument and independent physical checks supplied. This graph is already in the 76-class old frontier. |
| pa194qhs_conpa_2026-11-14 | PA194QHS | QH plus symmetric destructive cache-only Shift, removing a restoration loop. | Ordinary PA argument and independent literal checks supplied; changed source behavior, no new state record. |
| pa194qn6_conpa_2026-11-14 | PA194QN6; provisional TopOnly196 | Q emitter, coefficient six, no-push MP, original sum guard. | QN6 is 194 with full independent replay. TopOnly196 has the inherited arithmetic-box interface, and does not have the same independent replay/calibration status. |
| pa194qn_2026-11-14 | PA194QN5 and PA194QN6 | Coefficient-five/six Q/no-push/sum-guard combinations. | QN6 exactly duplicates the dedicated QN6 table; QN5 is a distinct 194 graph. |
| pa_consistency_reduction_study_2026-11-13 | Restricted direct-selector obstruction | Exact rational dual proves at least 194 within one fixed-raw-parent, disjoint direct-selector template. | No new machine meeting the strict target. No general 194 lower bound. |
| pa_consistency_research_2026-11-14 | All-offset coefficient-three obstruction | For I=3p, M=3p+1, U=3p(transposed)+2, every fixed nonnegative E=3p+e fails with the retained heads/rules. | No accepted new sub-194 machine. |
| pa_sub194_research | MP196 | Successful MP halts immediately when its conclusion is code one. | 196-state ordinary argument with inherited arithmetic-box interface; above the requested bound. |
| pa_sub194_research_2026-11-13 | Runtime193 | Merges native 301 into 88 and patches two return rows. | Runtime source contracts pass, but blank initialization is rejected. Not a blank-start Con(PA) machine. |

`principal_designs.json` supplies all principal literal paths, counts and
byte hashes. Two important duplicate pairs are exact byte identities:

* QN6 in the dedicated QN6 archive and in the QN5/QN6 companion archive:
  `72a35e528c1061f61e211d0bcf3a954859d2dbbcfd6b9f7846e4f970bb04e4e9`.
* QH5 in AX11's secondary component and in the dedicated QH5 archive:
  `94c85547b3edd0df0a441d45bf22abb52711f2b27cc9e680999232285757dba5`.

There are therefore six new supported 194-state graphs beyond the old
76-spanning-graph frontier: AX11, QH5, H5, QHS, QN5, and QN6. QH was already
present in that old frontier. They are compositions or protocol changes in
the existing numerical-calculus architecture, not independent new theories
of PA consistency.

## Fresh census and novelty

The completed full-scope scan covers 21,051 tracked paths and all nested
archives under both requested locations. It records 3,663 recognized table
occurrences, 774 byte strings, 751 labeled tables, 651 component buckets,
and 638 full single-halt graph classes. All 535 historical catalogue classes
are covered. The full scan reads 6,460 candidate text files and 10,649 JSON
occurrences, including archive members. It has no exclusions or warnings.
It confirms exactly the same 82 spanning 194-state graphs as the incoming
scan; the extra PA files contribute additional occurrences and numberings,
rather than further graph classes.

The incoming-only census reads all eleven ZIPs recursively and recognizes
complete numeric five-column tables in TM/text/tabular files and in JSON
strings or five-column JSON row arrays. It found 2,681 table occurrences,
726 distinct labeled tables, 651 maximal-component classes, and 638 full
single-halt graphs. There were no exclusions or warnings with a 128 MiB
per-text limit and 2 GiB aggregate candidate-archive limit.

Among these are 83 literal 194-label classes. One is a disconnected
diagnostic; the remaining 82 are spanning graphs. The old 76-class evidence
labels plus the six new reports give 40 supported reported constructions,
7 supplementary constructions, 26 research auxiliaries, 4 research seeds,
and 5 rejected constructions. This is an attribution of evidence, not 47
newly checked consistency theorems.

The 82 full 194-state graphs remain 82 distinct classes even under arbitrary
state renaming, any spanning root, tape reflection, global bit exchange,
and ignored write/move actions on terminal edges. Exact canonical tuples
are in `current194_novelty_corpus.json`; a fresh candidate can be
compared using `check_novelty.py`. The positive control correctly
recognizes the repeated QH5 table. These symmetries deliberately enlarge
equivalence for novelty; a bit exchange by itself does not preserve the
zero-blank initial condition.

There are 53 literal 193-state classes in the current incoming scan. This
growth beyond the old two classes is caused by failed runtime transplants,
append-zero and marker-relay experiments, and the AX11/QN6 runtime patches.
It must not be described as 53 smaller consistency machines.

## Important obstructions and already attempted routes

1. The old coefficient-three table reaches a good seed and has physical
   source checks, but its retained syntax has E3(1,0)=I3(0,1)=6. A supplied
   73,393-step primitive numerical proof derives code one. The later
   all-offset theorem also rules out merely replacing the equality tag by
   another fixed nonnegative constant, with the other heads retained.
2. Runtime193 has valid source-frame behavior under its stated arithmetic
   interface, but the blank start reaches an outward ray. Changing the
   initial control, tested register permutations, bounded neutral edits,
   and many variant transplants did not repair it.
3. QN6's latest report already includes more than 22 million grammar proposals,
   fixed/AX compatible folds, occurrence-specific rotations, reparsing,
   equality-head premise exchanges, coefficient-five/six associations,
   QNS6 compositions and forced increment-three reuse. These finite
   negative searches are not lower bounds, but should not be repeated and
   advertised as novel ideas without a materially different search space.
4. AX11 was already tested with the runtime193 quotient; all 193 possible
   starts either halt or enter certified rays. Its fourth AX operand must
   not be omitted from a command-level proof.
5. The H5 packet's sparse scheduler theorem is a real mathematical option:
   for any finite command word W, terminal pointers t and t+2^d(W) produce
   fresh encodings of opposite parity. Thus every parity progression
   eventually runs a command word with W as prefix. Its existing physical
   realization has 195 states and requires a physical H/X register swap.
   The included exact 93-step certificate shows that simply adding the runtime193 quotient to EvenHX still
   reaches the old outward ray before the extra scheduler control is used.
6. Removing the Shift wrapper eagerly has an actual counterexample; the
   corrected eager-Shift design in the QH5 packet costs 197 states.

## Delivered comparison files

* `archive_inventory.json`: all eleven archive identities.
* `principal_designs.json`: principal machine paths, hashes and statuses.
* `summary.json`, `full_graph_summary.json`, `table_occurrences.csv`, and
  `table_classes.csv`: full pinned PA plus incoming census.
* `packet_ledger72.csv` and `.json`: all delivered packets and their evidence.
* `current194_novelty_corpus.json` and `frontier_tables/`: exact reference
  canonical tuples and literal representatives of all 82 current full graphs.
* `check_novelty.py`: standalone candidate comparison; `--recompute` rebuilds
  every reference tuple from its actual table.
* `novelty.json`: fresh no-match receipt for PA194AX11QH5.
* `audit_current.py`: portable full-scope auditor. Pass the pinned repository
  path, `--revision`, and a fresh `--output` directory. It does not depend on
  the extracted working paths recorded in the historical inventories.

The recognizer does not execute arbitrary generators or interpret arbitrary
transition-dictionary encodings, diagrams, or prose descriptions. The
reported novelty scope must retain this limitation. Each principal report's
actual delivered literal table is covered; generators without a materialized
table are not evidence of a new graph identity.

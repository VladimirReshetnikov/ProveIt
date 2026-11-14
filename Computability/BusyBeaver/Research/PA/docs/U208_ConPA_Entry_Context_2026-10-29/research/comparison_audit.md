# Comparison of six supplied U209 archives

Internal independent audit for the parent research report, 29 October 2026.
Repository snapshot fetched by parent: `343da82d7384d10ec9fd1c17361fc923b2d1d117`.
The individual historical proposals cite `da4ab9dd68ccfc47ac852118601eaf1fdae53795`.

## Decisive result

The six archive names represent **two rooted labeled transition-graph isomorphism
classes**, not six independently different machines. All have 209 working states,
418 transition rows, separate halt 209 in their dense tables, and all 209 working
states reachable in the directed graph from start 0. Graph reachability is not a
statement about which states the particular blank computation visits.

`compare_tables.py` parses every row independently, canonicalizes by BFS with
read-0 before read-1, and includes write bits, move directions, and the halt label
in the canonical form. It also verifies each proposed isomorphism directly on
all rows. For nonisomorphic pairs it records the first inconsistent BFS row.
No tape reflection or symbol complementation is used.

| Archive stem after U209_ConPA | Dense SHA-256 | Class | Max source depth |
|---|---|---|---:|
| `_2026-10-29` (Plain) | `65ccb606c8e970adec22c311486e747b440171363601b8f11b56bc729cf8decb` | A | 42 |
| `_Compatibility_2026-10-29` | `bda91bd40880f96edef104246d22797fe281355cf03610ab7e93e7923be8aa16` | B | 41 |
| `_Compatible_Folds_2026-10-29` | `5ded628d692ff442e4346c61eb3db3c77b0ac2c80c1ecced45cbfc483be40e08` | A | 42 |
| `_Composed_2026-10-29` | `3a69998d818b6e637e33dc0a2412538e49179a501496d5c252c7f68ff2af78be` | A | 42 |
| `_Joint_2026-10-29` | `5ded628d692ff442e4346c61eb3db3c77b0ac2c80c1ecced45cbfc483be40e08` | A | 42 |
| `_Joint_2026-10-29 (1)` (PDF only) | `65ccb606c8e970adec22c311486e747b440171363601b8f11b56bc729cf8decb` | A | 42 |

The last row is independently recovered from all 209 two-column entries in the
PDF's transition appendix, not merely trusted from its printed hash. Reconstructed
`pdf_only_u209.tm` is byte-identical to Plain's `machine/u209.tm`.

Folds and Joint have identical native as well as dense tables. In native labels,
Plain maps to Joint by two disjoint 3-cycles:

* `217 -> 129 -> 214 -> 217`;
* `215 -> 204 -> 216 -> 215`.

Composed maps to Joint by the 5-cycle
`217 -> 129 -> 204 -> 214 -> 216 -> 217`.
Every other native label is fixed. Full dense maps are in
`machine_comparison.json`.

## Source comparison

All five executable archives have exactly the same ordered word of 3,909
primitive instructions and the same full ordinal control graph (5,083 nonhalt
arrows). Operation counts are CD=1175, CB=80, CI=1558, CC=1095, CH=1.
The comparison ran both the interval-based and arithmetic source CFG resolvers;
these helpers are inherited rather than an independently developed semantics.

Class A's source files are byte-identical, SHA-256
`cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164`.
Class B's source has SHA-256
`912724f29b0de28b3326c710fdf1f3863ebd07058c6db1a9b4bbaffb3ae5e3f3`.
Both have maximum zero run 6 and 197 distinct syntactic subtrees. Thus the
different class B layout changes addressing, not the logical proof calculus or
the ordered source computation. Depth 41 versus 42 does not imply a proven
unbounded running-time improvement.

## Construction and presentation differences

Every packet combines the three former U211 savings: native 180,181,218 are
deleted relative to common U212. Their labels have different helper assignments,
but their saving counts cannot be added again.

* **Plain:** 30 closed-factor rotations from U212, arithmetic entry repair
  `171/0: 0 L7 -> 0 L205`, then simultaneous folds
  `180->163, 181->220, 218->157`. Uses helper217 for 181/220. Its useful separate
  research is the propositional-row deletion obstruction described below.
* **Composed:** same class A machine after the above 5-cycle; 30 rotations plus
  physical relabeling. Its local proof exposition carefully distinguishes
  unmodified donor157's ordinary entries from its multi-step 218 simulation and
  explains finite reverse halting simulation well. It directly retains recovered
  U222 calibration material as well as original archives.
* **Compatible Folds:** 17 rotations, a closed eleven-factor reparenthesization
  of the emitter, and 3 external rotations. It preserves helper129 for181/220,
  uses163 for180, and parks `(218,116)` at215. Final machine exactly Joint.
* **Joint:** a simultaneous 18-selector layout of a 3,096-primitive region,
  followed by the three same deletions. Compact deterministic builder; clear
  direct simultaneous local proof; unchanged runtime engine tied by exact bytes
  to the retained U212 dependency; complete nested U222 lineage; independent C++
  finite executor. This is the best practical baseline for new literal-table work.
* **PDF-only Joint (1):** 24 reassociations starting from Contextual U211,
  hence 30 when the parent's 6 rotations are included. This is a useful alternate
  exposition of Plain, but contains no executable artifact or proof certificate
  beyond the PDF transition table.
* **Compatibility:** the unique second class. Starts from Research U211,
  uses 8 rotations to remove218, then an eight-factor rewrite which changes
  `204/1` while preserving `204/0` used by the backward129 helper. This yields
  a new `(90,211)` pair at216. Three outer rotations plus the arithmetic repair
  allow `180->216` with `216/0 = 0 L211`. It preserves helper129 and the
  already-removed181 and218. This packet explains selective preservation of a
  shared helper particularly well; treating every shared helper as frozen would
  miss its valid alternative layout.

Useful exact source references are the README in each package;
Compatibility `proofs/new_reduction.md` and `paper/construction.tex`;
Composed `paper/fold.tex`; Joint `code/check_local.py`, `code/build.py` and
`report.tex`; and Plain `research/propositional_row_no_go.txt`.

## Verification status

Each original packet claims ordinary PA-formalizable mathematics plus executable
symbolic-induction checks, explicitly not a newly compiled PA/Lean/Rocq/MM0
endpoint. The K215 ZFC result is for a different literal table and theory; it
cannot certify these U209 machines. The source/runtime/startup/numerical-calculus
and U/PA bridges remain substantive inherited dependencies.

For the local U212-prefold to U209 folds, complete incoming inventories establish
arrival-tag facts on every initial tape from state0. Exceptional paths read two
known cells with arbitrary unread exterior; all ordinary rows commute with the
state quotient; all blocks are positive and avoid halt internally. This yields
both halting directions by finite induction. The 1-to-5 step bound is only for
the final fold, not for preceding address reassociation. Full source/runtime
preservation has the canonical-frame/blank-start scope; intermediate rotations
with a seven-zero address run are construction intermediates, not certified
complete interpreters.

I freshly ran the full release verification for one member of each isomorphism
class rather than duplicating full tests of relabelings:

* Compatibility: **FULL_REPLAY_PASS**. Manifest72 files, both U210/U209 exact
  builders and finite auditors, startup48140 each, new U209 universal5084 cases,
  all418 rows, 1,248,748 symbolic inference applications, minimum duration
  constant5, fresh case data exactly equals delivered data. Receipt
  `compatibility_replay.json`; 157.754s in this environment. The `false` flags
  under `saved_runtime_records` mean that those records are only parsed there;
  the actual freshly rederived result is `fresh_runtime[0]`, with equality true.
* Joint: **U209_FULL_REPLAY_PASS**. Manifest90 files, both exact unmodified
  engine/dependency bindings,10 local cases,2 engine-entry cases,13 rejected
  negative controls,414 ordinary quotient rows,3909 primitive sites,5083 CFG
  arrows,3908 prefix interfaces,48140 startup steps,5084 freshly regenerated
  runtime cases, all418 rows,1,250,049 symbolic inferences. Receipt
  `joint_replay.json`;206.320s in this environment.

Joint's universal engine is inherited Python with assertions, not a proof
assistant kernel. Its release checker intentionally rejects optimized Python
for the symbolic engine while separately checking finite identities under -O.
All code was inspected before execution; Compatibility was copied to a work
directory so its generated build outputs did not alter the source snapshot.

## Prior search limits and new direction

Joint's old fixed-table discovery screened 43,264 direct aliases at macro limit15
and 7,038 one-row left-tag folds at limit17 without success. I ran the same
positive-certificate search on Compatibility, at limit25: 43,264 aliases and
6,624 folds (16 pair schemas), again with no result. These are incomplete
bounded discovery screens and prove no lower bound. All positive results would
require exhaustive symbolic local-branch checks on arbitrary exterior.

The supplied Plain packet already rules out simply deleting the native
dominated propositional row: a Boolean logical-matrix valuation with implication
as equality, membership false, auxiliary equality true, and identity quantifier
makes every retained logical and covering axiom designated. PA can therefore
prove that the resulting calculus does not derive target1. Under consistency
of PA it cannot retain a PA-provable Con(PA) equivalence, by second
incompleteness. The word 'dominated' is a numerical-parameter restriction, not
a logical redundancy. This is important prior research, not a new reduction.

## Independent check of the parent's new U208 proposal

The proposed change to Joint removes native172 by mapping172->211 and changes
`211/0` from `0 R157` to `0 L217`. I independently inspected its exact table.
There are two sufficient reachable-entry invariants:

1. Every old172 entry has bits at offsets(-2,-1) equal to(1,0): the sole
   incoming edge is116/0=0R172, and116's sole incoming edge is215/1=1R116.
2. Every old211 configuration scanning0 has bit1 immediately left. If entered
   by163/1, this is immediate. Otherwise163/0 moved left. Reading0 at that
   predecessor excludes the132/1 and199/1 entries to163, forcing217/0.
   State217's sole incoming216/1 wrote1 one cell further left. Neither of the
   two following moves changes that1.

The modified paths are then exact:

* old211/read0: `211@0 -> 217@-1 -> 215@0 -> 157@1`, 3 steps;
* old172/read0: `211@0 -> 217@-1 -> 163@0 -> 211@-1 -> 217@-2 ->
  215@-1 -> 157@0 -> 67@-1`, 7 steps;
* both read1 cases: the common `1 R184`, 1 step.

All writes preserve the three displayed cells, all exterior cells are unread,
and no path contains halt. The old one-step endpoints agree after projection.
Every other old row commutes with the quotient. Since start0 is outside the
selected states, the backward entry derivations apply to every possible visit
from every initial tape. This is a direct local halting-equivalence theorem
with no source reassociation. A full new primitive-runtime suite is therefore
helpful regression evidence but not needed to logically transfer the parent's
correctness via this proved simulation. The sharp clock formula for this
local change is `T208=T209+2*N(211,0)+6*N(172,0)` for an old halting run.

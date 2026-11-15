# Bounded reduction searches and portable replay

These files record unsuccessful searches for a machine below 194 states and the
finite composition work that led to PA194GD, PA194GDH, and PA194GDHS. The search
results are **not lower bounds on possible Turing machines**. They concern
specific grammars, source transformations, or local quotient models. The
positive construction and proof certificates are in the main packet.

All paths below are relative to the root of the extracted packet. Python 3.10+
is sufficient for the composition and continuation sweeps. The grammar and
physical searches additionally require a C++17 compiler (`g++` by default).
No repository checkout or network access is needed. The additional inherited
input snapshots are attributed and hashed in `INPUT_PROVENANCE.json`; the
main packet supplies its pinned primary compiler, source, and raw table.

## Receipt audit

```sh
python3 research/audit_receipts.py --output replay/recorded-research.json
```

This checks that the aggregate counters agree with the original completion
logs, that all recorded hit files are empty, and that the portable composition
and corrected continuation replay outputs agree with their recorded results.
It is a bookkeeping audit, not a new reduction search.

## Composition screen: 432 combinations

```sh
python3 research/composition/gd_variants.py --check-recorded --output replay/composition.json
```

The script reuses the main packet's construction modules and three inherited
grammar shapes. It varies explicit/original generalization binder,
ordinary/exchanged distribution, diagonal parameter A/D/H, two AX exit choices,
two decoder exit choices, and sum/cached/symmetric-cached Shift. The product is
`3*2*2*3*2*2*3=432` combinations. Its optimistic minimum is 194, and it reproduces
all 60 qualifying rows of `composition/gd_variants.log` exactly.

These are raw-state-minus-matching screens. They do not assert that every
candidate's side conditions or simultaneous folds hold. In particular, the
zero-test substitutions are counterfactual experiments in this grid. The
three delivered machines use ordinary structural exits and receive complete
validation separately. `composition/replay.json` records all 432 combinations,
including the candidates whose scores exceed 194.

## Corrected continuation sweep: 40 candidates

```sh
python3 research/loop_sweep/explore.py --check-recorded --output replay/loop-sweep.json
```

The sweep considers the four-increment loop's binary associations in primary,
AX11H, AX11GH, and AX11GHS. Ten compatible shapes per parent preserve the entire
resolved source graph, including every jump and branch. Helper allocation is
collision-free: it skips every occupied native control. The archived
`loop_sweep/report.json` and `corrected.log` are the corrected results.

Of the 40 candidates, 23 have an optimistic count of 194 and 17 have 195. No count
is below 194. The legacy field name `lower` in the report means the local
raw-minus-matching screen; it is not a theorem about all machines. A fresh
portable replay matches the corrected report, including the exact matching
choices and source-graph assertions.

## Grammar searches: eight timed runs

For example:

```sh
python3 research/replay_grammar.py GD --output replay/grammar-GD
python3 research/replay_grammar.py head_order --output replay/head-order
```

Available run names are `selector_primary`, `selector_GH`, `selector_GHS`,
`top_only_195`, `GD`, `GDH`, `GDHS`, and `head_order`. The default budgets are
600 seconds for the first seven and 300 seconds for head order. `--seconds` and
`--seed` override the recorded settings; `--compiler` selects a C++17 compiler.
The wrapper compiles the appropriate source, uses the exact bundled templates
and attributes, and writes fresh logs, seeds, and a receipt into the output
directory. For input-loading checks without mutations, use `--seconds 0`.

The original eight runs totaled **37,916,566 mutation slots** and 3,558,249
accepted mutations, with zero threshold hits. A slot counts the mutation-loop
iteration, including proposals abandoned before evaluation; it is not a count
of distinct grammars. Because the limit is wall time, a repeated run's final
mutation total depends on hardware and compiler. Its saved inputs, algorithm,
seed, and budget are reproducible; the archived logs preserve the exact
historical totals.

The ordinary search combines tree rotations with independent parameter
permutations. The head-order search splits and rejoins the seven emitted head
blocks while retaining their internal trees. A hit would still need complete
source, command, physical, and calibration checks. The top-only run attempts to
reduce a 195-state implementation to 194; the semantic idea was already in the
supplied corpus and is not claimed as new here.

## Physical quotients:radius 4 and 100 transitions

```sh
python3 research/replay_physical.py GD --output replay/physical-GD
python3 research/replay_physical.py GDH --output replay/physical-GDH
python3 research/replay_physical.py GDHS --output replay/physical-GDHS
```

The wrapper compiles `physical/inherited/src/joint_return_merge.cpp`, uses each
final native table, and supplies its recorded source-context windows. Add
`--regenerate-contexts` to rerun the inherited symbolic context collector first.
Its source executions include the interiors of accelerated scans, exclude
startup, and do not narrow the arithmetic engine. `--compile-only` checks the
build without starting the search.

For each unordered pair of controls, the program synthesizes both surviving
actions with targets among the remaining nonhalting controls. It permits
repeated visits to the quotient control and requires complete local tape,
head-displacement, and successor equality inside a radius-four window in at
most 100 transitions. Across the three tables it tested **56,163 control
pairs**, **70,793,172 single-row actions**, and **391,365 joint action pairs**,
with zero hits. This excludes candidates only within that bounded local
model; it does not rule out different windows, more state changes, or another
architecture.

The `physical/inherited/` code and notices are retained from the supplied
research packet. `physical/summary.json`, the completion logs, context
receipts, and empty hit files record the actual runs.

## Packaging scope and omitted exploratory files

Two path-bound auxiliary notebooks/scripts, `build_top.py` and
`visible_shapes.py`, have been omitted from `composition/`. They relied on
unbundled research directories and are unnecessary for reproducing either the
new machines or the recorded top-only grammar screen. Its complete executable
search input remains in `grammar/top_only_195/templates.txt`. No mismatched
proof or novelty claim for an auxiliary 195-state machine is included here.

The portability checks replayed the 432-combination grid and all 40 corrected
loop candidates, compiled both grammar engines and the physical engine, and
loaded the grammar inputs with zero mutation slots. They did not add new
bounded-search runs to the historical totals. Compiled binaries and Python
cache files are excluded from the deliverable.

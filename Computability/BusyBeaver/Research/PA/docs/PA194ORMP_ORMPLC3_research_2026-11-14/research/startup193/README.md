# Additional bounded 193-state initialization searches

These are research cores, not positive blank-start consistency machines.
No complete source frame was found.

## Inputs

The runtime193 table, append-zero sibling, and 346-edit pool come from
docs/incoming/pa194_ax11hc4_c32_research_2026-11-15.zip at ProveIt commit
7c0bb454cf73c29ca1c385f9fec856ddd236a7cb. The pool affects 92 rows and includes
speculative arithmetic edits; membership does not certify runtime validity.
Original authorship remains as credited in the retained licenses.

The template file contains all 3,673 primary source paths, from the filed
pa_sub194_research_2026-11-13/runtime193/primary.sites.json.

## Broadened two-edit screens

The all-sites pair screen adapts the supplied search to all source sites,
minimum header span 38, and a twelve-one-cell prefilter. The short-frame
screen allows any nonnegative padding after the recognized source path.

~~~sh
g++ -O3 -std=c++17 all_sites_pair_startup.cpp -o /tmp/pa194_pair
/tmp/pa194_pair runtime193.native.tm speculative_edits.tsv \
  all_source_templates.tsv 200000 /tmp/hits1.jsonl
g++ -O3 -std=c++17 short_frame_pair_startup.cpp -o /tmp/pa194_short
/tmp/pa194_short runtime193_append0.native.tm speculative_edits.tsv \
  all_source_templates.tsv 200000 /tmp/hits0.jsonl
~~~

Run each executable on both append variants for the four saved receipts.
Each tests 58,485 edit pairs and 11,287,605 initial controls. The complete
finite support, marker, unary blocks, and nonempty spare tail are checked;
all nine register values are unrestricted for discovery. A hit would still
need an admissible semantic seed and a universal edited-runtime proof.

The head-displacement bound is 20,000. Lookahead additionally requires
head + 38 < 20000, excluding a narrow region near the positive boundary
even for shorter paths. Pair screens inspect the fuel-bound configuration
before classifying it as unresolved.

## Trace-driven static edits

The new trace search branches on every allowed static edit when its row
is first visited. Choosing the original action freezes that choice too.
It never edits a row after an inconsistent earlier use. Up to three edits
are allowed. Unencountered edit combinations have the same bounded run as
an already represented branch.

Pruning uses a monotone outward zero-reading ray after all editable rows
on that ray have been decided (or the edit budget is exhausted), or an
exact repeated control/head pair during an interval without any tape
change. The latter is not a probabilistic tape-hash test.

~~~sh
g++ -O3 -std=c++17 trace_startup.cpp -o /tmp/pa194_trace
/tmp/pa194_trace runtime193.native.tm speculative_edits.tsv \
  all_source_templates.tsv 3 200000 1000000 /tmp/trace1_hits.jsonl
/tmp/pa194_trace runtime193_append0.native.tm speculative_edits.tsv \
  all_source_templates.tsv 3 200000 1000000 /tmp/trace0_hits.jsonl
~~~

| Quantity | Append zero | Append one |
|---|---:|---:|
| Complete initial-control searches | 193 | 193 |
| Traced branches | 516,722 | 551,892 |
| Literal transitions | 2,583,756,604 | 2,711,960,862 |
| Halts | 1,124 | 608 |
| Outward rays | 304,195 | 332,234 |
| Unchanged-tape cycles | 194,853 | 201,835 |
| Bounded unresolved branches | 16,550 | 17,215 |
| Complete frame hits | 0 | 0 |

Both runs finish before the one-million-branch cap. Frames are inspected
at times strictly below 200,000; the fuel-bound configuration is unresolved.
The same lookahead restriction applies. Branch counts are not counts of
distinct literal tables and include cases covered by the pair screens.

## Recognizer check

~~~sh
g++ -O2 -std=c++17 check_frame_recognizer.cpp -o /tmp/check_frames
/tmp/check_frames all_source_templates.tsv
~~~

This invokes the exact frame() function used by the trace search. It
accepts 14,692 canonical frames over every source path, including three
with only twelve ones, and rejects 29,384 malformed tapes. It checks the
implementation of the selected conditions, not their necessity for every
possible successful initializer.

No finite or bounded negative result here proves a 194-state lower bound.

Constructor-tag reassignment searches
====================================

These are negative research experiments, not accepted new consistency
machines or a lower bound on Turing-machine state complexity.

RESULTS

Eight heuristic searches tested 15,664,325 reassociation proposals. None
produced a screened allocation at or below 194 states. From both the
primary and the G grammars, the best screened totals were:

  radix 5, universal tag 2, equality tag 4: 196
  radix 6, universal tag 2, equality tag 4: 196
  radix 8, universal tag 2, equality tag 4: 196
  radix 4, universal tag 3, equality tag 2: 198

The standard implication tag zero and membership/contradiction tag one
are retained. The first three families need 135 fixed controls because
their multiplier engine uses an additional pure-increment helper. Their
best reader allocation is 68 raw readers minus seven compatible folds.
The swapped-tag family has 134 fixed controls. Its best primary grammar
uses 72 readers minus eight folds; its best G grammar uses 71 minus seven.

Exact iteration counts, accepted moves, seeds, times and paths appear in
tag_search_summary.json. TAG_SEARCH_PROVENANCE.json identifies the pinned
inputs and hashes the literal search sources, templates and complete logs.
The primary runs used seed 14112026 and 180 seconds each. The G runs used
seed 14122026 and 240 seconds each. The wall-clock limit can change how
many proposals finish on another computer; it is not a proof condition.

SCOPE AND REPLAY

The directories k5u2e4, k6u2e4, k8u2e4 and k4u3e2 contain the primary
searches. In the assembled delivery, generalizer/ contains the four G
search directories. Each is independently runnable from its frozen input
templates. From the chosen directory, compile and run, for example:

  c++ -O3 -std=c++17 search.cpp -o search_replay
  ./search_replay templates.txt attrs.txt replay 180 14112026

For a G run use 240 and 14122026 instead of 180 and 14112026. Choose a new
output prefix, such as replay, to preserve the frozen search_run files.
The C++ program includes screen_global.cpp from the same directory and
requires no repository checkout. The optional Python preparation scripts
regenerate the templates in the pinned source layout; the assembled
delivery supplies portable paths for those scripts separately.

The reported score adds a source-layout penalty to raw readers minus
compatible folds. Every reported final best has zero penalty. All eight
logs contain zero hits; the explicit hit-recording threshold is 58 effective
readers, and the complete best-score logs separately exclude scores at or
below 60 in the tested run. Thus the narrower hit threshold does not conceal
a 193- or 194-state result. No full physical/source acceptance pass was run
for these larger screened allocations.

An early grammar-only manifest used the old four-increment engine while
scoring changed constructor tags. Its optimistic_total field is expressly
an exploratory old-engine score, not a valid literal-machine count. The
apparent 195-state score for universal tag 2 and equality tag 4 disappeared
when the actual helper cost and compatible folds were charged. Use the
eight-run summary for corrected counts.

The free-constructor audit retags all 15 universal blocks and all three
equality blocks, including the earlier equality helper. It checks complete
emitted formulas and the stack, rather than a bounded list of numerical
examples. A successful recoding lemma still would not establish an iPRA
calibration of a physical table without the separate internal simulations.
The main report supplies the tag-recoding argument and its limitations.

The accompanying MILP work, when present under milp/, is a separate search
over shared-substring dictionaries. Its solver-reported optimum 68 and
matching bound apply to that finite model. They omit physical folds and
are not formal dual certificates or global state lower bounds.

The zero/nonzero register analysis is also a separate negative screen.
It reaches 263,888 abstract contexts of the 3,673-site primary source.
All 36 register pairs may be co-positive in this abstraction; this does
not establish concrete co-positivity or rule out a redesigned eight-register
program. The only always-zero decrement detected is the known cleanup site
3634, already represented in the historical HAZ designs.

ATTRIBUTION

The randomized reassociation and compatible-fold engine is adapted from
the supplied pa194_radix_family_2026-11-13 search scripts. New work consists
of constructor-tag variants, actual multiplier-helper charging, the G
variants, fresh runs, and the associated checks and audit. Original inputs
are pinned to commit 32d0d8b7d93a63ad4106c18cdb29b37927acdad2.

# New 193-state bootstrap investigations

No blank-start consistency machine below 194 states was established. This
folder contains a new exact obstruction for one runtime-core family and
fresh two-/three-edit startup screens. It supplies neither a global state
lower bound nor an unconditional iPRA calibration.

## The fixed runtime core

The input is the previously supplied 193-state runtime core obtained from
primary PA194 by identifying native 301 with 88 and using these rows:

```
88 0 0 L 51
51 0 0 R 122
```

`inputs/runtime193.native.tm` has SHA-256
`50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53`.
Its earlier 4,780 source contracts pass on valid register frames, but its
unchanged blank initialization fails. The changed marker route agrees with
the old route when the next bit is1; initially unallocated fields can instead
present0. This is the actual bootstrap defect.

## An exact obstruction for all 9! register allocations

Run `python3 allocation193_obstruction.py`.

Consider any permutation pi of the nine physical register positions. Change
only the genuine external register-selector targets in the fixed core,
using the selector set obtained from the baseline table: transitions outside
the arithmetic box whose baseline targets belong to
`[51,36,25,48,32,33,22,55,60]`. The new decoder-helper transition88/0 is not a
register selector and is kept fixed. Start at native 74 on blank tape.

For each possible image of physical position7, an exact finite trace is
checked. The trace's ONLY permutation-sensitive row is45/1. Consequently,
any two allocations with the same image of7 have identical entire startup
traces: induction on the trace length shows that every executed row either
is fixed or is that common 45/1 row. The other eight images cannot affect the
trace because their selector rows are never visited before the certified ray.

All nine traces end in state 35 to the right of every written1. Their lengths
are 85, 86, ..., 93 transitions. Row35/0 is 1R35. The machine therefore forever
writes1 while moving right into blank cells, with no opportunity to halt.
This proves the obstruction for all 362,880 allocations of this EXACT core,
with fixed initial control74 and no other table changes. It is stronger than
a bounded simulation failure, and much narrower than a general state lower
bound. Every transition of the nine prefix certificates is retained in
`evidence/allocation193_obstruction.json` and replayed from the literal table.

## Fresh simultaneous-row screens

The 346 replacement actions come from the prior corrected radius-six context
pool. It contains 327 outside-box suggestions and 19 speculative arithmetic-box
suggestions. Their simultaneous semantic validity is not assumed. A search
hit would still require fresh universal runtime verification, an adequate
semantic seed and the unresolved arithmetic calibration.

The acceptance detector requires a COMPLETE physical source frame at one of
source sites 25..44: all finite nonzero tape support must agree, including
both markers, source bits, padding 48+n, all nine unary fields and a nonempty
spare tail. It permissively allows arbitrary values in all nine fields.
The absence of even such frames is a stronger negative screening result
than failure to find the one old clean seed.

Each simulation has limits 200,000 transitions, head displacement 20,000 and
support size 20,000. A reported limit is not a proof of permanent failure.

| Experiment | Tables/simulations | Literal transitions | Halts | Certified rays | Bounded/size-limited | Accepted frames |
|---|---:|---:|---:|---:|---:|---:|
| All distinct-row pairs, start 74 | 58,485 | 87,558,362 | 0 | 58,072 | 413 | 0 |
| All distinct-row pairs, all blank starts via first-write reduction | 468,913 | 129,450,571 | 117,274 | 351,052 | 587 | 0 |
| All distinct-row triples, start 74 | 6,440,096 | 16,572,610,941 | 0 | 6,359,449 | 80,647 | 0 |

For the all-start pair screen, only controls with a write 1 transition on 0
need simulation. From any blank initial control, either no 1 is ever written,
or the configuration at the first such write is a translation of the run
starting at that write-producing control. Translation does not change frame
recognition. Thus this reduction covers all initial controls for the stated
frame search. Prefixes before the first write can only delay a hit.

Reproduce from this directory with a C++17 compiler:

```
g++ -O3 -std=c++17 pair_startup.cpp -o /tmp/pa193-pairs
g++ -O3 -std=c++17 pair_all_blank.cpp -o /tmp/pa193-pairs-all
g++ -O3 -std=c++17 triple_startup.cpp -o /tmp/pa193-triples
/tmp/pa193-pairs inputs/runtime193.native.tm inputs/neutral346.tsv 200000 0 346 inputs/startup_any_frame_templates.tsv
/tmp/pa193-pairs-all inputs/runtime193.native.tm inputs/neutral346.tsv 200000 0 346 inputs/startup_any_frame_templates.tsv
/tmp/pa193-triples inputs/runtime193.native.tm inputs/neutral346.tsv 200000 0 346 inputs/startup_any_frame_templates.tsv
```

The original simulations completed in about 1.64, 2.05 and 241.77 seconds in
the execution environment. Wall times are environment-dependent. Standard
output contains hits (empty here); standard error contains progress and the
final totals preserved in `evidence/`. No additional unrecorded search is
needed to reproduce the results.

## Provenance

Input tables, corrected candidate pool, frame templates and the starting C++
frame recognizer derive from the supplied
`pa_sub194_research_2026-11-13.zip`, at ProveIt commit
`1c9524d8bf2e0a27b9a16ff622359927f536e663`.
The new contributions are simultaneous pair/triple enumeration, the
first-write reduction, and the exact nine-trace proof for all register
allocations. Imported licenses are retained in `licenses/`.

# Fresh physical reduction searches

This directory records additional unsuccessful attempts to obtain a blank-start
machine with at most 193 working states. It supplies reproducible search evidence,
not an arithmetic consistency theorem or a lower bound on arbitrary machines.
The reference repository revision is
`1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.

## 1. Runtime193 bootstrap with up to five row rewrites

The inherited Runtime193 table correctly implements the primary source program
on its prescribed register frames, but its ordinary blank startup fails. The
unchanged-marker obstruction is not solved by a finite simulation.

The new `search_four.cpp` performs an encounter-directed depth-first search with
a parameter specifying the maximum number of edited rows. It uses the corrected
327-candidate non-box pool from the later AX11 study. Earlier work covered
encountered pairs and triples; this run extends the search through quadruples and
quintuples. Conflicting edits to a row are excluded and edit sets are deduplicated.
All these searches start at native state 74 on an entirely zero tape.

The success condition is deliberately broad: the **entire** finite tape must be
an admissible source frame at native state 84 for one of source sites 25--44,
with arbitrary values for all nine work registers, any nonempty spare-register
list, arbitrary translation, and padding at least 48. Thus a hit would still need
its seed values, simultaneous runtime equivalence, and logical calibration
checked. There were no hits.

| Quantity | Maximum four edits | Maximum five edits |
|---|---:|---:|
| Baseline computations | 1 | 1 |
| One-edit computations | 34 | 34 |
| Two-edit computations | 640 | 640 |
| Three-edit computations | 9,013 | 9,013 |
| Four-edit computations | 106,694 | 106,694 |
| Five-edit computations | 0 | 1,098,399 |
| Total computations | 116,382 | 1,214,781 |
| Literal transitions executed | 288,257,204 | 5,462,651,667 |
| Outward blank rays | 62,021 | 465,448 |
| Exact repeated full configurations | 52,800 | 717,898 |
| Cutoffs | 1,561 | 31,435 |
| Literal halts | 0 | 0 |
| Complete source-frame hits | 0 | 0 |

The per-run transition cap is 200,000, with a finite tape-window boundary and a
20,000-one-cell cap. A frame first reached exactly at the transition cap is not
accepted. A cutoff is unresolved beyond its bound, never classified as infinite.
The total number of computations is not the number of all formal five-element
subsets of 327 edits: changes to rows never encountered in the relevant run cannot
change that run. The figures above describe the explicit encounter-directed domain.

Two accelerations have exact justifications:

* An outward ray follows zero-reading transitions all moving in one fixed
  direction until a control repeats; every future cell is untouched blank.
  Every downstream zero row is added to the encounter set, so a later mutation
  can still be explored even if it would interrupt that ray.
* At intervals of 64 steps, small configurations are stored as their exact
  control, absolute head position, and complete sorted one-cell set. Equality is
  exact string equality of this encoding, not a probabilistic hash. Repetition
  proves a deterministic cycle. The complete cycle has already been observed,
  including its encountered transition rows.

The depth-four run was independently repeated before and after adding exact-cycle
recognition. The same 116,382 edit sets were processed. The earlier 54,361 cutoffs
split into 52,800 exact cycles and 1,561 remaining cutoffs, with no change in hits.
The 640 pair and 9,013 triple cases agree with the prior AX11 start-74 study.

Reproduce either run from this directory with GNU C++17:

```sh
g++ -std=c++17 -O3 search_four.cpp -o /tmp/pa193-startup-search
/tmp/pa193-startup-search runtime193.native.tm neutral.tsv startup_any_frame_templates.tsv 4 200000 > four_hits.replay.jsonl 2> four_log.replay.txt
/tmp/pa193-startup-search runtime193.native.tm neutral.tsv startup_any_frame_templates.tsv 5 200000 > five_hits.replay.jsonl 2> five_log.replay.txt
```

The fifth argument names the maximum edit-set size despite the historical source
filename. The implementation supports sizes through five; larger values require
extending the counters and assessing memory use.

## 2. Two-row quotients of the new AX11GH and AX11GHS machines

For each new machine the inherited corrected symbolic collector was rerun at
radii four and six. It includes interior positions of accelerated scans, rather
than only their symbolic endpoints. The source outcomes quantify over arbitrary
register values through the inherited arithmetic-box interface. The arithmetic
boxes retain the conservative windows obtained from blank-tape abstract
propagation. Startup is not added to the narrower source windows.

For every unordered pair of 194 controls, the inherited `joint_return_merge`
synthesizer redirects one control to the other and assigns both rows of the
retained control. Each allowed row chooses a write bit, move, and remaining
working successor. A candidate must realize each original one-step endpoint
within 100 steps without leaving the chosen finite window.

| Machine | Radius | Source windows | Control pairs | Row-action trials | Joint row pairs | Hits |
|---|---:|---:|---:|---:|---:|---:|
| PA194AX11GH | 4 | 8,789 | 18,721 | 23,887,996 | 139,688 | 0 |
| PA194AX11GHS | 4 | 8,830 | 18,721 | 23,579,196 | 129,742 | 0 |
| PA194AX11GH | 6 | 30,755 | 18,721 | 25,753,148 | 181,936 | 0 |
| PA194AX11GHS | 6 | 30,860 | 18,721 | 25,589,484 | 174,778 | 0 |

The collector freshly reproduces 4,778 source outcomes for GH and 4,774 for GHS.
Larger windows, longer detours, a different simulation relation, simultaneous
rewrites of other states, or a different source are outside this finite search.

## 3. A neutral row followed by a two-row quotient

The fresh radius-four neutral-row screen finds 341 putative neutral rewrites for
GH and 298 for GHS. `mutation_search.py` applies each rewrite, then runs the
quotient synthesizer. `freeze_contexts.py` fixes the original machine's arithmetic
windows and combines them with the corrected symbolic source windows, preventing
vacuous checks caused merely by a mutant's failed abstract blank startup.

This phase is **heuristic candidate discovery**. The original windows are reused
after the first mutation; inserted detours may create additional contexts, and
mutated arithmetic rows require fresh block lemmas. A hit could not be promoted
to a machine without complete fresh universal checks and blank initialization.
The completed phase counts are recorded in each `*_neutral_quotient4/receipt.json`.

| Machine | First-row candidates | Control-pair tests | Row-action trials | Joint row pairs | Hits |
|---|---:|---:|---:|---:|---:|
| PA194AX11GH | 341 | 6,383,861 | 8,146,889,752 | 47,793,125 | 0 |
| PA194AX11GHS | 298 | 5,578,858 | 7,028,165,252 | 38,791,359 | 0 |

All 639 prescribed first-row variants completed. There were no timeouts or
partial quotient searches. No putative reduction reached the subsequent
universal-source and blank-startup validation stage.


## Inputs and attribution

The 193-state table is the kept file at
`Computability/BusyBeaver/Research/PA/docs/pa_sub194_research_2026-11-13/runtime193/runtime193.native.tm`.
Its SHA-256 is
`50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53`.
The corrected `neutral.tsv` pool is copied from
`PA/docs/pa194_ax11_research_2026-11-14/research/startup_repair/neutral.tsv`;
its SHA-256 is
`5c209f95fc074bb4dc4f3976c5bd85cf62d68797b3769e6cdde2a549bee97a5a`.
The frame templates are copied from the earlier Runtime193 packet and have SHA-256
`9f04bf6d991c11d50a0e74aa812f3ebe79a21bb2801bbe0f30428bc42ae7d564`.

The new startup DFS adapts the tape-frame detector and search convention from the
AX11 packet's `pair_startup.cpp`. The corrected context collector and quotient
synthesizer are the attributed copies in
`PA/docs/PA194B_PA194G_research_2026-11-14/research/physical_searches/src/`.
The neutral-row synthesizer comes from
`PA/docs/pa_sub194_research_2026-11-13/research/reduction/neutral_rows.cpp`.
Retain the enclosing delivery's upstream and packet licenses when redistributing
those source files and reference artifacts.

## Portable optional replay

The package includes the exact attributed context collector, symbolic executor,
neutral-row synthesizer, and quotient synthesizer under `inherited/`. Python 3.10+
and GNU C++17 are sufficient; no repository checkout or network is needed.
Run from this directory, retaining Python assertions:

```sh
python3 -B replay_quotients.py --output /tmp/pa194-quotients-replay
python3 -B mutation_search.py PA194AX11GH --output-directory /tmp/pa194-gh-neutral-replay
python3 -B mutation_search.py PA194AX11GHS --output-directory /tmp/pa194-ghs-neutral-replay
```

The first command regenerates source windows, compares their exact bytes,
replays all four quotient searches, and checks the deterministic counters.
The latter two use the bundled frozen radius-four windows and put all new output
in the selected directory. They compile the merger in a temporary directory.
`--candidate-root` can select a different directory containing the two machine
subdirectories; by default the delivered `../../machines` directory is used.
The mutation scripts record full per-edit receipts; runtime timings will differ.
The supplied empty hit files and final summaries are the recorded evidence.

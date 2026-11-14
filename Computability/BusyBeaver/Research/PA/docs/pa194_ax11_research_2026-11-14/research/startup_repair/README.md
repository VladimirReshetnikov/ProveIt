# Bounded startup-repair searches for the 193-state runtime core

These are **unsuccessful bounded searches**, included to make the sub-194 research reproducible. They found no complete source frame and do not establish a lower bound on consistency machines.

## Inputs and acceptance condition

The inherited core and frame templates come from `docs/incoming/pa_sub194_research_2026-11-13.zip` in ProveIt commit `2337ce611a26e308697ccbddb2a1636f989f01c3`, within its `pa_sub194_research_2026-11-13/` wrapper:

- `runtime193.native.tm`: `runtime193/runtime193.native.tm`.
- `startup_any_frame_templates.tsv`: `research/reduction/inputs/startup_any_frame_templates.tsv`.
- `neutral.tsv`: the fixed pool from `research/reduction/inputs/runtime193_neutral_source.tsv`, removing its no-edit sentinel and all nine edits of row `(35,0)` rejected by the corrected source-envelope collector, then renumbering entries. **327 edits remain.**

`ax11_runtime193.native.tm` composes the new AX11 source edits with the inherited 193-state runtime quotient. It is only an exploratory core, not an accepted blank-start machine. `no_edits.tsv` is intentionally empty. Input SHA-256 values are in [summary.json](summary.json).

The C++ program simulates the all-zero tape from native start states. A hit must be an entire canonical finite source frame at native state `84`, for one of source sites `25..44`, with all nine register values arbitrary, any nonempty finite spare list, permitted tape translation, and a gap of at least 48. The complete finite support is checked, including the left marker and register/spare encoding. A short local pattern is insufficient.

The search stops a run after 200,000 simulated transitions, at the finite tape-window boundary (head displacement beyond approximately 24,900 cells), when more than 20,000 cells are one, at literal halt label `254`, or upon a directly recognized outward blank self-loop ray. Frame detection precedes each transition but follows the bound check, so a frame first reached exactly at the step cutoff is not accepted by this run.

## Reproduction with GNU C++17

Run the following from this directory. The source uses GNU's `bits/stdc++.h`; `g++` is the intended compiler. Commands write into a separate `replay/` directory and preserve the delivered evidence.

```sh
mkdir -p replay
g++ -std=c++17 -O3 -DNDEBUG pair_startup.cpp -o replay/pair_startup
```

Pair search across all 193 working initial states:

```sh
./replay/pair_startup runtime193.native.tm neutral.tsv startup_any_frame_templates.tsv 2 200000 > replay/pair_startup_hits.jsonl 2> replay/pair_startup.log
```

Triple search with native initial state `74` for the pair/triple phase:

```sh
./replay/pair_startup runtime193.native.tm neutral.tsv startup_any_frame_templates.tsv 3 200000 > replay/triple74_hits.jsonl 2> replay/triple74.log
```

Triple search across all 193 working initial states:

```sh
./replay/pair_startup runtime193.native.tm neutral.tsv startup_any_frame_templates.tsv 4 200000 > replay/triple_all_hits.jsonl 2> replay/triple_all.log
```

AX11-composed core, all 193 starts and no edits:

```sh
./replay/pair_startup ax11_runtime193.native.tm no_edits.tsv startup_any_frame_templates.tsv 0 200000 > replay/ax11_core193_hits.jsonl 2> replay/ax11_core193.log
```

The positional arguments are `table edits frame_templates stage step_bound`. In every stage, baseline and single-edit preparatory runs use all starts. Stage `2` then checks eligible pairs at all starts; stage `3` checks eligible pairs and triples only at start `74`; stage `4` uses all starts for that phase. An empty edit file makes the final command a baseline-only test. Timings printed in the logs are machine-dependent.

## Recorded results

| Experiment | Eligible pair/start runs | New triple/start runs | Total simulated runs, including preparation | Simulated transitions | Hits |
|---|---:|---:|---:|---:|---:|
| Pairs, all starts | 42,648 | 0 | 45,835 | 1,950,774,470 | 0 |
| Triples, native start 74 | 640 | 9,013 | 12,840 | 566,834,684 | 0 |
| Triples, all starts | 42,648 | 516,610 | 562,445 | 50,593,490,055 | 0 |
| AX11-composed core, no edits | 0 | 0 | 193 | 1,587 | 0 |

The pair and triple counters count the runs selected by the program's row-encounter filters; they are not the number of all formal subsets of the 327 edits. An edit is considered only when its transition row can be encountered along the relevant baseline, single-edit, or pair trajectory. Conflicting edits to the same row are excluded, and triple/start cases are deduplicated. The initial single-edit preparation is repeated in each command; do not sum these totals as disjoint experiments. All four delivered `*_hits.jsonl` files are empty as expected.

The all-start triple run reached a search bound in **255,752 runs**; these are unresolved beyond the cutoffs. The AX11-composed core's 193 baselines instead ended in two literal halts and 191 recognized outward rays, with no cutoff.

## Limits of the result

The pool is fixed and omits other row edits, changed source grammars, new tape encodings, different initialization strategies, and combinations of four or more edits. Each pool member originated in a restricted source-neutrality study; simultaneous correctness of pairs/triples is **not assumed**. A startup hit would only nominate a candidate for fresh universal runtime and logical validation. Likewise, failure to reach the specified frame within the bounds does not imply permanent failure and does not exclude a different valid invariant or source entry convention.

These optional C++ experiments are separate from `../../verify_all.py`. The combined verifier validates the two delivered 194-state constructions; it does not rerun these research searches.

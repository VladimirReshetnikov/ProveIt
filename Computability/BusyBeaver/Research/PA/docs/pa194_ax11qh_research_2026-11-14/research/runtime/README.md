# Runtime reduction experiments

These files record bounded reduction searches on the exact PA194AX11QH native table, together with a complete rejection certificate for one proposed 193-state runtime core. They establish no smaller consistency machine and no general state-count lower bound.

The input table is `../../candidate/machine/machine.native.tm`, with SHA-256:

```text
424bd5175bbca161e76af485f1eda03f2f169d90afe80563035b60289361bf07
```

All commands below run from this directory. Python scripts require Python 3.10 or newer and its standard library. The search programs require a GCC-compatible C++17 toolchain; their sources use `<bits/stdc++.h>`. The package's main Python verifier does not require a C++ compiler or rerun these exploratory searches.

## 1. Source context collection

`collect_source_contexts.py` calls the preserved construction symbolic engine and records radius-four tape windows at every observed controller state. It explicitly adds the interior configurations of accelerated constant-symbol self-loops. This matters: observing only the loop endpoints would omit relevant local contexts. Symbolic register interiors and external stream correlations are conservatively overapproximated.

```sh
python3 -B collect_source_contexts.py \
  ../../candidate/machine/machine.native.tm \
  ../../candidate/machine/sites.json \
  ../../candidate/machine/instructions.json \
  fresh_source_k4.tsv 4 > fresh_contexts_k4.json
```

The recorded collection validates all 4,778 source outcomes and contains 8,462 context pairs, with 6,242 accelerated-scan observations. The retained outputs are `ax11qh_source_k4.tsv` and `contexts_k4.json`.

**Scope:** this envelope describes execution from arbitrary source frames. Startup is intentionally excluded. Arithmetic-box states are not narrowed using these observations. The search programs retain their coarser blank-start local closure for states without a supplied source envelope. Any promising edit would require a fresh complete source proof and complete blank-start check.

## 2. Joint two-row quotient synthesis

This search removes one control, aliases it to a retained control, and synthesizes both rows of the retained control. Local simulations may return to that new control repeatedly. They must reproduce the old transition's successor, head displacement, and entire radius-four tape window in at most 120 steps, without leaving the window. Local exit agreement is checked with the final pair of rows, not just each row independently.

```sh
c++ -O3 -std=c++17 joint_return_merge.cpp -o joint_return_merge
./joint_return_merge \
  ../../candidate/machine/machine.native.tm \
  4 120 ax11qh_source_k4.tsv \
  > fresh_quotients.jsonl 2> fresh_quotients.log
```

The recorded run screened 18,721 unordered control pairs, 23,902,664 partial row trials, and 143,951 completed row pairs. It found zero accepted quotients. `ax11qh_quotients_source.jsonl` is therefore intentionally empty; `ax11qh_quotients_source.log` retains the counts.

This search is restricted to its merger scheme, existing target controls, radius-four envelope, and 120-step local simulation limit. Its negative result is not an impossibility theorem for 193 states.

## 3. A neutral row change followed by a quotient

`neutral_rows.cpp` first finds alternative single rows that rejoin the old transition's complete local effect after a positive number of steps. The replacement path cannot revisit the edited control before rejoining.

```sh
c++ -O3 -std=c++17 neutral_rows.cpp -o neutral_rows
./neutral_rows \
  ../../candidate/machine/machine.native.tm \
  4 120 ax11qh_source_k4.tsv > fresh_neutral_candidates.jsonl
```

The retained pool `ax11qh_neutral_candidates.jsonl` has 357 rows; their largest observed rejoining duration is eleven steps. A fresh reproduction with these exact parameters was byte-identical to the delivered pool, whose SHA-256 is:

```text
3ede3bd6ab857b3e3d0f453b3cd01c67e67fddf54fa9b76685d34bc7ee62788b
```

After compiling `joint_return_merge` in this directory, run:

```sh
python3 -B screen_neutral_then_merge.py
```

This runner uses the delivered table, delivered 357-row pool, and delivered radius-four envelope. It writes per-edit material under `neutral_then_merge/` and a new `neutral_then_merge_summary.json`. The recorded run completed all 357 screens and found zero quotient hits; its frozen summary and log are included.

The runner deliberately reuses the original source envelope after the first edit. This is a two-stage heuristic screen: a positive would require fresh universal source verification and complete startup verification. The recorded absence of positives does not exhaust other multi-row transformations or other tape invariants.

## 4. Complete rejection of one 193-state core

`check_startups.py` reconstructs the tested 193-state core from the pinned 194-state table. It aliases state 301 to state 88, removes state 301, sets `(88,0)` to `(0,L,51)`, and sets `(51,0)` to `(0,R,122)`.

```sh
python3 -B check_startups.py --output fresh_startup_rejection.json
```

This does not infer divergence from a timeout. It replays every recorded finite prefix in `new193_startup_rejection.json`, checks the complete final tape, and verifies the outward blank-ray invariant for every claimed infinite continuation.

All 193 choices of blank initial working state are classified: two halt, and 191 reach certified outward rays. No bounded or inconclusive cases remain for those starts. The longest prefix is 93 steps. The intended initial state 74 reaches its outward ray after 92 steps, in state 35 with head coordinate 14 and one-cells exactly `{-3,1}`. Thus merely changing the initial state of this particular core cannot supply the required blank startup. This says nothing about other edits to its startup or a different 193-state design.

## Attribution and retained scope

The searched table is the new PA194AX11QH composition documented in `../../candidate/PROVENANCE.json`. Its compiler, symbolic register engine, and arithmetic-box interfaces descend from the supplied ProveIt PA194 packets and James Chang's PA196 development; the preserved notices are under `../../licenses/` and `../../candidate/licenses/`. The context collector loads `candidate/vendor/symbolic_runtime.py` as a library of symbolic operations; it does not call that file's legacy external-reference loaders.

The search drivers, context treatment, staged quotient experiment, and complete startup-rejection replay are the work recorded in this research run. Their finite results have the scopes stated above. None supplies the missing iPRA-to-Con(PA) calibration.

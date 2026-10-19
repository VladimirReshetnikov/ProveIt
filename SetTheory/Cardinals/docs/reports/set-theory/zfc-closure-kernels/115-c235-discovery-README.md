# Discovery material and rejected controls

The final theorem uses the exact source, fold, startup and unbounded runtime
certificates in the main package. The files here document how invalid shortcuts
were detected and provide a concrete filter for future research.

`replay_counterexamples.py` checks two rejected source layouts on exact finite
frames. It has no external Python dependencies. Supply the extracted pinned
236-state package:

```sh
python3 -B discovery/replay_counterexamples.py \
  --baseline-dir PATH/TO/zfc236-research-20261019 \
  --output-dir rejected-replay
```

Both use nine zero primary registers, first spare zero and extra gap zero.

| Rejected layout | Leaf | Required effect | Incorrect first clean redispatch |
|---|---:|---|---:|
| Four core rotations, seven-zero source run | 648 | Increment logical register 1 | 666 transitions |
| Six rotations containing the 105/123 repair | 195 | Increment logical register 7 | 82 transitions |

The corresponding pinned baseline instructions pass in 584 and 618 transitions.
The second repair also first changes the blank startup action after 12,742 common
steps. Full tapes and literal traces are retained in `evidence/rejected_counterexamples/`.

A visit to state 96 alone is not a clean dispatcher frame. The routines also use
state 96 internally. The checker explicitly distinguishes these visits from a
complete runtime-frame return and bases its counterexamples on the latter.

## Optional fast concrete filter

`finite_runtime_filter.cpp` accepts a literal inherited-label table and a plain
source list with one `path opcode argument` record per line; use `-1` for the halt
argument. Build it with a C++17 compiler:

```sh
g++ -O2 -std=c++17 discovery/finite_runtime_filter.cpp -o finite_runtime_filter
./finite_runtime_filter table.tm sites.txt 0 0
./finite_runtime_filter table.tm sites.txt 1 7
```

The optional arguments choose one of two concrete primary-value profiles and an
extra gap. Each run checks all 8,386 guarded cases but only at those concrete
values and one spare block. It rejects after 20,000 literal transitions or upon
a wrong clean return. Thus a PASS is a finite discovery filter, never a quantified
runtime theorem. The unbounded verifier is `verification/verify_runtime.py`.

The complete restricted negative-search scope is recorded in
`evidence/research_scope.json`. Those profiles and parameter bounds imply no lower
bound on state count. The final construction is reproduced deterministically by
`build_zfc235.py`; stochastic search replay is not needed to reconstruct or prove
the result.

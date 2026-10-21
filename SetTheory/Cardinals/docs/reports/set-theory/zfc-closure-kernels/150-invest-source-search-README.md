# Independent source and physical-allocation search for K217

## Outcome

**This packet does not contain a proved 217-state blank-tape machine.** It records a reproducible attempt to improve the supplied K218 construction. The smallest source DAG found has 205 nodes, matching the input. The smallest physical allocation found has 218 working states. The example tables are exploratory allocations; their complete primitive runtime and blank startup have not been verified.

The useful contribution is a broader search space and reusable machinery: exact open-control-flow grammar classes, shared-grammar dictionary moves, affine and independent-register permutations, a maximum-zero-run feasibility constraint, incremental physical allocation followed by unconditional state bisimulation, and whole-window multistep fold searches. These methods go beyond reassociating a fixed tree one occurrence at a time, but they did not cross the requested state threshold.

The finite input and grammar checks are in `src/verify_packet.py`. The authoritative observed counters are in `results/summary.json` and the individual logs. All counts below are per run; the runs overlap and their counts must not be added to claim distinct search coverage.

## Pinned inputs and provenance

The main input is the ProveIt repository at commit `9adcaff0a72486ecc81242e0eca86e428c74879e`, under `Computability/BusyBeaver/Research/ZFC/candidate-k218`:

- `inputs/sites218.json`: 4,744 primitive occurrences, 23 distinct primitive nodes and 182 distinct internal nodes, for 205 source DAG nodes; maximum address depth 38 and maximum zero run 6.
- `inputs/k218.native.tm`: 218 working states, native start state 0, dispatcher 84, terminal label 254. Its SHA-256 is `2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f`.
- `inputs/k218-row157.native.tm`: the supplied row-157 variant from the same candidate directory.
- `inputs/k218-alternative.native.tm`: the supplied alternative package from `docs/incoming/K218_Contextual_Alternative_2026-10-20.zip`; the extracted source was `K218_Construction_2026-10-20/machine/k218.native.tm`.

Repository: <https://github.com/VladimirReshetnikov/ProveIt/tree/9adcaff0a72486ecc81242e0eca86e428c74879e/Computability/BusyBeaver/Research/ZFC>.

The source model and hash-consed DAG utilities adapt the repository's `k219-source-search/model.py` and `dag.py`. The three modules in `vendor/` are copied unchanged from `k219-continuation-search/compiler-inputs/`; their original comments and license are retained. New search drivers and exporters use these inputs. `SHA256SUMS` identifies the delivered files.

The environment used Python 3.12.14 and GCC/libstdc++ 13.3.0. The Python drivers use only the standard library. The shared-grammar search requires a C++17 compiler.

## Source semantics and safe transformations

The source tree has primitive leaves `CI`, `CD`, `CB`, `CC`, and `CH`. A local control-flow graph records each primitive occurrence in left-to-right order. Nonnegative successors are primitive ordinals; negative successors encode normal return, an escaping break, or an escaping continue. The model implements both an interval-based and an arithmetic full-program successor resolver. Their equality is checked for every extracted source layout.

### Open association

The rewrite

`((A,B),C) <-> (A,(B,C))`

is permitted when `A` has no escaping break and `C` has no escaping continue. The middle factor can have escaping control. These conditions are weaker than requiring all three factors to be closed. The relevant local control graphs, including every external exit, agree. The e-graph does not equate graphs approximately: it uses exact tuples of primitive effects and ordinal successors as class keys, and its exported productions are checked independently in the packet verifier.

The beam driver applies a rewrite globally to every occurrence of a shared DAG node. It admits source costs up to two nodes above the current best, and retains a mixture of the best three costs. All retained roots have maximum zero run at most six.

### Affine block commutation

The affine recognizer accepts increments, sequential compositions of accepted blocks, and simple counted loops that drain one register while adding fixed multiples of its initial value to other registers. Its contract is an exact affine map on all natural register values; its accepted loops terminate for all such inputs. Two accepted blocks may be exchanged when their affine maps commute, checked by exact integer matrix composition. This permits reordering the primitive word, unlike an association-only search.

### Disjoint-register block commutation

The additional independent-register rule exchanges adjacent closed, halt-free blocks when the sets of registers mentioned by their increment/decrement instructions are disjoint. Each block's execution and termination depend only on its own registers. If both terminate, either order produces the same store. If either diverges, both serial orders diverge. There is no intervening halt in an accepted block. This is a partial-computation equivalence, not a claim that the two instruction words or their step counts are identical.

In the original tree there are only two immediately adjacent disjoint-register block pairs; both were already accepted by the affine rule. Rotations can expose new adjacencies, which is why the disjoint rule was also run throughout a beam search.

## Observed source-search results

| Run | Beam width | Seed | Completed levels | Attempted rewrites | Smallest DAG |
|---|---:|---:|---:|---:|---:|
| Open association | 100 | 217 | 25 | 502,952 | 205 |
| Association and affine commutation | 60 | 218204 | 37 | 460,667 | 205 |
| Association, affine and disjoint-register commutation | 60 | 217051 | 37 | 460,117 | 205 |

Every run reached the six-million interned-node cap. An attempted rewrite is not a distinct source program. The interned nodes accumulate over the search, and this count is not the size of any individual candidate.

### Shared dictionaries

Instead of selecting a binary tree directly, the grammar search selects a dictionary of semantic classes. Every selected nonprimitive class must be derivable from selected children using one of its exact productions. The required root must remain derivable. The search tries adding one class and removing one or two classes; selected runs also admit one or two temporary extra classes and later delete them. A seeded beam retains only a bounded frontier.

The closed-sequence model contains 1,698 classes after two saturation rounds: 41 closed atom classes and 1,657 nontrivial words, with 8,869 binary productions. The original source needs 119 serial classes plus 86 fixed source DAG nodes. The open-control model contains 1,587 classes, 23 primitives, and 3,465 productions. Its original dictionary has 182 internal classes.

| Dictionary run | Width | Temporary excess | Completed levels | Distinct dictionaries recorded | Feasibility calls | Improvement |
|---|---:|---:|---:|---:|---:|---|
| Closed sequences | 150 | 0 | 51 | 564,991 | 162,086,292 | None |
| Open control | 200 | 0 | 26 | 394,371 | 182,618,502 | None |
| Open control | 150 | 2 | 21 | 1,543,294 | 116,494,597 | None |
| Prefix-preserving open control, zero-run constraint | 120 | 1 | 26 | 480,008 | 109,905,366 | None |

C++ log levels are zero based; for example the final logged level 25 means 26 completed levels. “Distinct dictionaries recorded” includes candidates not retained in the next frontier. It is not a count of fully expanded source trees or physical machines. These are bounded heuristic searches in finite, partially saturated grammars. They establish no lower bound on source or machine size.

### Geometry and bootstrap prefix

The final model fixes 27 ancestor productions so that the first 37 primitive addresses remain identical to K218. Its zero-run feasibility test propagates the smallest possible initial zero-run for each selected class, using only representations whose internal zero runs are at most six. At a pair, the left leading run gains one and the right run is unchanged. Because every parent only needs this leading-run statistic, choosing the minimum for each class is sufficient; no bounded sample of tape strings is involved.

Preserving these source addresses is a useful constraint for physical allocation. It does **not** itself establish that the physical blank startup remains valid.

## Physical allocation results

The final geometry-constrained search emitted 989 sampled dictionaries. Two deterministic representation policies were applied: prefer old subtrees when possible, or minimize the leading zero-run first. After deduplicating the resulting source bytes, this produced **1,190 distinct layouts**. Every one has:

- 205 DAG nodes and 4,744 primitive occurrences;
- maximum zero run 6;
- the original complete primitive ordinal control-flow graph;
- the original first 37 primitive addresses.

Their maximum depths range from 36 to 42. The incremental allocator successfully checked decoder-prefix bindings for **353** layouts and rejected **837**. A binding rejection is an allocation failure, not a source-equivalence failure.

Every successful allocation was then minimized by unconditional deterministic-state bisimulation: two states may share a class only when both rows have the same writes, directions, and destination classes; the terminal state is kept separate. This gives an all-tape quotient of the allocated table. It changed the state count of 88 allocations. The smallest raw count and the smallest quotient count were both **218**, attained by 36 distinct tables.

This allocator reuses physical roles by source origin. It checks decoder prefixes, and it can reuse a state that has other runtime or startup obligations. Consequently these 353 outputs are **not** 353 established correct machines. A complete primitive-runtime certificate and a blank-startup check remain necessary before any allocation could be presented as a candidate. The two small examples are explicitly marked exploratory.

`results/allocation_final.json` is the complete record for this final pass. Earlier overlapping allocation passes are intentionally omitted from the final census.

## Low-level fold searches

The packet also includes three progressively broader finite-contract search drivers:

1. `two_branch_marker.py` synthesizes both merged-state actions by reusing helpers confined to the previous and current cells. It restores those cells exactly and requires the old one-step endpoint. Candidate role pairs have opposite unique incoming written markers. Changed states cannot occur inside the helper.
2. `general_prefix_fold.py` computes an inductive finite prefix-window invariant from all initial tapes, then searches arbitrary old-state pairs with exact old one-step endpoints. Synthesized helper actions start with a left move; an identical direct branch may also be retained. The supplied runs use radius eight.
3. `stutter_window_fold.py` uses a symmetric window and permits positive multistep old/new joins at the same complete window, head position, and state. Both actions can write either bit, move either way, and enter any existing working state. The new helper interior excludes both edited states. Paths are explored until they leave the known window, halt, or repeat a complete finite-window configuration; there is no arbitrary step cutoff.

The all-initial-tape invariant is computed to a fixed point. When a move exposes a new boundary cell, either bit is allowed. It is therefore an overapproximation; extra abstract contexts can reject a fold that might work on the actual blank execution. No conclusion about all possible folds follows from a zero-hit result.

The two-cell family tested 4,816 ordered pairs for the main table, 4,730 for the row-157 table, and 4,704 for the alternative table; all returned zero hits. The generalized radius-eight one-step family tested 46,872 ordered pairs for each of the three tables, with zero hits. The symmetric multistep family tested 46,872 ordered pairs on the main table at radii three and five, again with zero hits. Finally, it tested the same pair family at radius three on each of the 36 distinct newly allocated 218-state tables, with zero hits. The 36-table count is distinct by table bytes; it does not imply correctness of those input allocations.

The unchanged-helper-interior restriction is significant. This family does not cover every recursive two-action implementation, every possible invariant, or every use of a newly synthesized helper state. The fold searches are negative results within their stated contract systems, not impossibility results.

## Reproduction

Run Python without `-O`, so assertions remain active. From this directory:

```sh
python src/verify_packet.py
g++ -O3 -std=c++17 src/grammar_fast.cpp -o grammar_fast
```

Regenerate the small grammar inputs:

```sh
python src/closed_grammar.py --output replay_closed
python src/open_egraph.py --rounds 2 --output replay_open
python src/pin_prefix.py --model replay_open/model.json --output replay_prefix
```

Replay the recorded dictionary frontiers by level count rather than wall time:

```sh
./grammar_fast models/closed/model.txt replay_closed_search 150 999999 0 0 51
./grammar_fast models/open/model.txt replay_open_search 200 999999 0 0 26
./grammar_fast models/open/model.txt replay_barrier_search 150 999999 2 0 21
./grammar_fast models/prefix/model.txt replay_geometry_search 120 999999 1 1 26
```

The arguments are input model, output stem, width, seconds, permitted excess, geometry flag, and level cap. The original runs used a wall-time budget checked between complete levels; the portable driver adds the optional level cap while preserving the default algorithm. Exact seeded frontier replay assumes the same `std::shuffle` implementation. Wall times are diagnostic and are not expected to reproduce.

Reproduce the final physical allocation pass from the delivered 989 samples:

```sh
python src/compile_layouts.py --samples models/prefix/geometric.samples --model models/prefix/model.json --output replay_allocations --keep-prefix
```

Reproduce the broadest included baseline fold search:

```sh
python src/stutter_window_fold.py --table inputs/k218.native.tm --radius 5 --output replay_folds
```

For the source beams, use `src/search_source.py`, the widths and seeds in the first table, `--rounds 25` or `37`, and a sufficiently large `--seconds` budget. Add `--affine` or `--affine --disjoint` as appropriate. The memory cap remains six million interned nodes. The delivered logs and input hashes are the record of the actual searches.

## Limits and next use

The source-equivalence checks concern register-program behavior. The physical allocation checks concern decoder prefixes. The fold contracts concern specified local simulations. None of these substitutes for the source calculus's consistency calibration, the complete register-to-tape simulation, or blank initialization. Those obligations remain distinct.

The large plateau and the allocation failures suggest that future searches should optimize the physical decoder and its reusable helper roles jointly with source representation. A smaller source DAG is sufficient progress for the current compiler, but it is not necessary: a 205-node source with a different arrangement might expose a fold unavailable in the input. This packet supplies the machinery and measured variants for continuing that route, without claiming that the 217-state target has been met.

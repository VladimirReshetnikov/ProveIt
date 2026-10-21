# K215 state-reduction experiments and nine-head AX source variants

Pinned source: ProveIt `b07002a86bcc96e76a31b57dce23d3b8c2b76fa6`.
This packet contains **no established 214-state machine**. It supplies a broader exact local-fold search, three shorter source variants, their measured allocation costs, and reproducible evidence explaining the remaining obstruction.

## Results

| Source | Primitive occurrences | Distinct source subtrees | Best raw allocation in this protected model | Status |
|---|---:|---:|---:|---|
| Accepted K215 | 4,751 | 202 | 215 | Existing accepted machine; identity control reproduced byte for byte |
| AX9clear | 4,734 | 205 | 218 | Exact source construction; allocated table only |
| AX9additive / AX9+ | 4,732 | 204 | 217 | Exact source construction; allocated table only |
| AX9topbinder / AX9″ | 4,725 | 203 | 216 | Exact source construction; logical completeness also remains open |

An allocation here means that the finite decoder/prefix checks passed, including the inherited eight contextual108 aliases. It is **not** an arbitrary-value primitive-runtime proof, a blank-initialization proof, or an accepted consistency machine. Files under `unverified_allocations/` must retain that status. The larger packet's AX9 discussion supplies the separate source-level logical argument for the first two variants; this subpacket does not substitute a source or allocation test for that argument.

The protected allocation model keeps the inherited engine-row filter and old compatible decoder roles. Its negative results are not lower bounds. In particular, “best raw allocation” refers to the exact unrotated source and tested integer budgets in this model. There may be smaller implementations using different associations, contextual role assignments, engine changes, or encodings.

The biased emitter's new generalization binder is `D + oldTop`; the top-binder emitter's binder is `oldTop`. These are distinct changes of formalism, not plain compiler optimizations. `AX9clear` instead explicitly clears the old top. Its abstract factorization is `AX10 = DROP ; AX9clear`. The analogous factorization for AX9additive needs the incoming cache to be zero; DROP does not generally leave the top zero.

## Local-fold search

`context_fold_search_v2.py` proves 889 individual local-bit implications by finite backwards-transition analysis and examines all 202 state pairs having one equal transition row and one different row. For each pair it tests all 214 retained entries, both writes, and both movement directions: **172,912 candidate replacement rows**. It symbolically explores **4,965,734 configurations**, branching on unknown outside tape bits. No candidate passes both origin cases within the explicit limits: radius4 context, backwards depth12, 96 additional transitions, 14 visited cells, and 4,096 symbolic nodes per case.

A cap exit is inconclusive. These figures describe a bounded template search, not exhaustive Turing-machine minimization. `check_marker_control.py` independently passes the known52/176 marker fold in exactly three steps for either origin. That control adds one selector while deleting one old decoder role, so it remains215 states.

The earlier narrow search is retained separately: 270 predecessor-bit implications,19 eligible pairs,16,264 replacements, plus81 disjoint pair-of-fold combinations using one selector and two direct provider steps. It also finds no reduction. The new three allocated tables were searched by the broader checker; they also produce no exact fold under the same limits.

## Reproduction

Python3 standard library suffices for source and fold checks. Allocation additionally needs NumPy and SciPy; the recorded runs used SciPy1.17.0. Run from this directory with assertions enabled:

```sh
python3 code/build_ax9_sources.py --source inputs/candidate-k215/sites215.json --output /tmp/ax9-source-check
python3 code/check_marker_control.py inputs/candidate-k215/k215.native.tm --output /tmp/marker-control.json
python3 code/context_fold_search_v2.py inputs/candidate-k215/k215.native.tm --output /tmp/context-search.json
python3 code/allocate_portable.py --zfc-root inputs --source inputs/candidate-k215/sites215.json --output /tmp/identity-allocation
python3 code/allocate_portable.py --zfc-root inputs --source sources/ax9clear.json --output /tmp/ax9clear-allocation --fresh 3
python3 code/allocate_portable.py --zfc-root inputs --source sources/ax9additive.json --output /tmp/ax9additive-allocation --fresh 2
python3 code/allocate_portable.py --zfc-root inputs --source sources/ax9topbinder.json --output /tmp/ax9topbinder-allocation --fresh 1
```

Use fresh output directories. `allocate_ax9.py` is the exact hashed adapted allocator used in the retained receipts; `allocate_portable.py` overrides its historical workspace default without modifying it. It requires only the two pinned baseline files shipped under `inputs/candidate-k215/`.

The recorded source-rotation beams contain 16 exact finalists each. They retain the primitive word and both complete guarded CFGs of their own changed source. AX9additive examined34,032 roots and AX9topbinder32,425 roots in 128-wide beams; each stabilized after17 rounds. Neither lowers its DAG count, although each lowers maximum depth47→39. The boundary of the protected selector subtree can be reassociated; it is not claimed literally frozen as one whole subtree. Restore compressed finalist bytes and verify their recorded SHA-256 values with:

```sh
python3 code/restore_rotation_sources.py --input rotation_search/ax9additive --output /tmp/ax9additive-finalists
python3 code/restore_rotation_sources.py --input rotation_search/ax9topbinder --output /tmp/ax9topbinder-finalists
```

All16 earlier additive finalists and all16 top-binder finalists failed the zero-fresh-state protected model. The additive finalization was rerun using compact rotation metadata after an oversized nested-tree trace could not be saved. The completed compact run and its finalist bytes are supplied. Raw counters depend on the stated deterministic beam and its termination; none is a global optimization theorem.

## Provenance

The baseline, source language, allocator ancestry, engine-row filter, marker construction, and source-rotation machinery originate in the pinned ProveIt tree. Exact source URLs and the modifications introduced here are in `FINDINGS.md`. Inherited notices and licenses are retained under `licenses/` and `inputs/candidate-k215/NOTICE.md`. The new work adds the generalized finite-context search, AX9 source edits and external-edge checks, the allocator's zero-variable identity handling and explicit known108 alias acceptance, portable runners, and the measured experiments. New material follows the project's MIT No Attribution terms. No inherited component is relicensed.

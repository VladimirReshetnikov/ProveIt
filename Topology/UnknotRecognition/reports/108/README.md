# Few Nonlinear Columns

## Fixed-Parameter Forest Selection for Compressed Unknot Hierarchies

Research continuation for Vladimir Reshetnikov's ProveIt project, 12 October 2026.

The main deliverable is `article/nonlinear_activation_forests.pdf`, with complete
LaTeX sources alongside it. This package addresses an explicit open problem in
the incoming *Dual Forest Normalization* work: choose the top forest jointly
with positive raw cancellation when a bounded number of columns have three
unit owners.

## Main result

For `k` nonlinear unit-triple columns after free closure, the finite problem is
decidable in

```text
3^k Bell(2k+1) poly(N) = 2^{O(k log(k+2))} poly(N).
```

Here `N` is the complete encoded graph/matrix input length. The graph's rank
and the number of top handles need not be fixed. The proof uses one unit-output
choice per nonlinear column, a distinguished partition block for undemanded
prerequisites, and graphic/partition matroid intersection for shared seed
witnesses. The earlier ordered-event proof gives the alternative factor
`3^k k! Bell(2k)` and is retained as an independently tested comparison.

Additional proved results include exact free-closure preprocessing, extension
to arbitrary nonlinear supports and seed matroids, minimum-weight successful
tree optimization, and native parity/rank preservation. Under the full raw
parity hypothesis, only one Stirling layer of witness partitions is needed.
A uniform bound on the additional seed-rank deficit yields the sharper
`3^k (Delta+1)^(2k)` factor, single-exponential at fixed Delta.
A certified matroidal-closure regime supplies another polynomial case; an
explicit parity-compatible counterexample shows that its stronger hypothesis
cannot be inferred from parity alone.

The weighted optimizer and the matroidal-closure fast path are **proved but not
implemented**. This is a local algorithmic advance, not a completed
quasi-polynomial unknot recognizer. The article states the missing global
hypotheses and twelve further research questions.

## Run the algorithms

Only Python 3.10+ and its standard library are required for the finite code.
Run from this directory or add it to `PYTHONPATH`.

```python
from activation_forests import from_dense, solve_output, verify_output

problem = from_dense(
    3, [[0, 1], [1, 2], [2, 0]], [[1], [1], [1]]
)
result = solve_output(problem, max_work=1_000_000)
if result["status"] != "INCONCLUSIVE":
    assert verify_output(problem, result)
```

`SUCCESS` certifies a tree and complete original-matrix peeling trace.
`NO_FOREST` is an exact obstruction within that supplied finite criterion.
`INCONCLUSIVE` records a resource limit, with no complete certificate. A finite
negative never means that the knot is nontrivial or that all geometric
handlebody-recognition routes fail.

For the optional polynomial-prefix dispatcher:

```python
from integration.bounded_prefix import solve_prefix
from integration.verify_prefix import verify_prefix

result = solve_prefix(problem, max_fallback_work=1_000_000)
if result["status"] != "INCONCLUSIVE":
    assert verify_prefix(problem, result)
```

It first gives the pinned incumbent stopping search at most `len(rows)+1`
nodes, then invokes the FPT fallback. Each incumbent node has polynomial work,
so the abstract unrestricted fallback retains the FPT guarantee. The Python
reference can still return `INCONCLUSIVE` at its recursion limit even without
an explicit work cap. Verification is a separate
required step before using any produced certificate.

## What was observed

| Experiment | Outcome |
|---|---|
| Ordered implementation | 16 methods; 5,129 forest-oracle and 800 Rado comparisons; all pass |
| Output-only implementation | 9 methods; 6,024 forest-oracle comparisons; all pass |
| Maintained 106 full-boundary inputs | Both new solvers reproduce 92 successes and 14 exact negatives |
| 117 native cases, source and full matrices | Output-only completes and checks 232/234 at one million structural units |
| 256 relabelings of one five-tetrahedron source | Both exact methods succeed; existing maximum-weight choice also succeeds throughout |
| Paired timings | 373 inputs × 7 repetitions × 6 methods; all 13,475 complete trials checked |
| Optional bounded prefix | All 490 supplied matrix questions complete and check; the incumbent visits at most nine nodes on this bank |

The finite validation suites overlap; their totals are counts of
algorithm–instance comparisons, not distinct instances. Native matrices from
the same source and relabelings are correlated.

On a native `k=6` stellar case, output-only reduces the ordered prototype's
structural count from 426,223 to 742 and the paired median from 309.743 ms to
0.614 ms. It also finishes two `k=9` cases where the ordered prototype is
capped. However, the incumbent remains faster on most small inputs and solves
the largest stellar case that still caps output-only. The article and raw
timings retain these unfavorable results. Do not claim a general runtime
speedup or silently replace the incumbent.

## Reproduce the finite deliverable

```bash
python reproduce.py
```

This reruns the two independent finite test suites, checks the saved complete
native and relabeling certificates, and evaluates the optional dispatcher.
It writes new records under `reproduced/`, preserving the supplied evidence.

```bash
python reproduce.py --benchmark
```

The optional paired benchmark takes longer. It records new timings rather
than expecting the original wall times to match. Original budgets, method
ordering, seeds, statuses, and input/code hashes are retained in the JSON.

To rebuild the figures and article:

```bash
python experiments/make_figures.py
bash build_article.sh
```

Figure generation requires Matplotlib. PDF compilation requires `latexmk`,
pdfLaTeX, and the standard AMS/Latin Modern/graphics packages used by the source.

## Reconstruct native source geometry

`experiments/study.py` accepts three explicit source locations:

```bash
python experiments/study.py \
  --baseline-fast /path/to/ProveIt/Topology/UnknotRecognition/fast \
  --dual-pack /path/to/ProveIt_Dual_Forest_Normalization_2026-10-12 \
  --homological-pack /path/to/ProveIt_Dual_Forests_Homological_Progress_2026-10-12 \
  --output reproduced/native_study.json
```

Use the pinned versions below. The two package paths refer to the inner
extracted directories containing `native/` and `research/`, respectively.
The relabeling study accepts the same paths. Native geometry reconstruction
is a separate reproducibility tier from replaying the saved finite inputs.

The distributed `results/native_study.json` and `results/relabel_study.json`
contain original **uncapped** counts. Their filenames are shortened from the
working `_uncapped` names retained in some collection metadata. Bytes and
hashes are unchanged. No saturated predecessor input bank is distributed.

## Provenance and integration

Inspected head: `ada929648530f8689c26426e132a1b3e1c69c724`.
Maintained runtime base: `c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5`.
The inspected head only adds the relative-top-handles incoming archive.
The `fast/` tree is `697afe0edf113951dd53f8fe9b4c5011f6227b94`;
all 913 files were checked against their Git blob hashes. All six incoming
archives were checked likewise. See `provenance/`.

`reference/dual_forest/` contains the unchanged finite comparator and verifier
from the pinned *Dual Forest Normalization* archive. Their classical
augmenting-path/Rado primitive is also acknowledged as the basis of the new
cloned implementation. Prior forest normalization, stopping-set completion,
raw source parity, and exceptional-row results are attributed in the article.

`integration/INTEGRATION.md` gives the proposed repository location, API
boundary, row mapping, result semantics, and staged adoption criteria.
`CLAIMS.md` separates new proofs, inherited facts, experiments, and open work.
`MANIFEST.sha256` binds the distributed file contents.

No maintained source file or remote repository was modified by this package.
The proofs are research-draft arguments with independent review and exact
finite checks; they have not been formally verified or peer reviewed.

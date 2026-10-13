# Single-Exponential Activation Kernels for Dual-Forest Selection

Research continuation for Vladimir Reshetnikov's ProveIt project, 12 October 2026.

**Read `article/article.pdf` for the mathematical contribution.** Its self-contained LaTeX source is `article/article.tex`. This is a local matrix/dual-graph selection kernel and integration proposal, not an unrestricted unknot recognizer or a production replacement.

## Main result

For the fixed unsigned cancellation matrix and boundary-rooted dual graph, let `b` count every row incident to a usable column of support at least three. Heavy entries (at least two) are prerequisites and count toward this boundary. A usable column has a unit entry. Let `q` be the number of mandatory source components of the low-column dependency graph, and `r` the graphic rank.

The article proves a one-sided randomized `2^{O(b)} poly(input size, lambda)` local search, improving the audited predecessor's deterministic `2^{O(b log(b+1))}` parameter dependence at the stated randomization cost. With `lambda` uncapped independent rounds, an existing successful tree is missed with probability at most `2^{-lambda}`. Every positive is independently checked against the original discrete matrix and graph. No finite-field computation is trusted as a positive certificate.

When `q = 0` and `r <= b`, the original binary graphic representation is already small enough: the search is deterministic and exact. Its negative frontier certificate is independently checked using graph minors and literal matrix peeling. A separate polynomial mandatory-rank obstruction is also supported.

The reduction, representative-state proof, generic contraction, bit bounds, probability analysis, negative frontier protocol, parity diagnostics, and conditional quasi-polynomial regime are proved in the article. Conventional mathematical proofs are supplied for review; neither external refereeing nor proof-assistant formalization is claimed. Representative-family methods and matroid intersection are attributed as prior techniques.

## Run

Python standard library only; tested under CPython 3.13.5. Run from this directory. No installation or network access is needed.

```sh
python -m unittest discover -s tests -v
python -m experiments.validate
python -m activation_forest examples/repository_loop.json --no-incumbent
python -m activation_forest examples/generic_positive.json --seed 1210
python -m activation_forest examples/repository_loop.json --verify results/repository_loop_answer.json
python -m experiments.benchmark
python -m experiments.render_tables
sh article/build.sh
```

The LaTeX build needs `pdflatex` and standard packages listed in the source. All tables are inline in the TeX, so the source can also be compiled without running the experiments.

The default caps are `max_b=20`, `max_transitions=1000000`, and eight sampling rounds. CLI flags expose these finite caps. The Python API accepts `max_b=None, max_transitions=None` for the uncapped theorem's search. Caps do not bound the cost of reading input or constructing native geometry. Callback cancellation raises through the call rather than returning a forged partial proof.

```python
from activation_forest import Instance, solve, verify_positive, verify_obstruction
import json

with open('examples/repository_loop.json', encoding='utf-8') as f:
    instance = Instance.from_dict(json.load(f))
answer = solve(instance, max_b=None, max_transitions=None)
if answer['status'] == 'SUCCESS':
    assert verify_positive(instance, answer['certificate'])
elif answer['status'] == 'BLOCKED_EXACT':
    assert verify_obstruction(instance, answer['obstruction'])
```

Without a seed the random route uses system randomness. Fixed PRNG seeds in the retained experiments are for reproduction, not a derandomization. The success-probability guarantee requires genuinely independent uniform samples and enough resources to complete the stated rounds.

## Status meanings

`SUCCESS` means a spanning tree and complete private-column peeling schedule were verified for this fixed local input.

`BLOCKED_EXACT` means a mandatory rank obstruction or a faithful low-rank frontier proves this **local** tree-plus-positive-cancellation strategy impossible. It does not prove a source is a non-handlebody or a knot is nontrivial.

`UNKNOWN` means no accepted certificate was obtained: a cap, exhausted rounds, or a random representation that lost a witness may be responsible. In general, negative inputs return this status with certainty. They must proceed to a separate verified fallback in a recognizer.

The field acts only on dual-graph incidence columns. Replacing unsigned intersection counts by field residues is unsound and is not done here. Input digests bind the original counts, not merely their capped categories. Huge integers are transported in hexadecimal when appropriate.

## Executed evidence

The retained run has 71 passing unit tests. The exhaustive/random audit contains 8,061 inputs: 3,117 positives all certified, 3,391 exact local negatives, and 1,553 inconclusive negative inputs. Another 300 planted positive trials all succeeded, using 318 random rounds. These are **not** 8,061 total decisions: unknown outcomes are explicitly retained.

Additional audits cover 16,038 forced matroid-extension queries, 2,369 closure/literal comparisons, 1,951 sampled-independence soundness queries, 255 representative-search/literal comparisons, and all 503 samples in four complete small-field sample spaces. See `results/validation.json`. Unit assertions are not added to these case counts.

`results/benchmark.json` retains randomized-order paired per-query times, batching information, operation counts, source and input hashes, and new/new controls. These timings start from a validated local matrix/graph and include selection and one independent certificate replay. They exclude geometry construction, file I/O and whole-knot recognition.

The eight-arm nonlinear family reduces 6,305 literal distinct seed sets to 255 representative witnesses; its measured median paired time ratio is about 13.49. The maintained five-row loop reconstruction is faster than the audited predecessor's exceptional-order search, but direct testing of its few trees is faster still. The generic positive example favors the predecessor. The very large ratio on a six-edge negative control reflects needless order/partition enumeration on an instance with only six possible trees, not difficult-knot speedup.

Earlier unbatched measurements and earlier **anchored** choice-family controls remain in separately named JSON and run logs. The final choice family is **unanchored and genuinely nonlinear**, with exact-count parity-compatible entries. Its input digests therefore differ from those older controls. Those earlier files are not pooled with final-family measurements or presented as repeated samples of identical inputs.

## Integration and attribution

`INTEGRATION.md` explains the source-authentication contract and explicit non-goals. `integration/records_adapter.py` translates a verified tree into a native record proposal; seven record-level tests were executed. It does not authenticate a triangulation. Full native geometry, Regina comparisons, passive-port replay, and end-to-end recognition were not executed.

`SOURCE_AUDIT.json` pins the maintained repository and records the inspected baseline. The predecessor's code and license are vendored unchanged solely to reproduce comparisons. `CLAIMS.md` distinguishes inherited facts, proved results, implemented operators, measured evidence and remaining obligations. `MANIFEST.sha256` is the delivery integrity manifest; `DELIVERY_VALIDATION.json` records the final checks.

The two incoming archives named `ProveIt_Nonlinear_Activation_Forests_2026-10-12.zip` and `ProveIt_Exceptional_Rows_2026-10-12.zip` were inventoried but not content-audited. No exhaustive priority comparison with those archives is claimed. No upstream repository write was performed.

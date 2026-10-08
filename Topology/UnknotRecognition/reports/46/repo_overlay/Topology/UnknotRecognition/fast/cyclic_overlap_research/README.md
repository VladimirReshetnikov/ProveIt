# Exact shared cyclic-overlap index

This continuation changes the maintained explicit relator-overlap query. It
preserves the existing certificate format and both independent verifiers.
The default query is now exact adaptive search: a fixed-size pairwise base
case, a work-bounded decreasing-length donor prelude, then one shared capped
suffix-link index if the prelude does not finish.

## Algorithm and scope

For distinct target and donor slots, maximize the guaranteed shortening
`2 * overlap - donor_length` over all cyclic rotations and both donor signs.
A new index represents cyclic rotations by length-capped terminal points on a
single suffix-automaton suffix-link tree. At every tree or cap vertex, two
shortest donor records of distinct slots and two target slots suffice to
recover the best eligible pair. Inverse donors are scanned through the
positive index and need not enlarge it.

Let `s` be the number of original relator slots and `L` the total explicit
length. The shared query uses `O(s + L log(L+1))` integer/dictionary operations
and `O(L)` auxiliary storage. This is an expected word-time bound under the
usual expected constant-time dictionary assumption. A deterministic
balanced-map variant gives a conservative `O(s + L log^2(L+1))` comparison
bound for the complete adaptive policy. The supplied Python uses dictionaries;
it does not implement that balanced-map variant or claim an unconditional
CPython hashing bound.

For at most four nonempty slots, the existing pairwise query is already
`O(s + L)` and retains its historical witness choice. Larger lists try donors
in decreasing length. A donor of length `d` cannot improve a known gain `G`
when `d <= G`. The prelude consumes at most
`2 * max(1,L) * (L+1).bit_length()` charged work units plus one charged batch;
unfinished work continues through the exact shared index under the same
resource budget. Failed preparation and scans are included in that bound.

The maximum gain is exact. Equal-gain witness choices can differ between
backends. The final whole-knot audit found no change to the resulting
certificates, including the 141-move Gordian trace. The unchanged verifiers
reconstruct the original presentation and check literal transformations;
they do not trust the index.

This is a local query bound on **explicit presentations**. It gives no bound
on intermediate presentation length, compressed grammar growth, the number
of simplification moves, or completeness of the greedy search. It therefore
does not establish general quasi-polynomial unknot recognition.

## Final measurements

`results.json` is the final audit; `summary.json` and `table.tex` are derived
from it. There are 19 actual knot diagrams, two group representations, four
arms, five measured rounds, and one excluded warmup per arm: **760 measured
whole queries and 152 excluded whole-query warmups**. Every query completed
with the expected answer. The arms are the original pairwise implementation,
a second pairwise A/A control, adaptive search, and the shared index alone.
All arms include fresh PD validation, all recognition stages, search,
independent certificate replay, and any fallback. Imports and corpus
construction are excluded consistently. Overlap search actually activates
on mirror-03, mirror-08, and Gordian; the other cases are controls.

| Final query | Pairwise median | A/A median | Adaptive median | Joint-only median | Median paired pairwise/adaptive ratio |
|---|---:|---:|---:|---:|---:|
| Gordian, explicit group | 830.71 ms | 818.67 ms | 490.70 ms | 931.04 ms | 1.766 |
| Gordian, compressed group | 1357.32 ms | 1311.26 ms | 1045.27 ms | 1487.00 ms | 1.297 |
| Gordian overlap query only | 265.05 ms | 271.97 ms | 62.03 ms | 416.87 ms | 4.232 |
| Synthetic 128 by 64 letters | 2066.90 ms | 2113.14 ms | 231.60 ms | 185.60 ms | 8.798 |

A median paired ratio is the median of within-round ratios, not the ratio of
the displayed medians. The whole-query improvement is supported by the
actual 141-crossing PD and independently verified complete certificates.
The synthetic list is an exact string-query capacity experiment, not a
hard-knot benchmark; its random signed words need not be freely reduced.

Gordian reaches the overlap query after 129 eliminations, with 12 nonempty
relators and total length 17,504. The selected donor length is 3,726; target
length is 4,260; overlap is 3,362; guaranteed gain is 2,998. The prelude
builds four donor-orientation automata instead of the incumbent's 24.
Charged query work drops from 785,607 to 154,490.

The shared index alone regresses on the whole Gordian queries, and the
adaptive query regresses on the small synthetic 8-by-64 case (9.81 ms versus
8.25 ms). These results remain in the raw data. Across the other 18 actual
cases, summed medians are 37.29/36.72 ms for pairwise/adaptive explicit search
and 140.00/141.84 ms for compressed search. Those are sums of per-case medians,
not measured batch times; they support no broad small-case acceleration claim.

`calibration_results.json` records the first complete audit before adding the
fixed four-slot base case. That audit exposed avoidable small-core overhead;
`calibration_index.py` exactly matches the source hash recorded for that
version. It is archival evidence and is not the production module.

## Reproduce

Run from `Topology/UnknotRecognition/fast` in the pinned baseline checkout
`58ee11a97d5fd7f21647c57eefaf3ecc007931d6` with the supplied changes applied.
The benchmark records the baseline source hash, current source hashes,
Python/platform information, input diagrams and word lists, raw arm order,
all timings, operation counters, and full certificates. It asserts that all
measured source hashes remain unchanged during the run.

```sh
PYTHONPATH=tests:. python -B -m unittest test_cyclic_overlap_index test_relator_overlap -v
PYTHONPATH=tests:. python -B -m unittest test_relator_power test_adaptive_group test_group_certificate test_compressed_search -v
python -B cyclic_overlap_research/benchmark.py --output cyclic_overlap_research/results.json
python -B cyclic_overlap_research/make_summary.py
```

The final index/overlap gate passes 12 tests in 4.814 seconds. These include
7,056 exhaustive short word pairs; 350 independently brute-forced multi-slot
queries; 600 larger differential queries; inverses, powers, duplicated slots,
seams, clipped windows, global/local exhaustion, both full certificate
replayers with producers disabled, forged witnesses, and the fixed-slot route.
The earlier related group/compressed gate passes 23 tests in 4.522 seconds.
See `index_tests.log` and `related_tests.log`; the package's broader integration
report records the full-suite gate separately.

Use individual backends directly when auditing a query:

```python
from fastunknot.group_certificate import _Budget
from fastunknot.relator_overlap import overlap_move

budget = _Budget(lambda: None, max_letters=200_000, max_work=20_000_000)
statistics = {}
move = overlap_move(words, budget, backend="adaptive", stats=statistics)
# backend="pairwise" retains the original query; backend="joint" isolates the new index.
```

The direct input is an explicit list of signed-generator words; success is
only a presentation move. A knot verdict requires reconstruction and replay
of a complete certificate from a validated classical knot diagram.

## Follow-up problems

1. Construct a shared *fully compressed* cyclic index with complexity bounded
   by grammar size and logarithmic represented lengths, while retaining slot
   exclusions and arbitrary donor signs.
2. Maintain exact slot summaries after relator deletion and replacement,
   including occurrences that disappear; rebuilding the full index is the
   current conservative strategy.
3. Derive a predictor for the pairwise-versus-shared crossover from certified
   structural summaries, and evaluate it on a separate diagram corpus.
4. Find topologically justified classes whose explicit presentation length
   and successful move count stay quasi-polynomial in diagram size.
5. Add independent compressed certificates for inverse-index matches, so the
   local query's correctness can be checked without materializing long words.

`theory.tex` supplies the detailed proof fragment and `table.tex` the numerical
table for the accompanying article. Standard suffix-automaton ingredients
should be cited to Blumer et al., *The smallest automaton recognizing the
subwords of a text*, Theoretical Computer Science 40 (1985), 31–55,
DOI 10.1016/0304-3975(85)90157-4, and the suffix-automaton treatment in
Crochemore and Rytter's *Text Algorithms*, Chapter 6. The capped distinct-slot
reduction and bounded integration are presented as this continuation's
algorithmic contribution, without an unsupported claim of global priority.

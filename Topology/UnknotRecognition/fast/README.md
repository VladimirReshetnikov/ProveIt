# fastunknot 0.3.0: braid and structural certificates with optional shared backends

This research continuation adds a linear signed Seifert-graph certificate before
the established recognition pipeline and three optional Khovanov backends.
The new front end completely decides homogeneous input diagrams after validation.
When inconclusive it continues the original stages. Disable it with `--no-seifert`
or `use_seifert=False` to retain the previous stage order.

If the initial Reidemeister I/II pass removes crossings but does not finish,
the pipeline repeats the structural check before matrix filters. Cancelling
pairs can expose homogeneity. Evidence under `seifert_after_reduction` describes
the reduced diagram: replay `reidemeister_trace` with `fastunknot.simplify.replay`
before passing that certificate to `verify_seifert_certificate`. An unchanged
diagram is not checked twice. The integrated suite now has 539 passing tests.

New RIII trace entries include `triangle`, the three dart indices of the
chosen face in the original input diagram. Crossing indices alone can name
two different legal faces. Replay validates the specified face and accepts
older crossing-only RIII records only when the face is unambiguous. R1/R2
records retain their existing format. The causal RIII search proposed in
report 27 is still under review; this change fixes certificate replay.

The incoming radical-transfer report contributes exact binary prediction of
the objects surviving cancellation. `--reduction adaptive` (Python:
`reduction="adaptive"`) starts sparse cancellation and switches to that
prediction after its per-stage Schur-update allowance is exceeded. If the
survivors have no adjacent degrees, or the boundary is closed, their zero
differential is constructed directly. Otherwise cancellation resumes from
the saved partial complex. This works in both recognition and raw homology;
it requires the standard backend, minfill, bits, and race=1. It is distinct
from `--no-reduction`, which disables Reidemeister simplification.

`--reduction residue` predicts eagerly and is retained for comparison;
`--reduction standard` remains the default. The switch counters and ordinary
work counters are recorded in scan evidence. Dense two-term test complexes
benefit greatly, but eager prediction slows ordinary diagram scans, and no
general recognition or complexity improvement is claimed. See
[`../synthesis/radical.tex`](../synthesis/radical.tex) for the correctness proof,
the adaptive policy, and the incoming report's stronger hypotheses.
Run `python benchmark_residue.py --output results/residue_local.json` to
compare standard, eager, and adaptive modes with paired controls.

The later dense-algebra report adds a verified homogeneous multiplication path
inside component contraction. Inputs of a single dot degree use a binary subset
transform with a cardinality filter; products in the top degree use a packed
complementary-subset inner product. Mixed inputs retain the ranked transform.
The current scanner's erased quantum shifts were recovered and checked on 520
scans (196,928 entries). This also sharpens the article's sufficient sharing bound.
Use `benchmark_homogeneous.py` and `audit_grading.py`, each with `--output FILE`,
to reproduce the local measurements and checks. The same contraction options
apply; the default sparse engine is unchanged.

The mixed-degree synthetic matrices in the original adaptive benchmark cannot
be genuine scan differentials. `benchmark_adaptive_graded.py --output FILE`
adds dense scalar matrices satisfying the recovered grading constraint, with
local adaptive gains of 2.7–58.5×. These are still synthetic complexes, not a
claim that the current crossing order produces that density. Ordinary forced
component scans show mixed timing results, so these measurements do not justify
changing the default engine. Full proofs and results are in
[`../synthesis/homogeneous.tex`](../synthesis/homogeneous.tex).

Report 08 adds complete recognition for checked source braids on at most three
strands. `Diagram.from_braid` and braid JSON retain validated provenance, so the
pipeline uses a linear symbolic decision before the Seifert stage. The raw-word
API `braid_certificate(strands, word)` avoids PD construction. For more strands,
the initial stage supplies a writhe obstruction; optional checked endpoint
destabilization runs after the cheaper diagram and structural tests.
Use `--no-braid`, `--braid-backend matrix`, or `--no-braid-reduction` to control
these stages (API: `use_braid`, `braid_backend`, `use_braid_reduction`). A PD-only
input never acquires an unchecked source word. `to_json(preserve_braid=True)`
explicitly retains provenance; default JSON stays PD. The specialization does
not give a general quasi-polynomial algorithm.

`benchmark_braid.py` measures fresh diagram construction plus recognition
against the current Seifert-enabled pipeline with braid dispatch disabled.
The local nine-round data in `results/braid_integration_20261007.json` show
3.30–4.89× gains on five scrambled three-braid unknots with default RIII enabled,
1.23–1.35× on positive three-braids, and 6.14× on the hard eight-crossing fixture.
A 256-strand stabilization control is about 2.8% slower. Import/startup and JSON
parsing are excluded; the script also records separate raw-word scaling.

Report 09 adds checked Gauss-interlacement factorization as the default visible
sum decomposition, with `connected_sum_factorization` certificate evidence.
Use `factor_backend="legacy"` or `--legacy-factor` for the historical cut traces.
The modular Alexander filter uses sparse elimination at 256 crossings and above;
its low-level API retains explicit `backend="dense"` and `backend="sparse"` choices.
Preprocessing and factorization now share the cooperative `UNKNOWN` resource
handler. Run `benchmark_factor_sparse.py --output results/factor_sparse_local.json`
for isolated paired kernel measurements.

```bash
python3 -m fastunknot recognize examples/trefoil.json
python3 -m fastunknot khovanov examples/conway_sum_8.json --shared
python3 -m unittest discover -s tests -v
```

Recognition accepts `--backend standard|shared|saturated|euler|twist`. The default is
`standard`: sharing incurs overhead on prime examples that stay connected.
`shared` retains exact ranks and raw homological-degree counts. `saturated`
retains the final unreduced rank capped at three. `euler` adds an optional exact
suffix-Euler lower bound, controlled by `--euler-max-states` (default 4096).
A capped count of three means “at least three”; it is never an exact rank.
An early Euler result uses `rank_lower_bound_capped`, distinct from final
`rank_capped`. Exhausting the optional inference budget continues complete
saturated scanning; object/time exhaustion returns `UNKNOWN`.
The Euler backend now computes each completed matching's exact Euler value
from the classical closure's component count and crossing-sign parity in
linear time, avoiding suffix smoothing enumeration. The query budget counts
completed matchings. The original `SuffixEuler` recurrence remains available
as an independent reference; both prepare geometry lazily within the budget.
`euler_stats.prepared_stages` records the number of prepared stages.
`python benchmark_euler_setup.py --output results/euler_setup_local.json`
measures this setup separately from full recognition, with allocation peaks
measured outside the timing samples.
`python benchmark_euler_connectivity.py --output results/euler_local.json`
compares the raw Euler-assisted scans with the earlier recurrence implementation.

Shared backends require minimum-fill pivots, bit algebra, no tail contraction,
and no racing. Incompatible options are rejected. `khovanov --shared` cannot
be combined with `--factor`. Backend selection only matters after enabled
earlier stages have failed to decide; use the disabling flags in the companion
article to isolate a backend deliberately.

The new functions live in `fastunknot.seifert`, `fastunknot.component_scan`,
and `fastunknot.euler_scan`. The Seifert APIs are also exported from `fastunknot`.
Public PD scanner functions assume a validated classical one-component diagram.
The permissive `Diagram(pd)` constructor does not validate this promise; use
`Diagram.from_pd` or the command-line loader.

The maintained article is [`../synthesis/report.pdf`](../synthesis/report.pdf),
with source in `../synthesis/structural.tex`; the delivered report remains in
`../reports/07/paper/`. Run `python benchmark_structural.py --output results/local.json`
for paired recognition timings and exact scanner checks against the integrated code.
`python benchmark_reduction.py --output results/reduction_local.json` isolates
the post-reduction check against the first integrated revision.

The companion article proves exactness and a finite-type complexity bound in
frontier size and actual connected-component size. **There is no general
quasi-polynomial complexity guarantee.** All 69 unit tests passed in the
recorded environment. The research archive includes proofs, raw timing samples,
source provenance, and a patch against the pinned ProveIt baseline.

## Inherited documentation and performance history

The following version-0.2 documentation is retained as the record of the
previous pipeline and measurements. Stage-order descriptions below predate
the new optional and structural stages just described.

# fastunknot 0.2: exact unknot recognition with a scanning Khovanov backend

**Status: exact, complete, and exponential in the worst case. The `n^O(log n)`
bound announced in Lackenby's February 2021 talk is NOT achieved here**, for the
reasons documented in the synthesized report (`../synthesis/`): the accelerated
hierarchy operations in the talk's final flowchart have no published
algorithmic specification with cost bounds.

Version 0.2 integrates the ideas of the nine acceleration proposals in
`../proposals/` that gave a measurable speedup. The 36-crossing braid closure
that version 0.1 abandoned after 600 seconds now takes under a second; full
recognition of the Conway and Kinoshita–Terasaka knots went from about 60 ms to
about 1 ms; a connected sum of three Conway knots from 58 s to 2.5 ms. A Rust
port is in `../rust/`.

## Pipeline

1. **Validation.** One component, spherical rotation system. Inputs: PD code,
   braid word, or rectangular (grid) diagram.
2. **Reidemeister I/II reduction**, incremental: O(1) work per move on a
   mutable dart structure, one revalidation at the end. (A search for
   Reidemeister III moves that unlock further I/II moves runs later, between
   steps 7 and 8, when no filter has decided.)
3. **Descending-diagram test**, linear time; sufficient for `UNKNOT`.
4. **Visible connected sums.** Two edges bordering the same two faces cut the
   diagram into summands. A sum is trivial exactly when every summand is, so
   the summands are examined separately, smallest first.
5. **Modular Alexander test.** The first Alexander minor at t = −1 and at a
   generic element of F_p, p = 2^61 − 1. For the unknot it is ±t^k; anything
   else certifies `KNOTTED`. O(n³) field operations.
6. **Modular Jones test.** The Kauffman bracket at a generic A in F_p by a
   frontier scan that merges partial states with equal boundary matchings.
   Cost is bounded by all perfect matchings of the scan
   boundary, `(w-1)!!` (no multiplicity factor). A Catalan bound requires
   a certified common disk boundary, which the current order does not supply. Skipped above 4096 frontier
   states. Rejects knots with trivial Alexander polynomial such as the Conway
   knot.
7. **Exact Alexander polynomial** over Z[t] (fraction-free Bareiss).
8. **Reduced Khovanov rank over F2** by Bar-Natan scanning with delooping and
   Gaussian elimination: bit-packed morphisms, compiled gluing plans, min-fill
   (Markowitz) pivots, units treated as involutions. `UNKNOT` iff the reduced
   rank is 1 (Kronheimer–Mrowka plus universal coefficients).

Every verdict is exact. Filters 5–7 can only say `KNOTTED`; agreeing with the
unknot's value is never evidence of triviality, and an exhausted filter budget
just skips the filter. Optional ceilings (`--max-objects`, `--seconds`) turn an
expensive step 8 into `UNKNOWN`, never into a knot verdict.

## Run

Python 3.10+, standard library only. From this directory:

```sh
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/conway_sum_3.json --no-jones
python -m fastunknot recognize examples/hard_unknot_8.json --check-d2
python -m fastunknot khovanov examples/stress_braid5_36.json
python -m fastunknot khovanov examples/conway_sum_8.json --factor
python -m fastunknot jones examples/kinoshita_terasaka.json
python -m fastunknot alexander examples/figure_eight.json
python -m unittest discover -s tests -v
python ablation.py        # about 40 minutes: the LIFO rows hit their 300 s caps
python crosscheck.py 400  # default scanner against the generic and the 0.1 scanners on random closures
python ab.py HEAD         # interleaved A/B timing of the working tree against a git revision
python perf.py label      # sequential best-of-N timing with a control loop; see the caveat below
python cli_ab.py HEAD     # whole-process timing of the command line against a git revision
python hard_unknots.py    # scrambled unknot braids that no filter decides (pipeline timing inputs)
```

Exit codes: 0 for either exact verdict, 2 for invalid input, 3 for `UNKNOWN`.

Switches of `recognize`: `--no-reduction`, `--no-descending`, `--no-factor`,
`--no-alexander` (both Alexander stages), `--no-modular` (only the modular
one), `--no-jones`, `--jones-max-states N`, `--pivot {minfill,lifo}`,
`--algebra {bits,sets}`, `--tail N`, `--max-objects N`, `--seconds S`,
`--check-d2`. `khovanov` takes `--factor`, `--pivot`, `--algebra`, `--tail`,
`--check-d2`. `--algebra sets --pivot lifo` reproduces the 0.1 scanner.

## Input

```json
{"pd": [[1,4,2,5], [3,6,4,1], [5,2,6,3]]}
{"braid": {"strands": 3, "word": [1, -2, 1, -2]}}
{"rows": [[0, 2], [1, 3], [2, 4], [0, 3], [1, 4]]}
```

PD crossings are counterclockwise `[a,b,c,d]` with the under-strand `a-c`
(either under-port may come first). Grid rows are listed bottom to top;
verticals pass over horizontals. `{"pd": []}` is one crossing-free circle.

## Complexity

* Steps 1–5 and 7: polynomial in the crossing number n.
* Step 6: at most n · (w-1)!! · poly(w) field operations for scan width w.
  The older unconditional Catalan claim was refuted by report 09; it requires
  a certified disk frontier.
* Step 4 with step 8: if the visible factors have n_1, …, n_k crossings, the
  cost is poly(n) + Σ 2^O(n_i). Polynomial when every factor has O(log n)
  crossings; this is a restricted-class statement, not a bound for all diagrams.
* Step 8 in general: 2^O(n). The size of the complex after elimination is
  (number of boundary matchings) × (a multiplicity that grows with the
  homology of the partial tangle); no subexponential bound is known or claimed.

## Test and benchmark status (last observed 18 September 2026)

* `python -m unittest discover -s tests`: 41 tests, OK (about 9 s; one test starts race processes), about 3 s (CPython
  3.14.4, Windows 11). 19 are the 0.1 tests (three expectations updated because
  a filter now decides before Khovanov does), 22 are new and compare every new
  code path with the 0.1 implementation.
* `results/benchmark_0.1.json` is the 0.1 benchmark, kept as a record; its
  36-crossing 5-strand row is the 600 s timeout that motivated 0.2.
* `results/ablation.json` is the per-idea ablation (see the report). It takes
  about 40 minutes because the LIFO configurations on the stress case run into
  the 300 s cap; shorten the list in `ablation.py` if that matters.
* `python crosscheck.py 400 7`: 400 random braid closures (2 to 5 strands),
  ranks by degree of the default scanner (with `tail` 0 to 2 and `check_d_squared`
  on every fourth) equal to those of the generic scanner, 0 mismatches.
* **Timing caveat, learnt the hard way on 18 September 2026.** On this desktop
  the speed of pure Python drifted by more than a factor of two inside a single
  one-minute run (background applications, clock throttling): a fixed control
  loop went from 5.3 ms to 12 ms. Sequential before/after runs of `perf.py` are
  therefore not evidence. `perf.py` times that control loop next to every case
  and marks a run `SUSPECT` when the control spreads by more than 10%; three
  rows of `results/perf_log.json` are flagged as contaminated. Use `ab.py`,
  which times old and new alternately in one process (`results/ab_log.json`).
  Its first criterion, "interquartile range of new/old entirely below 1", was
  too lenient and **gave false claims in both directions**: a change confined
  to order selection, which is 0.2 to 1.8% of the affected scans and was
  measured on its own as 32 to 58% faster with identical output, was reported
  as 14% slower on one input and 4% faster on another. `ab.py` now also times
  the old code twice per round (an A/A control; on mid-sized scans identical
  code differed by 20 to 30% between adjacent runs) and claims a difference
  only if the order-statistic 95% confidence interval of the median excludes 1
  and the median lies outside the A/A interquartile range. `python ab.py OLD
  NEW` compares two revisions; the earlier "7 to 13% on small scans" claim
  below was re-tested that way and holds (0.87 to 0.92, intervals within
  0.87..0.95; no claim on the large scans). Deterministic counters are immune to this, but each
  sees only part of the work: `stats["compositions"]` counts elimination work
  and `stats["entries"]` the differential entries written while adding
  crossings. Neither alone predicts time: on the 41-crossing 4-strand closure
  the scan order with the fewest compositions (1565 against 4164, equal peak
  size) was not the faster one.
* Measured and left unchanged (deterministic counters, ranks identical in every
  variant). Pivot rule: the product cost (out-1)(in-1) with last-in-first-out
  inside a cost bucket is best or within 2% on four inputs; first-in-first-out
  needs 64% more compositions on the stress case and the sum cost is worse on
  all four. Scan-order selection: scoring greedy orders by the sum of
  2^(boundary/2) selects the same start crossing as the current (maximum,
  total) rule on all four inputs. On the 31-crossing 6-strand closure another
  start needs a tenth of the compositions, but its boundary profile is worse
  than the selected one, so no boundary-based score can find it. On the stress
  case 16 of the 36 greedy starts finish within 4 s; starts 14 to 16 tie for the
  least work (23710 compositions) and the default, which scores every third
  start, selects 15. The score is a fragile predictor: start 0 has profile
  (8, 230) against the winners' (8, 226) and needs 895182 compositions, 38
  times more, with 2.6 times the peak size.
  Scoring all greedy starts instead of 12 was tried on 40 random closures (25 to
  39 crossings, 3 to 6 strands; work = entries + compositions): a different
  order in 18, of which 8 with equal work, 6 cheaper, 4 dearer, ratios from
  0.29 to 6.69, total 0.952. Not adopted: the total is carried by three inputs
  and would change sign without one of them. The weak point is the score, not
  the number of starts. A matchings-only simulation cannot replace it: the
  38-fold gap above occurs at equal boundary size (at most 14 matchings), so it
  is all multiplicity, i.e. homology of the partial tangle.
* Where the transfer work goes (four inputs): 74 to 83% of the differential
  entries are incident to a cancelled pair when it is cancelled (an
  overestimate, since fill-in entries are counted but not in the denominator).
  Only 30 to 53% of the cancellations are between the two smoothings of one old
  object, the kind that could be predicted before writing any entries; the rest
  are between different old objects.
* Outside the scanner (`ab.py`, strict criterion, against c9572d2): the modular
  Alexander filter now evaluates only the nonzero matrix entries, at most three
  per row (`recognize T(3,61)` 0.60, interval 0.53..0.67; `recognize conway`
  0.92); the boundary profile of a greedy scan order is tracked inside the
  greedy in O(1) per step and a candidate start is abandoned once it cannot
  win (`scan chain256` 0.78, interval 0.73..0.82). Both are output-preserving:
  same determinants, and identical greedy orders, profiles and selected orders
  on 600 random diagrams (19993 start orders, 34 diagrams with loop edges).
* The Jones frontier scan now uses the interned matchings and strand-following
  gluing of `planar.py` instead of a union-find over labels per transition:
  0.67 (interval 0.46..0.72, 10 rounds) on the 36-crossing closure, where the
  scan is a few milliseconds. **No measurable effect on any `recognize` case of
  the corpus**, including the Conway knot, which this filter decides: with 11
  crossings the filter is a small part of 0.6 ms. Output-preserving: identical
  return values on 500 random closures (350 witnesses with equal bracket, peak
  states and transitions; 122 inconclusive; 28 identical budget failures; 48
  diagrams with loop edges). `filters._glue` is kept as the reference.
* The Alexander matrix is now built by sparse rows (`alexander_rows`); the dense
  `alexander_matrix` of the exact path derives from it, and the modular filter
  fills a zero matrix directly, evaluating each distinct entry polynomial once:
  `recognize T(3,61)` 0.69 (interval 0.62..0.72) on top of the 0.60 above, no
  claim on the small diagrams. Output-preserving: dense matrices, filter
  results and exact polynomials identical on 500 random closures (35 with
  kinks, where entries of one row coincide and can cancel).
* **Cross-stage plan cache (`shape_cache`, on by default; a trade-off, not a free
  win).** Every crossing brings new edge labels, so a per-stage cache never
  hits across stages, yet a long braid compiles the same few pictures at every
  crossing (at boundary 6 there are 5 matchings, and about 35 transfer plans
  were compiled per crossing of T(3,n)). Transfer plans are now also cached
  under a label-independent key (matchings and crossing slots relabelled by
  rank). This is sound because relabelling by rank is monotone and the circle
  numbering is by minimal label whichever matching is walked first (tested on
  random matchings, and on 20000 pairs while developing). Reuse: 80% of the
  plans of T(3,11), 94% of T(3,31), 72% of T(4,9), 99% of the kink chain, 38%
  and 19% of the random 3- and 4-strand closures, but 1% of the stress closure
  and 0% of the Conway knot, Kinoshita-Terasaka and Conway#Conway. `ab.py`,
  three runs agreeing: `scan T(3,11)` 0.61 (interval 0.59..0.66), `scan
  chain256` 0.78, `scan braid3_40` 0.97; **`scan conway` 1.06 (interval
  1.04..1.07 with 301 pairs) and `recognize hard_unknot_8` 1.07, slower**; no
  claim on the large scans. The cost was decomposed by timing partial variants
  against HEAD (A/A 0.999): ranking the boundary each stage +1.5%, building the
  key and looking it up +3.0%, storing +1.3%. Two explanations I had offered
  first were wrong and are recorded as such: hashing of nested tuples
  (interning shapes as integers changed nothing) and the cyclic garbage
  collector (same ratio with it disabled). Inlining the lookup changed nothing
  either; `shape_cache=False` restores the old speed exactly (1.003).
  **Correction, same day.** I first wrote here that an automatic switch was
  impossible, having tested one predictor: an early hit count predicts the
  wrong way (inputs that profit get their first hit after 35 to 150 lookups,
  the stress closure gets 12 hits in its first 64 and then none). A different
  predictor works. A plan can only be reused in a stage whose picture (the
  position of the four crossing slots among the boundary points, up to monotone
  relabelling) occurred before, and that is known from the scan order alone:
  `ordering.repeated_stages` gives 0 for the Conway knot, Kinoshita-Terasaka
  and Conway#Conway, 1 of 36 for the stress closure, 4 of 31 and 11 of 41 for
  the 6- and 4-strand closures, 16 of 40 for the 3-strand closure, 16 of 22
  for T(3,11). `shape_cache=None`, now the default, turns the cache on when the
  diagram has at least 16 crossings and at least an eighth of them repeat.
  Transfer and composition *results* are shared across stages as well, but only
  after the first plan-shape hit of the scan, since before that a shared
  result cannot exist (ungated this cost a further 2.6%, intervals
  1.023..1.029). Against the code before any of this (1ca6a5d), 301 pairs:
  `scan T(3,11)` 0.505 (0.486..0.508), Conway 1.008 (1.005..1.010), hard
  unknot 1.007; `ab.py`: T(3,11) 0.51, `scan chain256` 0.81, nothing slower.
* **The exact Alexander polynomial is no longer computed after the modular test
  has passed** (`use_exact_alexander=None`; `True` or `--exact-alexander`
  restores it; with `use_modular=False` it still runs). It can only say
  `KNOTTED`, and only for a polynomial that is not a unit, which the modular
  test has just failed to see at two points; whatever it would have caught the
  exact scan decides anyway, so verdicts cannot change. The corpus had a single
  filter-undecided input, of 8 crossings, which hid this stage's cost:
  `hard_unknots.py` now generates scrambled unknot braids, about half of which
  survive R1/R2 with 15 to 27 crossings and pass every filter. On 26 of them
  the exact polynomial took a median 24% (up to 63%) of `recognize`. Over 720
  diagrams (600 random closures, 120 scrambled unknots) the two modes never
  disagree and the exact stage decided nothing once the modular test had
  passed. `recognize` on the 55 scan-decided scrambled unknots: faster on all
  55, median 0.81, range 0.53 to 0.93; `ab.py`: 0.62, 0.84, 0.85 on three of
  them, `hard_unknot_8` 0.86. The evidence record says "not computed" instead
  of giving the polynomial and the determinant.
* A caveat on `ab.py` even with the strict criterion: that run flagged
  `recognize conway` as 1.05 slower (interval 1.005..1.254), a path this change
  cannot reach. 301 pairs gave 1.006 (1.000..1.015). With some 15 comparisons
  per run at 95%, expect an occasional false flag on sub-millisecond cases and
  confirm a flag with a few hundred pairs before acting on it.
* Tried and reverted: computing the fill-in terms of a pivot once per kind of
  source. Between 5 and 52% of the sources of a pivot share matching and value
  with another source (52% on the stress closure), so their terms coincide.
  With 151 interleaved pairs it was slower on every input: 1.075 (scrambled
  unknot, 25 crossings), 1.031, 1.043, 1.019, and 1.026 on the stress closure,
  all intervals above 1. Building the lists costs more than the sharing saves.
* `recognize` computes the greedy scan order once and hands it to both the Jones
  scan and the Khovanov scan, which used to compute the same order twice.
  Results identical to the previous code on 400 diagrams, evidence records
  included. 151 pairs: 0.943 (0.923..0.964) and 0.945 (0.936..0.955) on two
  scrambled unknots of about 10 ms; on a 40 ms one 1.029 against an A/A of 1.019
  in the same run, i.e. no difference (the change removes about 0.7% there).
  That A/A reading is itself a lesson: the second run of the old code comes last
  in every round and can be biased by a percent or two, so compare a ratio with
  its own A/A, not with 1.
* Scan orders again, now on 81 diagrams (36 scrambled unknots, 45 random
  closures of 20 to 35 crossings) and with work = entries + compositions.
  The greedy rule breaks ties by crossing index. Breaking them towards the most
  recently touched crossing costs 1.09 (unknots) and 1.05 (random) of the
  current total; towards the longest-waiting one 1.52 and 1.57. Not adopted.
  Per diagram the ratios run from 0.01 to 28, better on about as many inputs
  as worse: the rules are incomparable, not ranked. A portfolio does not
  rescue this: the best of the three rules per diagram would need 0.31 of the
  work on the unknots and 0.74 overall, but running them interleaved until the
  first finishes costs three times the winner, 0.94 on the unknots and 2.2
  overall, because 8 of the 81 inputs carry 86% of the work and there the
  rules are within a factor two. Only a predictor would collect that prize.
* **Reidemeister III help for the reduction (`simplify(d, r3=True)`,
  `recognize(use_r3=True)`, `--no-r3`).** The scan is exponential in what the
  reduction leaves, and the reduction stopped wherever a Reidemeister III move
  was needed. A triangular face is a 3-cycle of the face walk through three
  crossings; it can be inverted iff some side is over at both ends; inverting
  it reverses the order in which each of the three strands meets the other two,
  a relinking of at most twelve darts that keeps every crossing's slots and the
  direction of both strands through it, hence its sign. When no I/II move is
  left, each such triangle is inverted on trial, kept if that creates a I/II
  move and undone otherwise (the move is an involution); triangles with no
  small face across a side are skipped, which never changes the result (2120
  diagrams, identical traces). Tested on its own: 150 random moves give valid
  spherical diagrams with the same Alexander polynomial, writhe and Khovanov
  ranks by degree, and a second move restores the dart structure exactly (300
  of 300). On 1500 random closures: never more crossings than I/II alone, no
  I/II move left, every trace replays, Alexander polynomial and Khovanov rank
  unchanged; 26% of the diagrams shrink further, 0.80 of the crossings remain.
  `hard_unknot_8` goes from 6 crossings to 0. Verdicts with and without it
  agree on 900 diagrams.
  *Placement matters.* Run with the first reduction it cost 58% on T(3,61), 20%
  on a random 5-strand closure and 4 to 6% on the Conway knot, inputs a filter
  decides a moment later. It now runs only after every filter has failed,
  just before the scan: no claim of any slowdown on those inputs, `recognize
  hard_unknot_8` 0.48, a scrambled unknot of 27 crossings 0.18.
  *Fewer crossings is not always less work.* One survivor was flagged 1.43
  slower, correctly: R3 help takes it from 22 to 20 crossings and its scan work
  from 2081 to 3277. Over the 54 of 117 survivors where crossings are removed
  (3.4 on average) the scan work is 0.43 of before, cheaper on 44 and dearer on
  10, per-diagram ratios 0.03 to 7.3; over all 117 it is 0.69.
* **Deeper III search, budgeted.** One move of lookahead left 117 unknot
  diagrams (of 40000 random closures) untouched; sequences of two moves, the
  second next to the first, reduce 97 of them to nothing, three moves 109, four
  moves 110, with no violation at any depth (no I/II move left, traces replay,
  Alexander polynomial and unknot rank preserved). A failing search is what
  costs: on T(3,61), full of triangles that lead nowhere, depths 1 to 4 take
  2, 10, 44 and 189 ms. Useful sequences are found early, so the search is
  introspective about its own cost: it deepens only while fewer than
  `r3_budget` trial moves per crossing have been made. Budgets of 5, 15, 40 and
  none give the same 97 / 109 / 110, while a budget of 5 caps the T(3,61) case
  at 10 ms. Defaults: depth 4, budget 10. With them only 15 of 60000 random
  closures are unknots that survive the reduction (largest: 16 crossings).
* **Introspective algorithm selection (the introsort idea), measured.** It
  works where a cheap signal separates the populations and switching is free,
  and three parts of the package now are of that kind: the shape cache chosen
  from the scan order, result sharing enabled by the first plan hit, and the
  budgeted deepening above. For scan *orders* it does not work with the rules
  at hand, in either form. (a) Run the default order under a work budget, on
  overrun restart with another tie-break rule, grow the budget: simulated
  exactly on the saved work of three rules on 81 diagrams, 27 policies, every
  one costs 1.4 to 4.8 times the default. Introsort can switch because heapsort
  has a guarantee and recursion depth signals degeneracy; here no rule has a
  guarantee, expensive is not degenerate (on the 8 inputs with 86% of the work
  all rules are within a factor two), and an abandoned scan is lost. (b) No
  restart: `add_crossing` does not mutate the previous stage, so tied greedy
  candidates can each be tried from the same state and the smallest real
  complex kept. With all trial work counted: 0.41 on the scrambled unknots
  (median per diagram 1.02, dearer on 21 of 36) but 1.44 to 1.52 on random
  closures, 1.40 to 1.47 overall. The size of the complex now does not predict
  the cost of the choice later.
* **Racing orders in parallel** is where that data does promise something: by
  wall clock on separate cores the race costs the winner's time, and the best
  of two rules is 0.75 of the default on the expensive inputs (single inputs
  0.07, 0.24, 0.30). Not in Python, though: a competitor must be a process, and
  starting one costs 30 ms bare, 76 ms with the package imported, 111 ms for a
  complete CLI scan of the trefoil, against scans that mostly finish within
  300 ms. So it was built in the Rust version (`../rust`, `--race N`), where a
  thread costs microseconds. Measured there on 40 random closures with single
  scans of 30 ms to 8 s: racing two orders takes 0.650 of the total time, three
  0.689; per input 0.05 to 1.68 (6.8 s becomes 0.34 s), faster on half and 10
  to 60% slower where the default order was best anyway. That premium is
  hardware contention, not the allocator: separate processes slow each other
  just as much as threads. Details in `../rust/README.md`.
* **A race in Python after all (`race=N`, `race_after=1.0`; `--race`,
  `--race-after`; off by default).** Dismissing it because a process costs 0.1 s
  to start compared that cost with the typical scan; but the race only matters
  on the heavy tail, where Python scans take seconds to minutes. So the default
  order runs alone for `race_after` seconds, and only then are other greedy
  orders (tie rules `oldest`, `recent`; `ordering.best_scan_order(ties=...)`)
  started as `python -m fastunknot _scan` processes with JSON over pipes (no
  `multiprocessing`, which on Windows imports the caller's main module again).
  The scanner polls them where it looks at the clock; the first to finish wins,
  the rest are killed, and rank and ranks by degree are the same whoever wins
  (tested, including a win of a competitor against a handicapped default order,
  and that no worker is left running).
  Measured on 26 random closures with single scans of 0.15 to 3.6 s, three
  interleaved rounds (`results/race_eval_python.json`): total 0.910 of single
  with two orders, 0.925 with three. What that total is made of: a competitor
  won on 2 inputs, 3.22 s to 1.74 s and 3.55 s to 1.56 s, in every round and
  under both settings; on scans of 1 to 3 s that the default order wins the
  race costs 10 to 20%, the hardware contention seen in Rust. The other
  per-input ratios are noise and the data shows it: 18 inputs finish inside the
  head start, where nothing is started and the ratio must be 1, and they read
  0.80 to 1.43. Measured properly (61 interleaved pairs on the 0.25 s stress
  scan) an armed race that starts nothing costs 1.010, interval 0.984..1.041,
  with the A/A control at 1.042: nothing. It is insurance against a bad order on
  long scans; use `race=2`.
* `hard_unknots.py`: the scrambled family turned out weak, since its rewriting
  consists of Reidemeister III moves and the helped reduction undoes all of
  it (120 of 120; 180 of 180 with heavier scrambling). `SURVIVORS` lists unknot
  diagrams of 11 to 16 crossings found by random search that survive I, II, the
  default III search and every filter; they are the honest scan-decided inputs.
* **Start-up: a whole command-line run takes 0.52 of the time** (`python cli_ab.py`,
  41 interleaved pairs of whole processes, `results/cli_ab_log.json`): `recognize
  conway.json` 115.5 to 60.9 ms (interval 0.510..0.541), `hard_unknot_8` 0.523,
  `unknot_braid40` 0.530, `khovanov trefoil` 0.523, and still 0.856 on the
  half-second stress scan. The bare interpreter is 29.5 ms of that, so the
  package's own start-up went from about 86 to about 31 ms; for a command-line
  user that is more than every scanner optimization above, which save well
  under a millisecond on such inputs. Where it went: `import fastunknot` took
  56 ms, 25 of them for `dataclasses` (it loads `inspect`, `re`, `dis`, `ast`,
  `tokenize`) used for five simple records, now written out by hand with the
  same constructors, equality, hashing, immutability and `repr` (and they
  pickle and deep-copy); 9 ms for `subprocess` and `json`, needed only when a
  race starts; 5 ms for `typing`, used only in annotations that are never
  evaluated; the 0.1 reference scanner, needed only by the ablation
  configurations, is imported on demand. Then `argparse`: 55 to 59 ms in Python
  3.14, where it loads `_colorize`, `dataclasses` again and `shutil`
  (`color=False` does not help). The options are now one table that feeds a
  small direct parser for the well-formed common case and, on demand, the real
  `argparse` parser for everything else (help, errors, abbreviated flags,
  `--flag=value`, values that look like flags), so messages and help are
  argparse's own; tests check that the two agree wherever the fast one
  accepts, and that start-up loads none of those modules.
  Two measurement notes. My first two whole-process comparisons showed "no
  difference" and were invalid: `python -m` puts the current directory first on
  `sys.path`, and both arms ran from the working tree, so the working tree was
  compared with itself; `cli_ab.py` runs each arm from its own directory and
  checks which package it imports. And the absolute milliseconds of different
  rows are not comparable: the same command read 61 ms and, ten minutes later,
  100 ms; only the paired ratio within a row is robust.
* Three small things found by profiling `recognize` on the Conway knot by
  cumulative time: the Jones filter's `Planar` paid for shape-cache bookkeeping
  it never uses (9% of the call); `simplify` rebuilt and revalidated the diagram
  even when no move applied (12%; an unreduced diagram now keeps its own edge
  labels, where the rebuild renamed them by first appearance, and `replay` does
  the same for an empty trace); `Diagram.alpha()` was recomputed seven times
  per recognition although the diagram is immutable (now cached with `faces`
  and `traversal`; callers get copies, the caches are not pickled and do not
  affect equality). `ab.py`, strict criterion, against 3a86e0c: `recognize`
  Conway 0.765 (0.733..0.794), T(3,61) 0.759, Conway#Conway#Conway 0.731,
  random 5-strand closure 0.865, hard unknot 0.896, scrambled unknot 0.906; no
  claim on the three scan-dominated survivors. Status, method, reduced size and
  rank identical to the previous code on 700 diagrams.
* The most common input, a reducible closure that the Alexander filter decides:
  `simplify` was half of `recognize` there, and half of that was
  `Diagram.from_pd` validating the rebuilt diagram from scratch. What the moves
  could break is the topology, so `rebuild` now checks that directly on the
  darts (one traversal through every crossing twice; the face walk closing into
  n + 2 faces) and builds the diagram from rows that are normalized by
  construction. Reduced diagrams and traces identical to the previous code on
  1500 diagrams in both modes; of 282 deliberately corrupted dart structures
  273 are rejected and the other 9 also pass the full validation (a random
  reconnection is sometimes a legitimate diagram). Also, the Alexander rows skip
  the polynomial addition when a slot is empty, the usual case. `ab.py`
  (strict): `recognize` random 5-strand closure 0.796 (0.772..0.831), hard
  unknot 0.913; no claim where nothing is reduced.
* Kept but not claimed: the face walk written out with bit operations in
  `move_at` (called 168 times in a typical recognition). Identical reduced
  diagrams and traces on 1500 diagrams; `ab.py` medians 0.98 to 0.99, every
  interval reaching 1.
* `tail` re-tested on the current scanner (41 interleaved pairs per input, 15 on the
  stress closure, ratio to `tail=0`, ranks by degree asserted equal): `tail=1`
  0.94 to 1.01 on eight inputs, the interval excluding 1 on two of them (Conway
  0.947, stress 0.971) and no A/A control behind it; `tail=2` 0.98 to 1.60;
  `tail=3` 1.03 to 3.04. The default stays 0, as after the 0.2 ablation.
* `seconds=` fidelity: the default scanner overshot a 1 s budget by up to
  0.24 s because a crossing was added without checking the clock; with a check
  every 512 objects the overshoot is at most 0.03 s on the same runs.
* Post-0.2 scanner work (commits 24b6111, 2e3fef7, e34c9e8), `perf.py` totals:
  1022 ms (0.2) to 602 ms (`FastScan`) to 412 ms (integer geometry). Those six
  runs predate the control loop; what supports them is that the one case the
  changes did not touch (`jones braid5_36`) stayed within 2.63 to 2.73 ms
  throughout. The later geometry refinements are 7 to 13% on small scans by
  `ab.py` and **not measurable on the large scans**. One idea was measured and
  rejected: queuing only the cheapest pivot candidate per source object cut
  queue traffic but raised compositions on the stress case from 29k to 42k.
* Same-machine comparison with the nine proposals:
  `../synthesis/data/proposals_bench*.json`.
* Pitfall for anyone writing random tests: a braid word of even length on an
  even number of strands induces an even permutation and never closes to a
  knot, so a "draw until one-component" loop with such parameters never ends.

## Layout

`fastunknot/diagram.py` (validation, braids, grids, signs), `simplify.py`
(incremental R1/R2, descending test, 0.1 versions as oracles), `ordering.py`
(heap-based greedy scan order), `factor.py` (visible connected sums),
`filters.py` (modular Alexander and Jones tests), `alexander.py` (exact
polynomial), `geometry.py` (matchings, gluing a crossing), `algebra.py`
(bit-packed cobordism algebra), `scan.py` (entry point `khovanov_rank` and the
generic scanner used by the ablation configurations), `scan_fast.py` (the
default scanner: list storage, interned matchings, bucket-queue min-fill),
`planar.py` (its integer geometry and compiled plans), `scan_reference.py` (the
0.1 scanner, unchanged), `recognize.py` (pipeline), `__main__.py` (CLI).
MIT-0, see the repository root.

The default planar algebra also short-circuits typed identities and scalar
squares over its square-free F2 ring. These identities agree with the original
cobordism evaluator; they do not apply to arbitrary morphisms or matrix blocks.
`benchmark_planar_shortcuts.py` records raw scan and separate scalar-kernel
timings. Ordinary scans showed negligible timing impact because most identities
are already removed by the scanner. Report 12's component contraction is now integrated as an opt-in production
option; the standard engine remains the default.

### Optional component contraction

Both `recognize` and `khovanov_rank` accept `composition="component"` (adaptive)
or `composition="component-dense"` (forced ranked subset convolution).
The CLI flag is `--composition`. This contracts morphisms through the connected
components of their compiled gluing plan without changing any differential.
On a boundary of `w` points the dense operation has `poly(w) * 2^(w/2)` bit cost;
the number of chain objects and operations still has no general quasi-polynomial
bound. Standard min-fill/bit scanning and `race=1` are required; shared backends
are not yet wired to this option.

```bash
python -m fastunknot khovanov examples/conway.json --composition component --check-d2
python -m fastunknot recognize examples/conway.json --composition component-dense
```

Earlier recognition filters still take priority. `composition_max_variables=18`
(CLI `--composition-max-variables`) caps component/output variables on selected
allocations. Recognition returns `UNKNOWN` if this limit is exceeded; the raw
Python rank API raises a resource exception. The CLI reports resource exhaustion
with exit code 3. `composition_stats` exposes actual use of the new method.
The advanced fresh-scanner installer is in `fastunknot.component_algebra`.

`benchmark_component_algebra.py` separates full raw scans from dense and sparse
kernel measurements. Local seven-round data show about 38× for independent dense
ten-variable products, 183× for nearly equal dense products using polarization,
and about 44× slowdown when a sparse ten-variable product is forced through the
dense method. None of the six ordinary scan cases selected an adaptive factored
call. Those results justify the explicit option, not a default switch. The raw
samples and A/A controls are in `results/component_algebra_20261007.json`.


### Optional twist compression

Report 11 is integrated through `--backend twist` or `backend="twist"`.
Existing cheap certificates and filters retain priority. After they fail, a
checked source braid is grouped into maximal equal signed runs and evaluated
using the exact reduced twist macro complex. Its complete uncapped bound is
`poly(n) * 2^O(t log(2+n/t))`, where `n` is the expanded crossing count and `t`
is the number of runs in the supplied word. This is quasi-polynomial for
`t = O(log n)`; there is no general conversion to such a presentation.

```bash
python -m fastunknot recognize examples/hard_unknot_8.json --backend twist
python -m fastunknot khovanov examples/trefoil.json --twist --check-d2
python -m fastunknot.twist examples/trefoil.json --mode estimate --profile
```

The direct Python rank entry point is
`fastunknot.twist_adapter.twist_khovanov_rank(diagram, budget=Budget(...))`,
with `Budget` from `fastunknot.twist`. Advanced signed-run homology and estimates
are available there too. Binary run exponents do not change the expanded-size
complexity convention. The main Diagram input still expects an explicit word.

PD and grid recognition fall back to the standard scanner when no checked
source braid exists. Proper connected-sum factors never inherit the original
source word: cheap factor tests run first, then unresolved factors defer to
one computation on the whole original braid. Such factors carry
`twist_deferred` evidence. The whole-knot rank is recorded only at the top level.
This preserves the restricted run-count bound for source-braid inputs.
The raw twist-rank API rejects missing provenance instead of falling back.

An exact Temperley–Lieb basis count precedes assembly. Recognition exposes
`twist_max_basis` (CLI `--twist-max-basis`, default one million); the raw `Budget`
also controls macro states, matrix bits, XORs, and time. Preflight and assembly
share a deadline. Exhaustion returns `UNKNOWN` in recognition and the CLI;
the production Python adapter raises `ScanLimit` or `MemoryError`. These
limits are separate from the ordinary scanner's object ceiling.

Raw degree output is converted to the original source braid's cube grading,
with `grading_diagram` and `source_crossings` identifying it explicitly. This
remains the original grading after whole-diagram simplification. Macro reduced
degrees are also retained. Assembly and degree-profile estimates report the
peak degree dimension, matrix-bit bound, and a degree-sensitive XOR-bit bound.

`benchmark_twist.py` compares raw homology against the production scanner,
including exact degree equality and A/A controls. The default recognition
pipeline often decides these inputs earlier; raw homology speedups are not
recognition speedups. The theory, restricted-family proof, integration details,
and benchmark limitations are maintained in `../synthesis/twist.tex`.

Local seven-round raw homology gains on two-strand twists are 31.6×, 134.7×,
and 574.4× at 51, 201, and 801 crossings. In a fixed four-strand context, a
single 801-letter block gives a 4.29× gain with peak degree dimension 177.
The alternating no-compression control is about 4.5× slower, and the Morton
four-strand unknot about 15.8× slower. Default recognition already decides the
long examples by the braid obstruction. Full inputs, degree counts, timing
boundaries, and A/A controls are recorded in `results/twist_integration_20261007.json`
and `results/twist_context_scaling_20261007.json`.

### Exact windows and bounded adaptive widening

Report 13's exact moving-window scanner is integrated. A window retains both
adjacent differential degrees and prunes irrelevant objects before allocation.
It can choose the mirror with the smaller proved object bound. The dedicated
command returns partial ranks, never an unknot verdict from a partial rank:

```sh
python -m fastunknot window examples/conway.json --lower 0 --upper 0 --normalized --auto-mirror
python -m fastunknot recognize examples/conway.json --window-radius 4 --window-seconds 0.1
```

Recognition's `--window-radius N` enables radii 0, 1, 2, 4, …, N before the
complete backend. Attempts share a per-factor time budget (default 0.1 seconds)
and object ceiling (`--window-max-objects`, default 20000), bounded by the
outer recognition limits. Widening restarts and reuses the last crossing order.
If less than twice the previous attempt's time remains, it proceeds to the
complete backend. Local resource limits also fall back; global exhaustion is
`UNKNOWN`. Any computed profile differing from the unknot proves knottedness.
Agreement remains inconclusive unless the window covers all raw degrees.

The Python API is `fastunknot.window_scan.khovanov_window(pd, lower, upper)`
or `fastunknot.window_bounds.khovanov_window_auto(diagram, lower, upper)`.
Endpoints and `by_degree` use raw cube degree. Normalized degree subtracts the
number of negative crossings in `Diagram.signs()`, not negative braid letters.
Both functions support `reduction='adaptive'` and the component algebra modes.
`recognize(..., window_radius=4, window_seconds=0.1)` enables the bounded probe.
The API's default `window_radius=None` leaves it disabled.

`benchmark_windows.py --output FILE` reproduces seven paired rounds with A/A
controls. The 36-crossing stress input drops from 17694 to 7692 peak objects;
a 10000-object limit changes `UNKNOWN` to certified `KNOTTED`. Widening on the
hard unknot is slower, so this policy remains optional. Earlier default
certificates already decide all six benchmark fixtures. Measurements are
fallback comparisons; the raw-window arm computes less than full homology.
The integrated suite passes 245 tests. Proofs, conditional query bounds, and
negative results are in [`../synthesis/windows.tex`](../synthesis/windows.tex).

### Interval normalization and graded scalar splitting

Report 14 adds optional exact-rank and capped-decision backends:

```sh
python -m fastunknot khovanov examples/conway.json --barcode
python -m fastunknot khovanov examples/conway.json --fitting
python -m fastunknot recognize examples/conway.json --backend fitting
```

`barcode` decomposes a whole component when it has one matching and one common
square-zero differential coefficient. `fitting` first searches for a bounded,
verified scalar change of basis exposing independent summands, then applies
interval normalization and sharing. By default its scalar blocks also preserve
recovered quantum shifts. Global budget exhaustion is `UNKNOWN`; local search
limits retain unresolved components. The standard backend remains the default.

The exact Python APIs are `barcode_khovanov_rank` in `fastunknot.barcode_scan`
and `fitting_khovanov_rank` in `fastunknot.scalar_split`. Their `_decide`
counterparts return rank capped at three, shortening whole intervals to length
two under the ordinary closure theorem. Decision output has no exact rank or
degree profile. A capped three means at least three, not exactly three. Exact
mode retains full lengths and degree counts. Both support `seconds`,
`max_objects`, supplied `order`, and `check_d_squared`; `fitting` additionally
supports `record_witnesses=True` and configurable local search limits.

These backends require min-fill pivots, bit algebra, no tail contraction, and
no racing. They are separate from `--reduction adaptive` and component kernels.
An exact window probe may fall back to them, but shortened decision models
cannot answer exact window queries. The explicit low-level comparison option
`preserve_grading=False` uses the archive's ungraded scalar search and does not
support the refined homogeneous checkpoint bound.

All 267 production tests pass. `benchmark_continuations.py --output FILE`
records paired timings, full-rank cross-checks, and replayable actual splits.
The five measured knot diagrams showed overhead and no nonsingleton interval
normalizations. A separately labeled graded synthetic component compresses
217 stored objects to seven in exact mode and two in decision mode. The
conditional checkpoint theorem no longer needs a bound on the original
connected component size; it still requires suitable frontier widths and
frequent pure stages. Proofs and limitations are in
[`../synthesis/continuations.tex`](../synthesis/continuations.tex).

### Verified rank-two braid preprocessing

`recognize(..., use_ranktwo=True)` or CLI `recognize FILE --ranktwo` enables
one deterministic AVL pass on a checked source braid, after cheap certificates
and before expensive descent and fallback. It replaces an optimal collection
of disjoint two-index subwords by equal empty or single-letter words. A separate
central-normal-form verifier replays the full transcript before its output is
used. These are context-safe braid equalities, not closed-braid equivalences.

Search and replay share `ranktwo_seconds` / `--ranktwo-seconds` (default 0.1).
A local limit skips the optional stage; a global limit remains `UNKNOWN`.
If the verified word beats the current diagram's crossing count, recognition
restarts with the shorter validated input, compression disabled, and the
remaining global budget. Other options are preserved. Evidence under
`before_ranktwo` and `after_ranktwo` records the distinct reduction branches.
The former includes the original source word and independently replayable
certificate. PD input without checked braid provenance bypasses the stage.

The low-level `fastunknot.ranktwo.compress` and `verify` functions also accept
explicit braid words. Recognition always uses one pass; the low-level default
`max_passes=None` instead iterates to saturation, with a weaker total bound.
The one-pass bound is deterministic `O(n log n)` word-RAM time, not a universal
quasi-polynomial knot-recognition guarantee. Flat rank-two inflations of small
cores do have a proved conditional recognition bound.

`benchmark_ranktwo.py --output FILE` reproduces seven paired end-to-end rounds,
including diagram construction and all existing certificates. Sleeve examples
improve by 3.4–33.8 times locally, while the stress five-braid slows down about
1.8 times. Default behavior is unchanged. The full suite passes 272 tests;
proofs, barriers, and measurements are in
[`../synthesis/ranktwo.tex`](../synthesis/ranktwo.tex).

### Minimal extremal windows and certified size bounds

The new optional strategy cancels the entire crossing extension before upper
truncation, including the temporary degree beyond the guard. This is distinct
from the default support strategy's pre-allocation pruning:

```sh
python -m fastunknot window examples/conway.json --lower 0 --upper 2 --minimal
python -m fastunknot recognize examples/conway.json --window-radius 2 --window-strategy minimal
```

The Python entry point is
`fastunknot.minimal_window.khovanov_minimal_window_auto(diagram, lower, upper)`.
It defaults to choosing the mirror with smaller raw upper depth. CLI mirror
selection requires `--auto-mirror`, as with other window queries. Results
always return original raw degree labels. `trace=True` records retained
matching/degree profiles. Ordinary, residue, and adaptive exhaustive reduction
and component composition are supported.

This strategy verifies a nice disc scan order: connected prefixes and suffixes,
consecutive attachments, no projection loop edges, and final closure. With no
supplied order it first checks the fast greedy order, then attempts a cubic
construction when needed. Failure withdraws the sharper complexity certificate;
the query still computes exact homology. All planning and temporary allocations
are covered by the query's resource limits.

A certified order of girth W gives retained degree-j counts at most binomial(t,j)
before closure, doubled at closure, and a uniform quasi-polynomial query bound
for raw upper depth O(log n) and W=O(log² n). Runtime checks verify these counts.
This bound does not apply to the existing support strategy, and a narrow interval
in the middle is not necessarily a shallow endpoint query. Partial agreement
still cannot certify an unknot. See
[`../synthesis/extremal.tex`](../synthesis/extremal.tex) for the domination proof,
cache accounting, external theorem attribution, and exact padding obstruction.

All 277 tests pass. `benchmark_minimal_windows.py --output FILE` compares exact
identical window queries on common supplied orders. Minimal mode is slower on
all six measured cases; it remains optional despite its stronger conditional
bound. These partial-query ratios are not end-to-end recognition speedups.

## Optional exact Potts Jones filters

`recognize --jones-backend potts-exact` uses integer pairs in
`Z[x]/(x²−(q−2)x+1)`, with six colors by default. The
`potts-exact-factorized` option keeps processed Tait components separate until
an edge joins them. `potts5` supplies a modular five-color comparison; it
misses a proved infinite weaving family even without modular collisions.
The exact six-color filter detects that family. Equality at any chosen
specialization remains inconclusive and continues the complete fallback.
The existing `matching` filter remains the default.

Use `--potts-colors 7` to choose another exact color count (integer ≥5), and
`--jones-max-states` / `--jones-max-transitions` for local work limits.
A state limit counts represented keys, not total memory. Local exhaustion
falls through; the global recognition deadline returns UNKNOWN.
Standalone examples:

```sh
python -m fastunknot jones examples/conway.json --backend potts-exact
python -m fastunknot jones examples/conway.json --backend potts-exact-factorized
python -m fastunknot recognize examples/conway.json --jones-backend potts-exact
python -B check_potts_independent.py /tmp/potts-independent.json
python -B benchmark_potts.py --output results/potts_local.json
```

The standalone Jones command returns an inconclusive result and exits 3 on
resource exhaustion, 2 for invalid options, and 0 on a completed query.
Exact witness pairs use signed hexadecimal strings for large-integer JSON
safety. Raw evaluator APIs retain integer pairs.

The same-color benchmark measured a 23.6× factoring gain on a fixed fragmented
order (4,111→205 peak keys), but factoring slowed all six other kernel cases.
Normal recognition with the single-table exact option was about 1.14–1.15×
faster on Conway and Kinoshita–Terasaka in this small run; earlier certificates
bypassed the new filter in the other five cases. These observations do not
justify an automatic switch or a default change. See the complete theory,
limitations and measurements in [`../synthesis/potts.tex`](../synthesis/potts.tex).

## Adaptive transfer on certified disk frontiers

`--reduction disk-adaptive` adds a full finite radical transfer after sparse
cancellation pauses and the existing cheap residue shortcut declines. It keeps
nonzero maps between adjacent surviving degrees. Geometry is certified from
the actual processed rotation system and checked against live matching types.
A local work guard can decline the attempt; the unchanged partial complex then
resumes ordinary cancellation. Global deadlines still produce UNKNOWN.

This option works with full homology, recognition, either window strategy, and
component coefficient composition, under the existing adaptive scanner
restrictions. Evidence reports actual transfer calls, geometry declines, budget
fallbacks, and transfer work. The local allowance counts cooperative polls,
not elementary bit operations or total memory. It is an experimental policy,
not a competitive scheduling guarantee. `standard` remains the default.

```sh
python -m fastunknot khovanov examples/conway.json --reduction disk-adaptive
python -m fastunknot recognize examples/conway.json --reduction disk-adaptive
python -m fastunknot window examples/conway.json --upper 2 --reduction disk-adaptive
python -B check_disk_geometry.py /tmp/disk-audit
python -B benchmark_disk_transfer.py --output results/disk_local.json
```

Dense synthetic blocks gained up to 4.08× while retaining nonzero survivor maps;
the sparse control avoided transfer altogether. None of the four ordinary
diagram benchmarks made a full-transfer call, so no recognition speedup follows.
The [theory section](../synthesis/disk_transfer.tex) covers certificates, finite
perturbation, rollback, cost accounting, and explicit unknot diagrams whose raw
frontier is Ω(√n) in every order. The latter limit an order-only approach, not
recognition with simplification and structural certificates.

## Exact long-twist profiles and streamed homology

The additive RLE frontend `python -m fastunknot.twist.continuation input.json`
accepts `{"strands": 3, "runs": [[1, 1001], [2, -1], [1, 1], [2, -1]]}`.
It checks the original knot component count and evaluates structural
certificates directly on run counts. `--mode homology --method tail` computes
an exact reduced homological profile using a finite reference at run length
`W+2`, where `W` counts the fixed context crossings. Longer exponents produce
a constant interval plus finite exceptional degrees, without expansion.
The returned degrees are macro degrees; quantum grading is forgotten.

`--method streaming` instead retains two adjacent state layers and feeds
columns directly into elimination. It reduces storage but was slower in all
eight measured full-homology cases. In recognition it may stop when finalized
reduced homology already exceeds one, explicitly reporting an incomplete
homology and a rank lower bound. A partial rank-one result never proves UNKNOT.
`--method macro` retains full assembly. The existing main CLI and production
`backend="twist"` defaults are unchanged.

The ordinary recognizer has a separate opt-in `--braid-profile` flag
(`use_braid_profile=True`) for a checked source word. It specializes the
existing Seifert graph criteria, with the established PD/Artin sign conversion.
The original source remains distinct from any connected-sum factors.

The largest measured tail gain was 58.6× for exact homology; dominant-run knots
were already structurally decidable, so this is not a new recognition family.
The profile option gained 2.30–3.33× on selected fresh prebuilt homogeneous braid
diagrams. See [TWIST_CONTINUATION.md](TWIST_CONTINUATION.md) for schemas,
budgets and examples, and [the theory section](../synthesis/twist_continuation.tex)
for proofs, output-size limits, independent audits and timing scope.


## Checked rational and Montesinos presentations

`Diagram.from_rational(e, tangles)` now builds and validates a Montesinos
numerator closure, retaining checked source provenance. The recognizer uses
an exact arithmetic decision before the general diagram pipeline; disable it
with `use_rational=False` or `--no-rational`. JSON uses
`{"montesinos":{"e":0,"tangles":[[2,3],[-2,-2,-1,-2]]}}`.
The decision preserves each rational summand's denominator and handles
nontrivial determinant-one knots. Arbitrary PDs have no inferred source.

For binary coefficients too large to expand, `montesinos_certificate(e,tangles)`
provides a separate arithmetic-only API. The ordinary constructor and CLI
still build the actual PD, with a default 100,000-crossing expansion ceiling.

`recognize_with_subtangles` in `fastunknot.tangle_obstruction` optionally
searches a small literal-pattern catalogue in an arbitrary validated PD.
Each rejection verifies a four-port disk occurrence and its non-embeddability
in an unknot. No match falls back to the ordinary recognizer. This wrapper
was slower in all five measured cases and remains explicit.

See [RATIONAL.md](RATIONAL.md) for APIs, provenance and certificates,
[rational_research/README.md](rational_research/README.md) for reproducible
checks, and [the theory](../synthesis/rational.tex) for arithmetic bounds,
full-complex barriers and performance scope. These are polynomial procedures
on supplied presentations or fixed local patterns; general quasi-polynomial
recognition remains unproved.


## Quantum-ordered full transfer

`--reduction graded` and `--reduction graded-adaptive` are optional exact
policies for the standard scanner. The first computes the full differential
between scalar survivors using quantum-ordered transfer. The second retains
completed sparse pivots and switches only when the per-stage Schur-update
allowance is exhausted. Unlike a survivor-count shortcut, both retain nonzero
maps between adjacent surviving degrees. They do not require a common-disk
certificate. The standard policy remains the default.

The Python `khovanov_rank` and `recognize` APIs accept the same reduction names.
Bit coefficients, minimum-fill pivots, self-inverse cancellation and one scan
order are required. Component coefficient composition and tail finishing are
supported; homological windows and alternative scanners are rejected before
early recognition certificates. Global resource failure remains `UNKNOWN`
in recognition. The replacement graph is fully prepared before installation,
so transfer failure preserves the current differential.

See [graded_research/README.md](graded_research/README.md) for reproducible
checks and measurements and [the theory](../synthesis/graded_transfer.tex)
for the finite-transfer proof, cost accounting and unresolved multiplicity
bounds. The new full suite has 426 passing tests. The report's remaining proposals are reviewed in
[the symbolic continuation section](../synthesis/symbolic_runs.tex).


The run frontend now transports huge integer values and degree keys using exact
hexadecimal strings, accepts either signed runs or an explicit word, and
supports independent replay of serialized structural certificates. Use
`fastunknot.integer_codec.decode_degree_profile` after a JSON round trip.
The earlier total-rank law at context length plus one is documented and audited;
the full-profile computation keeps its context-length-plus-two reference.
All 431 maintained tests pass. See [TWIST_CONTINUATION.md](TWIST_CONTINUATION.md)
for the extended schema and [the theory](../synthesis/symbolic_runs.tex) for
succinct complexity and the conditional repair-DAG research target.


### Survivor corridors and bidirectional adaptive transfer

`--reduction corridor` preserves full graded transfer while pruning paths
that cannot reach an output survivor and choosing propagation direction per
component. `--reduction corridor-adaptive` first spends the existing sparse
Schur-update allowance and retains completed pivots before switching.
Both are optional; `standard` remains the default. The supported backend,
coefficient, tail and resource contracts match the graded full-transfer modes;
window combinations are rejected. Direct controls also expose sparse scalar
components and Boolean endpoint selection.

The 458-test maintained suite passes. Independent audits check 3,885 transfer
comparisons on 555 prefixes, all eight contraction identities at each prefix,
and entrywise equality of sparse versus packed scalar maps. The constructed
shared-suffix family proves a near-linear complete stage versus quadratic
forward propagation at fixed algebra size; it does not prove a knot-prefix
family or superiority to sparse cancellation. See
[corridor_research/README.md](corridor_research/README.md) for measurements,
commands and limitations, and [the article](../synthesis/corridor_transfer.tex)
for proofs and complete setup accounting.


## Certified cyclic Garside preprocessing

Report 25's exact source-braid compressor is available with `--garside` or
`recognize(diagram, use_garside=True)`. It shares exact Garside prefix states
across cyclic cuts, independently replays the proposed equalities, and restarts
recognition only when the candidate improves the current simplified diagram.
Cheap modular Alexander and structural obstructions run first; Jones follows
the probe. The optional probe has a local time/operation
allowance; exhausting it resumes the established exact pipeline under the
remaining global budget. Original source-branch evidence and PD reductions stay
separate, and backend/reduction options survive the restart.

The default radius is one; `--garside-radius 2` adds two-letter targets.
The default caps are `--garside-seconds 0.1`, `--garside-max-ticks 100000`, and
`--garside-max-targets 100000`. The probe is disabled by default. See
[`garside_research/README.md`](garside_research/README.md) for reproduction,
resource semantics and measurement scope. The theory article derives the
polynomial fixed-radius compressor bound and a conditional small-core theorem;
it does not claim a general sub-exponential unknot algorithm.


## Compressed surface-cover geometry

`fastunknot.surface_cover` maintains report 24's classifier for supplied
binary-encoded dihedral covers of bordered surfaces. `CoverIndex` provides
component and boundary-lift queries, exact signatures for ordered marked fibre
points, and evaluation of rooted equivariant maps. Classification uses at most
three unmarked family records; all arithmetic is polynomial in the input bit
length without expanding sheets. Hexadecimal JSON and cooperative cancellation
are supported. See [`cover_research/README.md`](cover_research/README.md) for
input examples, proofs, audits and separate geometric benchmarks.

This module is not called by knot recognition. Presentation extraction, full
external attachments and hierarchy search bounds remain unproved integration
steps. Even a one-type cyclic annulus cover has `W` inequivalent ordered pairs
of marked points, so efficient marked comparison alone does not bound the
number of possible hierarchy states. The theory is maintained in
[`../synthesis/surface_covers.tex`](../synthesis/surface_covers.tex).

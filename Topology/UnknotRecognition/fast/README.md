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
   Cost is bounded by the number of crossingless matchings of the scan
   boundary (proved, no multiplicity factor). Skipped above 4096 frontier
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
* Step 6: at most n · Catalan(w/2) · poly(w) field operations for scan width w.
* Step 4 with step 8: if the visible factors have n_1, …, n_k crossings, the
  cost is poly(n) + Σ 2^O(n_i). Polynomial when every factor has O(log n)
  crossings; this is a restricted-class statement, not a bound for all diagrams.
* Step 8 in general: 2^O(n). The size of the complex after elimination is
  (number of boundary matchings) × (a multiplicity that grows with the
  homology of the partial tangle); no subexponential bound is known or claimed.

## Test and benchmark status (last observed 18 September 2026)

* `python -m unittest discover -s tests`: 40 tests, OK (about 9 s; one test starts race processes), about 3 s (CPython
  3.14.4, Windows 11). 19 are the 0.1 tests (three expectations updated because
  a filter now decides before Khovanov does), 21 are new and compare every new
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

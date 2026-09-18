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
   mutable dart structure, one revalidation at the end.
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

* `python -m unittest discover -s tests`: 33 tests, OK, about 6 s (CPython
  3.14.4, Windows 11). 19 are the 0.1 tests (three expectations updated because
  a filter now decides before Khovanov does), 14 are new and compare every new
  code path with the 0.1 implementation.
* `results/benchmark_0.1.json` is the 0.1 benchmark, kept as a record; its
  36-crossing 5-strand row is the 600 s timeout that motivated 0.2.
* `results/ablation.json` is the per-idea ablation (see the report). It takes
  about 40 minutes because the LIFO configurations on the stress case run into
  the 300 s cap; shorten the list in `ablation.py` if that matters.
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
(bit-packed cobordism algebra), `scan.py` (scanner), `scan_reference.py` (the
0.1 scanner, unchanged), `recognize.py` (pipeline), `__main__.py` (CLI).
MIT-0, see the repository root.

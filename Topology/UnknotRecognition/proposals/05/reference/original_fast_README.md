# fastunknot: exact unknot recognition with a scanning Khovanov backend

**Status: exact, complete, and exponential in the worst case. The `n^O(log n)`
bound announced in Lackenby's February 2021 talk is NOT achieved here**, for the
reasons documented in the synthesized report (`../synthesis/`): the accelerated
hierarchy operations in the talk's final flowchart have no published
algorithmic specification with cost bounds, and none of the six earlier
archives nor this package supplies one.

What this package does achieve is a recognizer whose exponential part depends
on the *boundary size of a scan through the diagram* rather than on the
crossing number. Diagrams with hundreds of crossings but a thin scan (braid
closures on few strands, the exponential family `sigma_1...sigma_n` of archive
03, long connected sums) are decided in milliseconds where the cube-of-
resolutions implementations of the six archives need `2^n` states.

## Pipeline

1. **Validation.** One component, spherical rotation system. Inputs: PD code,
   braid word, or rectangular (grid) diagram.
2. **Reidemeister I/II reduction** (crossing-decreasing only; polynomial time).
3. **Descending-diagram test** (polynomial; sufficient for `UNKNOT`).
4. **Alexander polynomial** by fraction-free Bareiss elimination over `Z[t]`
   (polynomial; `Delta != 1` certifies `KNOTTED`; strictly stronger than the
   determinant filter used by the archives).
5. **Reduced Khovanov rank over F2** by Bar-Natan scanning: the diagram is
   processed crossing by crossing in a greedy small-boundary order; after each
   crossing, closed circles are delooped and all invertible differential
   entries are cancelled (Gaussian elimination in the dotted cobordism
   category). The final complex has zero differential, so its size is the
   unreduced rank; for a knot the reduced rank is half of it and equals 1
   exactly for the unknot (Kronheimer--Mrowka, with the universal-coefficient
   argument of the archives).

Every verdict is exact. Optional ceilings (`--max-objects`, `--seconds`) turn
an expensive step 5 into `UNKNOWN`, never into a knot verdict.

## Run

Python 3.10+, standard library only. From this directory:

```sh
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/hard_unknot_8.json --no-alexander --check-d2
python -m fastunknot recognize examples/unknot_braid40.json
python -m fastunknot khovanov examples/kinoshita_terasaka.json
python -m fastunknot alexander examples/figure_eight.json
python -m unittest discover -s tests -v
python benchmark.py
```

Exit codes: 0 for either exact verdict, 2 for invalid input, 3 for `UNKNOWN`.

## Input

```json
{"pd": [[1,4,2,5], [3,6,4,1], [5,2,6,3]]}
{"braid": {"strands": 3, "word": [1, -2, 1, -2]}}
{"rows": [[0, 2], [1, 3], [2, 4], [0, 3], [1, 4]]}
```

PD crossings are counterclockwise `[a,b,c,d]` with the under-strand `a-c`.
Grid rows are listed bottom to top; verticals pass over horizontals (the
convention of archive 01). `{"pd": []}` is one crossing-free circle.

## Complexity

* Steps 1--4: polynomial in the crossing number `n`.
* Step 5: the number of objects before elimination at any stage is at most
  twice the number after the previous stage times the delooping factor, so the
  whole computation is bounded by the size of the ordinary cube: `2^O(n)` bit
  operations. This is a proved upper bound.
* Empirically the complex after elimination stays close to the number of
  crossingless matchings of the current boundary times a small multiplicity,
  i.e. roughly `2^O(w)` for scan width `w`. **This dependence is observed, not
  proved.** A proof would need a bound on the multiplicity of each matching in
  the minimal complex of a tangle, which is not known to us.

The scan width of a planar 4-regular graph can be as large as `Theta(n)` (for
example for diagrams whose Tait graph is a grid), so the worst case stays
exponential.

## Verification performed

* 19 unit tests: polynomial arithmetic, known Alexander polynomials, symmetry
  and determinant identities on random braids, Reidemeister moves, the local
  endomorphism ring of the scan, `d^2 = 0` after every crossing on several
  diagrams, independence of the processing order, resource-limit semantics,
  known reduced ranks (trefoil 3, figure-eight 5, T(3,5) 7, Kinoshita--Terasaka
  and Conway 33, two hard unknots 1), an independent dense reduced-cube
  computation on 25 random braids, and the command line.
* Cross-validation against the five cube implementations of the archives on
  120 random braid closures and the Atlas 10- and 11-crossing PD codes
  (see `../synthesis/`).

## Test and benchmark status (last observed 18 September 2026)

* `python -m unittest discover -s tests`: 19 tests, OK, about 2 s (CPython
  3.14.4, Windows 11). Two test expectations were corrected while writing the
  suite (a braid word that closes to a trefoil, not an unknot, and a word that
  closes to a link); no source file changed after the suite went green.
* `python benchmark.py`: completed in about 11 minutes. Every input finished
  within a few seconds except a random 36-letter closure on five strands,
  which hit the 600 s per-input cap (`timed_rank(..., seconds=600)`) and is
  recorded as `timeout` in `results/benchmark.json`. A 31-letter closure on
  six strands took about a second, so the cost is driven by the size of the
  intermediate minimal complexes, not by the strand count. Expect the same
  timeout on rerun; raise the cap or drop that input if 10 minutes matter.
* Pitfall for anyone extending the benchmark or writing new random tests: a
  braid word of even length on an even number of strands induces an even
  permutation and therefore never closes to a knot. A "draw until
  one-component" loop with such parameters never terminates. Two earlier
  experiment runs were lost to exactly this; `benchmark.py` now uses odd
  lengths for 4 and 6 strands.

## Layout

`fastunknot/diagram.py` (validation, braids, grids), `simplify.py`
(Reidemeister I/II, descending test), `alexander.py` (polynomial arithmetic and
the Alexander polynomial), `scan.py` (dotted cobordism category, delooping,
Gaussian elimination, scan orders), `recognize.py` (pipeline),
`__main__.py` (CLI). MIT license.

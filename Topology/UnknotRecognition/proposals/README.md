# proposals

Nine independently produced proposals for accelerating `fast/fastunknot` 0.1,
extracted from the ZIP archives that were delivered on 18 September 2026 (the
ZIPs were deleted after extraction; `ORDER.txt` records which archive became
which directory, in order of modification time). Each archive had one wrapper
directory, which was removed.

Every proposal is a complete, runnable replacement for the 0.1 package with
its own report (LaTeX and PDF), tests, benchmarks, and an unchanged copy of
the 0.1 baseline. **All nine state that the general worst case stays
exponential and that no quasi-polynomial bound is claimed.**

| Dir | Archive | Package root | Tests | Distinctive content |
|---|---|---|---|---|
| `01/` | `unknot_speedup.zip` | `01/fast` | 30 | exhaustive validation on all 2856 three-braid words of length ≤ 6; ablation showing the pivot rule alone is worth 45× on the stress case |
| `02/` | `unknot-accelerated.zip` | `02` | 37 | **incremental O(n log n) Reidemeister I/II simplifier**; no connected-sum factorization |
| `03/` | `unknot_accelerated.zip` | `03` | 34 | **bit-packed morphisms with compiled gluing plans** (fastest raw scanner); factorization |
| `04/` | `Knots-accelerated.zip` | `04/fast` | 48 | evidence replay (`verify`), factored rank as a separate API |
| `05/` | `unknot_accelerated (1).zip` | `05` | 42 | exact scaled-integer bracket as a follow-up to the modular one; keeps LIFO pivots |
| `06/` | `unknot_accelerated_solution.zip` | `06/fast` | 41 | **tail crossings**: no cancellation during the last crossings, linear algebra at the end |
| `07/` | `unknot_acceleration.zip` | `07` | 36 | fill-estimate pivots, Jones witness verification |
| `08/` | `Knots_accelerated_solution.zip` | `08` | 30 | keeps the 0.1 Fox signs separately as `relation_signs()`; `git apply`-able patch |
| `09/` | `unknot_accelerated (2).zip` | `09` | 47 | modular determinant as its own stage, factor-certificate replay |

## The ideas, and who proposed them

| Idea | 01 | 02 | 03 | 04 | 05 | 06 | 07 | 08 | 09 | Adopted in 0.2 |
|---|---|---|---|---|---|---|---|---|---|---|
| Units of End(m) over F2 are involutions (no geometric series) | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | yes |
| Min-fill (Markowitz) pivot choice instead of LIFO | ✓ | ✓ | ✓ | ✓ | – | – | ✓ | ✓ | ✓ | yes |
| Cached composition topology / identity shortcuts | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | yes |
| Bit-packed morphisms, compiled plans | – | – | ✓ | – | (masks) | – | – | – | – | yes |
| O(n log n) greedy order with a heap | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | yes |
| O(n) descending test | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | yes |
| Modular Alexander test before Z[t] (*det* = determinant at t = −1 only; *2 pts* = a second evaluation point, which is what rejects determinant-one knots such as T(3,61) without the 5.8 s symbolic computation) | 2 pts | det | det | – | det | – | – | 2 pts | det | yes, 2 pts |
| Modular Jones/Kauffman bracket by frontier scan | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | yes |
| Visible connected-sum factorization | ✓ | – | ✓ | ✓ | – | ✓ | ✓ | ✓ | ✓ | yes |
| Crossing signs from both incoming ports | ✓ | – | ✓ | ✓ | ✓ | – | ✓ | ✓ | ✓ | yes |
| Incremental R1/R2 simplifier | – | ✓ | – | – | – | – | – | – | – | yes |
| Tail crossings + final linear algebra | – | – | – | – | – | ✓ | – | – | – | optional (`tail=1` gains about 10%, larger tails lose) |
| Exact integer bracket after the modular one | – | – | – | – | ✓ | – | – | – | – | no (equality is inconclusive either way; no measurable effect) |
| Witness replay / verification commands | ✓ | – | ✓ | ✓ | ✓ | – | ✓ | – | ✓ | no (not a speedup) |

Same-machine measurements of all nine against the baseline and against the
integrated version are in `../synthesis/data/proposals_bench*.json`; the
per-idea ablation is in `../fast/results/ablation.json`; both are discussed
in `../synthesis/report.pdf`. All nine proposals and the integrated version
return identical ranks and verdicts on every benchmark input.

## Running a proposal

```sh
cd proposals/03 && python -m unittest discover -s tests
cd proposals/03 && python -m fastunknot recognize examples/conway.json
```

(For `01`, `04` and `06` the package root is the `fast/` subdirectory.)
The proposals' own test suites were not re-run as part of this review; only
their public APIs were exercised by the comparison benchmark.

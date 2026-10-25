# Actual one-policy projection results

All five authorized author commands passed on the unchanged reviewed core.
Both independent checker modes rejected all 46 actual corruptions, and both
pure rebuilds reproduced the entire generated inventory byte for byte. Root's
four fresh independent runs also passed; all four complete JSON receipts and
all four full stdout records matched the author records exactly. Root retains
those eight records separately. No root output is copied into this packet.

| Chart | Variables | Rows | Degree | Terms | Coefficient height | Row height |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Plain | 329 | 216 | 4 | 6226 | 414619 | 324 |
| Centered | 329 | 216 | 4 | 5728 | 128446 | 256 |

The source has 478 integer coordinates/365 rows; the exact Horn image has
479/364. Its actual projection certificate contains 148 monic restorations:
100 affine and 48 quadratic, with 137 gate, nine witness and two
square-difference variables. The actual unconstrained coordinates are 133
(`sqd.10`) and 135 (`mul.333`). The Horn maps overwrite 27 private coordinates
and preserve the other 451 source coordinates. All rules, complete coordinate
and row maps, free values and chart metadata are explicit in the certificates
and `COMPOSED_MAPS.json`; none of these counts was inferred from an old run.

The six product coordinates p2 through p7 are retained; p8 is monically
restored. The three strict-product Legendre auxiliaries remain retained. The
plain chart has 13 shifts. The centered chart has 60 composed nonzero shifts
and 78 recorded improving moves. The original complete guarded-source tuple
is reconstructed by inverse translation, assignment of actual free coordinates,
reverse monic rules and finally the old Horn private overwrites. Native
calibration applies only after that complete reconstruction.

The checker independently collected the whole quadratics/quartics and all
metrics for both new charts and all five complete accepted baseline charts.
`data/COMPARISON.json` contains every baseline byte hash, raw metric schema,
normalized census and both new-chart deltas. Selected centered comparisons are:

| Accepted centered baseline | Variable delta | Row delta | Term delta | Height delta |
| --- | ---: | ---: | ---: | ---: |
| Cap: 359/222/6058 | -30 | -6 | -330 | 0 |
| Grouped cap: 364/227/4574 | -35 | -11 | +1154 | 0 |
| Helper: 433/287/4606 | -104 | -71 | +1122 | 0 |

Thus the grouped and helper alternatives retain fewer terms. These are
comparisons of separately calibrated complete equations, not identities of
their polynomials or private tuples. No global optimality is asserted.

The generated index is SHA256
`659b9154862310640bbe7a107e8a2ab5c33bf83fb834f0d740e0f43cadc00465`.
It closes 26 payload files, plus the index itself. The complete centered
equation and polynomial SHA256 are respectively
`08033ddb02ccd654a03cee01025a2da26c5bb64063a2adda5cccc078a1362e77`
and `ed45a6e439bb7d706ddd630d5475d432fe37aae8e9ca22ca220453d0c389b43e`.
The endpoint calibration pins all prior generated files and the complete
ordinary source calibration. `RESULTS.json` also retains the exact actual
maps, alternative comparisons, receipt hashes and product retention status.

Only the single reviewed default support16 policy and its two integer charts
ran. There was no alternate search, canonical change, Lean execution or new
unbounded theorem claim. The frozen parents remain unchanged.

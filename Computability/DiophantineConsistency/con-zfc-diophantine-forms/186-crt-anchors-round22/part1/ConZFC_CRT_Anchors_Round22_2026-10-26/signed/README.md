# Direct consistency equations with weighted growth indices

New Round22 quartics over unrestricted integers. The equation is the sum of
squares of the literal residual array, equal to zero. Every coefficient of the
collected polynomial is also supplied.

| Endpoint | Variables | Residuals | Degree | Collected monomials | Height |
|---|---:|---:|---:|---:|---:|
| principal215 | 215 | 154 | 4 | 7,081 | 8,880 |
| balanced215 | 215 | 154 | 4 | 7,315 | 4,096 |
| low215 | 215 | 154 | 4 | 16,077 | 2,304 |
| dimension214 | 214 | 153 | 4 | 7,078 | 1,052,028 |

`PROOF.md` gives the uniform growth-index theorem, its noncircular CRT/Pell
composition, and exact integer projection proof. The pinned inherited
ordinary proof closure is under `inherited_anchor/`; it also contains the
independently verified incoming 215/214/213 equations. The new principal
improves Round21's 217 variables and 7,396 terms at unchanged height 8,880.
The endpoints are tradeoffs, not a global optimality claim.

For each endpoint, ZFC proves that absence of integer zeros is equivalent to
Con(ZFC), for the inherited fixed effective proof presentation. Neither side
of this equivalence is asserted separately. No new end-to-end Lean or Rocq
build is claimed, and finite numerical controls are not substitutes for the
unbounded proof.

## Standard-library reproduction

From this directory, without network or nonstandard Python packages:

```sh
python3 -B verify.py
python3 -B -O verify.py --deep
python3 -B build.py --check
python3 -B build.py --output /tmp/conzfc-round22-fresh
python3 -B coordinate_maps.py check
```

The builder freshly reconstructs the inherited anchor from its parent225,
applies the exact semantic source delta, then replays all algebraic maps and
row changes. It compares every generated equation, expansion and metric to
the delivery. The independent checker uses separate polynomial kernels for
the chart and common-radical projections, verifies composed inverse row
operations, and rejects deliberately corrupted certificates. Deep mode also
runs the complete inherited package's verifier.

`coordinate_maps.py project ENDPOINT point.json` maps a point of its chosen
221- or 220-variable source zero set to the final zero set. `lift` performs
the reverse integral map. These do not claim a fixed-point map across different
cofinal horizon choices. `evaluate.py ENDPOINT point.json` evaluates a supplied
tuple; it does not search for a zero or decide consistency.

The sparse format `[coefficient,[indices...]]` is literal; an empty index list
means a constant. Variable indices start at zero. `WHITELIST.json` and
`MANIFEST_SHA256.json` pin the portable deliverable files. Any new receipts
should be saved outside the package so they are not confused with frozen
historical receipts.

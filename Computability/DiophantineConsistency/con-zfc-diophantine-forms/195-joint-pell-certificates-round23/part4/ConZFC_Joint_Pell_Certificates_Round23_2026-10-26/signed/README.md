# Round23: signed affine horizons and a quartic height ladder

Every endpoint is a literal sum of squares of quadratic polynomials in
**unrestricted integers**. Complete collected coefficients are included.

| Endpoint | Variables | Rows | Degree | Terms | Exact height |
|---|---:|---:|---:|---:|---:|
| `dimension209` | 209 | 149 | 4 | 5,278 | 70,368,744,177,664 |
| `principal210` | 210 | 150 | 4 | 5,276 | 16,777,216 |
| `balanced211` | 211 | 151 | 4 | 5,401 | 65,537 |
| `low212` | 212 | 152 | 4 | 18,381 | 5,200 |

`principal210` improves the credited incoming 210-variable quartic's
5,282 terms and height 2^40 at unchanged degree and dimension. `balanced211` also dominates the
incoming balanced214 affine-radix companion (5,699 terms, height 91,679)
in dimension, row count, support and height.
`dimension209` saves a coordinate at a larger height. The other two
are dimension/height/support tradeoffs. In particular **5,200 is larger
than Round22's heights 4,096 and 2,304**; those older endpoints are not
claimed dominated. No global optimum is claimed.

`conservative209/equation.json` is the exact separately pinned m=16,
full-square-frame source required by the reciprocal component. It has
209 variables, 149 rows, degree four, 5,486 terms and height 2^50.
It is retained for that proof boundary, not advertised as a new Pareto point.

## Theorem and attribution

The new source uses a signed affine horizon t=4(2z+1). Its sign is recovered
from the actual retained q^t certificate only after excluding x=0 by the
beta endpoint. A compressed affine-atom frame and a difference of two
orientation errors reduce support. The proof supplies new quantitative
power bounds for that frame; it does not silently reuse squared-atom
hypotheses. Splitting a fixed power-of-two coefficient into monic wires
then lowers coefficient height at the stated variable costs.

`PROOF.md` gives the full new ordinary proof, including cofinal completeness,
all sign stages, numerical margins and explicit zero-set maps.
`MATHEMATICAL_REVIEW.md` is a separate internal mathematical audit, not
external human peer review. The incoming standalone Pell-growth and affine
radix theorem and its complete preserved source/build/proof closure are in
`incoming210/`, credited to `ConZFC_Pell_Growth_210_2026-10-25`.

With its pinned C222/ZF/ZFC calibration, the construction proves within ZFC
that each equation has an integer zero iff a finite ZFC refutation exists.
Negating gives integer unsolvability iff Con(ZFC). This is an equivalence,
not a proof of consistency or inconsistency. Proof codes are internal to
ZFC, not restricted to externally standard integers. No complete new
proof-assistant compilation is claimed.

## Reproduce offline

Python 3.10+ standard library only; no network or root search:

    python3 -B verify.py
    python3 -B -O verify.py
    python3 -B verify.py --deep
    python3 -B -O verify.py --deep
    python3 -B build.py --check
    python3 -B build.py --output /tmp/round23-rebuilt

`--deep` additionally verifies the entire preserved incoming210 package,
including its parent closure, independent source checks, inverse maps,
mutation controls and deterministic rebuilds. The main verifier imports
no producer algebra. It separately reconstructs semantic edits, authenticates
the actual 34-atom frame and all 15 power ports, checks monic pullbacks,
affine projection identities and composed inverse row operations, and
recollects every coefficient using unordered-pair squaring. It rejects
controlled corruptions of each new family. Checks remain active under `-O`.

Each endpoint includes `unsplit_modified_source.json` (semantic source),
`modified_source.json` (monic wires inserted), `certificate.json`,
`equation.json`, `expanded_polynomial.json`, and `metrics.json`.
These distinguish semantic cofinal-source changes from exact coordinate
bijections. `coordinate_maps.py` exposes the integral projection, lift,
wire insertion and forgetting maps; its `check` mode gives bounded sanity
controls in addition to the verifier's exact symbolic identities.

To evaluate a supplied tuple, without searching:

    python3 -B evaluate.py principal210 point.json

Booleans, floats, wrong dimensions and other noninteger inputs are rejected.
`WHITELIST.json` and `MANIFEST_SHA256.json` define the portable inventory.

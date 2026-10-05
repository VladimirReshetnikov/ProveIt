# Validation summary: report111

Validation date: 2 October 2026. Result: **PASS**.

## Reproduced results

- Normal and optimized (`python -O`) checker runs produce byte-identical JSON
- Each complete checker run evaluates **394,716 explicit guards**
- All **17** fixture values for A348351, n=0 through 16, match the independently
  reconstructed quadrant-walk recurrence
- Direct enumeration of vincular-pattern-avoiding permutations through n=7 gives
  1, 1, 2, 6, 20, 72, 274, 1088
- Exact finite algebra verifies the transition matrix, Perron data, stationary
  law, conditional drift, Poisson corrector, martingale, covariance, independent
  spectral Hessian, dual chain, finite killed-kernel duality, and count transfer
- Complete constructions include **1,136** terminal connectors,
  **514** padded injections,
  **52,025** dyadic integer schedules,
  **4,064** exact square-root padding cases, and
  **90,237** exact bridge-time pairs
- Additional annular certificates cover **32** original/dual seeds, **7** large
  exact scale-selection schedules through n=10^300, and **16** variable-time
  first-hit-recoverable concatenations, together with squared-metric step bounds,
  the no-skip inequality, and exact geometric sums
- The angle certificate is X^2+29X+2 with nonsquare discriminant 833=49*17;
  its target root lies in (-2,0), and its other conjugate is below -2

## Deliberate corruption tests

The campaign checks both pristine baselines before any corruption. It then runs
**54 distinct mutations in both modes**, totaling
**108 corrupted runs per campaign**. Running the campaign itself normally and under
`-O` produces byte-identical JSON. Every corruption is rejected at the expected
named mathematical or schema diagnostic; no crash, import failure, or syntax-only
failure is counted as a detection. A syntax-only negative control verifies this.

Covered changes include source-step signs and states; the Perron conjugate;
stationary weights; conditional drift and corrector signs; covariance entries;
angle signs and minimal polynomial; n versus n-minus-one; terminal color and
spatial endpoint; initial states and counts; dual displacement and stationary
ratio; return-cycle displacement; connector length/state; scale and descending
schedule; annular step/time/no-skip/geometric bounds; middle-time off-by-one;
last-hit instead of first-hit recovery; seed direction; schema inventories,
missing fields, duplicate keys/edges, wrong sizes/types, nonfinite values,
noncanonical algebraic triples, and malformed JSON. Five mutations alter the
checker implementation itself and must compile before their mathematical tests.

All subprocesses run from isolated temporary copies with `-I -S -B`, excluding
site packages and user import paths. The original source, fixture, campaign and
README are actually hashed before and after; all remain unchanged.

## Exact source hashes

SHA-256 values are recorded by the campaign before and after its runs:

- `README.md`: `c3d9e2ed11a81b90a81bf0ebe70fc059043b98a7ac52d4ea05c9484a713e7606`
- `mutation_campaign.py`: `e4532abbd14f30f640d5cfa03fbc7f6c7568319704dd356fc54322ec4c7b9049`
- `report111_fixture.json`: `1675a8e9e47cc6ff4cf2f55eb3171a3083ba4c3e00f72210e37cf1d6d90d49f5`
- `verify_report111.py`: `6bd00c20b452544953c412e021c8783204c39f229b8254e2c8762491a99ee6b8`

`CHECKSUMS.sha256` additionally inventories this directory's delivered files,
excluding that checksum file itself. `mutation_results.json` contains every
mutation name and observed diagnostic; `verification_normal.json` contains the
exact matrices, angle data, counts and guard-category totals. Their optimized
counterparts are byte-identical.

## Scope

These checks use integer/Fraction arithmetic and a two-coefficient exact
representation of Q(sqrt(17)); the checker has no `assert` nodes and no float
literals. No numerical arccos test is used. The annular example parameters are
illustrative exact bookkeeping data, not calculated analytic crossing constants.

The validation does **not** machine-certify the source bijection, any statement
for all integers, the FCLT, LLT, Brownian harmonic measure, uniform annular
transfer, bridge tightness, the logarithmic coefficient theorem, G-function
regularity, or the non-D-finiteness deduction. Those depend on the mathematical
proof and cited theorems in the article. It does not establish a multiplicative
coefficient equivalent or its leading constant.

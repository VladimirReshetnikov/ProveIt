# Reproducible finite checks

These files support the general fixed-phase amplitude and reciprocal-window
manuscript. They verify finite statements and record exact counts. They do
**not** prove an asymptotic theorem, provide a convergence rate, or certify a
finite-size approximation. The analytical proof is supplied in the manuscript.

## Run

From this directory, with Python 3.10 or later:

```sh
python verify.py
```

The verifier uses the Python standard library only. It writes `results.json`,
`third_boundary_counts.csv`, and `third_window_counts.csv`. All counts and cap
choices use integer arithmetic; JSON counts and Catalan denominators are
decimal strings to preserve arbitrary precision in downstream readers.
The denominators are the actual Catalan numbers, not reduced denominators.
Only presentation values (probabilities, scaled values, and limit constants)
use ordinary binary floating point; they are not certified intervals.

To run only the small finite checks, use `python verify.py --quick`; that
writes `quick_results.json` and leaves the full regression files unchanged.
The shipped full run used Python 3.12.14. A later Python version may change
the version field or the last floating-point digit without changing any
exact integer data.

## What is checked

1. For `p=2,...,14`, every binary mask of the `p-1` gaps is passed through
   the endpoint channel automaton. Gaps are ordered from the terminal core
   outward. Under the manuscript's one-piece-fits/two-pieces-fail geometry,
   the low mode accepts only the all-empty mask; the high mode accepts
   exactly the `p` initial prefixes. The number of accepted mode/mask
   channels is therefore `p+1`. Given the proved half-mass of each endpoint
   mode and mass `2` of each gap class, exact rational arithmetic checks
   `2^(p-2)(p+1)` and the amplitude factor `(p+1)/2^p`. These finite
   automaton checks do not establish the asymptotic endpoint hypotheses or
   the formula for every integer `p`; those are proved in the manuscript.
2. For every `n=1,...,8`, the Catalan maximum-decomposition generator in the
   credited `model.py` is compared with the set obtained by enumerating
   all `n!` permutations and applying a direct `132` pattern predicate.
   Duplicates and Catalan cardinalities are checked. This is an independent
   enumeration algorithm, although the generator and endpoint DP share the
   same credited module.
3. For every cap `m=0,...,n`, the endpoint DP total and **every** pair of
   first/last deficiency thresholds `u,v=0,...,n-1` are compared with the
   literal permutation counts. There are 44 total-count comparisons and
   1,500 endpoint-state comparisons through `n=8`.
4. Exact endpoint-DP counts are recorded for `n=48,72,96,144,192` at
   `m=n/3`. The scaled presentation value is
   `n^(3/2) * exact_count / Catalan(n)`; its limiting target is
   `B3=5/sqrt(2*pi)`.
5. Four additional indexing regressions use `n=48,96`, `t=-1/8,+1/8`, and
   `m=floor(n/3 + t*n^(3/4))`. Integer fourth-power comparisons compute
   these floors exactly. The limit formula shown beside them is
   `B3+A3*max(t,0)^2`, with `A3=729*sqrt(3)/(4*pi)`. No accuracy claim is
   made at these small sizes; for example, the positive window values
   still differ substantially from their eventual limit.
6. Exact rational algebra checks the normalization of `A3` and `B3`, using
   the analytically proved identity `I4(1/3)=8*sqrt(2)*pi` as an input.
   The verifier does not numerically or symbolically prove that integral
   identity. Neither SciPy nor SymPy is needed.

## Center rows (rounded display only)

| n | m | n^(3/2) p_n(m) |
|---:|---:|---:|
| 48 | 16 | 3.461074206453 |
| 72 | 24 | 3.454887459594 |
| 96 | 32 | 3.419090716254 |
| 144 | 48 | 3.335292832437 |
| 192 | 64 | 3.258783292724 |

The target is approximately `1.994711402007`. These values reproduce the earlier
numerical exploration, with its numerically integrated target replaced by
the exact analytic constant. The considerable finite-size discrepancy is
reported openly: this table is a regression record, not a convergence
certificate or an error estimate.

## Provenance

`model.py` is copied **byte-for-byte**, without modifications, from the
delivered Polynomial Rarity package's `code/model.py`. That program credits
the Mayama–Akita endpoint recurrence and ProveIt's
`code/05-macroscopic-deficits-model.py`, Git blob
`f0248e0d6181200257e2949c1a8fa8f9fecf5617`. The same model was reused in the
half-size crossover package and is recorded in the current report under
both `07-polynomial-rarity-model.py` and `08-half-size-crossover-model.py`.

- Copied model Git blob: `a4fdee376119a24c057623829b76cee71628b369`
- Copied model SHA-256:
  `c693d80529b69762600edc4b4d271155e6aa12c9127bda9a59a839ee143538f7`
- Current report source pin:
  `7421a4ca60fdf125411edf412f825aac54278b37`
- Inspected combined article SHA-256:
  `32edad6e8217abfa2cd79bd004efbbf153b4cce02ddd3dd49b67de3d04afb48e`

The current source includes Part VII. Historical delivery ledgers describe
older pins and should not be read as describing the current source. The
exact-count algorithm is inherited and credited; the new contribution of
this directory is the verification driver and its finite regression data.

The model checksum is validated on every run. The source pin is recorded
for attribution and is not re-fetched by the script. No network access or
repository writes are performed.

## Optional integral algebra check

`python verify_integral.py` uses SymPy to verify the pair-convolution antiderivative, its endpoint evaluation, and the exact derivative calculation producing I4=8*sqrt(2)*pi and the constants A3,B3. It writes `integral_symbolic.json`. The ordinary-integral and differentiation justifications remain in the manuscript; the main standard-library verifier does not require SymPy.

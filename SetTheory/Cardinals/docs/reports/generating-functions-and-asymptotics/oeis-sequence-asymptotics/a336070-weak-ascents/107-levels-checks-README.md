# Report 107: finite exact weighted-level checks

This directory is the report's **sole exact-rational checker suite**. It is
standalone: Python 3 and its standard library are the only dependencies. Nothing
imports report 105, the analytical supplements, a CAS, `mpmath`, or a network
resource at verification time.

## Run

From any working directory, run the verifier by its path:

```sh
python3 checks/verify_exact.py
python3 -O checks/verify_exact.py
python3 checks/run_checks.py
```

The first two commands check the committed `fixtures.json` and compare the
computed result with `expected_summary.json`. They return 0 on success and a
nonzero exit code with a JSON diagnostic on failure. The final command runs both
modes, the full corruption campaign in both modes, and untouched baselines again.
It writes `corruption_results.json` and the stdout/stderr files in `logs/`.
`standalone_replay.json` records a successful fresh-directory replay using only
`verify_exact.py`, `fixtures.json`, and `expected_summary.json`, in both modes.
It also records byte-identical fixture regeneration.

Paths in the commands above assume the report directory is the working directory;
the scripts themselves locate their data relative to their own file location.

`verify_exact.py` is self-contained. Its guards use explicit conditional checks
and exceptions; there are no assertion statements. Thus Python optimization does
not disable a correctness gate. Duplicate JSON keys, floating JSON numbers,
missing cases, noncanonical rational strings, wrong types, and extra or missing
keys are rejected. Fixed case inventories cannot silently shrink.

## Exact arithmetic and the symbolic parameter

Choose rational `0 < r < 1`, an integer `M >= 1`, and rational `w > 0`. Put

```text
q = -M log r, symbolically
v = r^(-M)
f_l = r^l
lambda = (v-1)/(1-r)
p_d = (1-r)r^d/(1-r^M)
```

No numerical logarithm or exponential is evaluated. Every frozen-kernel
calculation is rational. The corrector equations are divided by the common
nonzero factor `q`; the fixture stores `b_scaled=b/q`, `c_scaled=c/q` and
`h_scaled=h/q`, not a floating approximation to those values. The corrector
includes the polynomial seam value `h_scaled[M]`, which is not an additional
Markov state. A separately checked stable rational expression is

```text
h_l/q = Abar x(1-x) + Jbar x,   x=l/M
Abar = M(r^(-1)-1)/(2(1-r^M))
Jbar = r^M/(1-r^M) - r/(M(1-r))
```

For `r=1`, the fixture explicitly records `q=0`. The actual quantities
`b=c=h=Z=0` are checked without division. Separately, the candidate continuous
normalized limits are

```text
(b_l/q)_0 = [M(M-1)-l(l-1)]/(2M^2)
(c/q)_0   = (M^2-1)/(3M^2)
(h_l/q)_0 = l(1-l)/(2M^2)
```

Those rational candidates are checked against the endpoint finite sums and
Poisson equations. The finite checker does not prove their analytic convergence
as `q` tends to zero; the removable-limit argument belongs to the article.
In particular, `h/q` at the endpoint is never confused with the actual `h=0`.

## Committed inventory and independent checks

- `M = 1, 2, 3, 5, 8, 16`
- `r = 1/5, 1/2, 2/3, 9/10, 99/100, 1`
- `w = 1/10, 1/2, 1, 3/2, 7`
- 36 frozen cases: 30 positive-`q` and 6 endpoint cases
- 180 weighted cases: 72 below one, 36 at one, and 72 above one

The verifier checks direct unweighted and weighted matrix-vector actions, Doob
entries, strict positivity, every row sum, and every stationary column sum.
For `w<1`, it verifies that `delta_w<0` while the actual entries of `P_w` remain
strictly positive. The expression

```text
P_w = (1-delta_w) P + delta_w I
```

is checked **as an algebraic identity only**, never sampled as a probabilistic
mixture. The 10,770 signed-mixture entry checks include both sides of `w=1`.

Direct finite sums independently check `b/q`, `c/q`, the unweighted Poisson
equation, the weighted operator equation, and

```text
E_(P_w)[a J/M + (h_J-h_l)/q] = c/q + delta_w(l/M-c/q).
```

The analogous interpolated identity is checked at `zeta=0,1/3,1`. There are 1,050
weighted eigen rows, 1,050 weighted Poisson operator rows, 3,150 interpolated
first-moment checks, 720 increment-moment checks, and 1,050 weighted tracker-drift
checks. Deterministic tracker increments are computed directly from the before
and after states and compared with the circular-increment formula.

Level-polynomial coefficients `H_n(w)` are checked through `n=16`. Their fixture
generator uses outgoing `(K,L,E)` transitions; the verifier uses incoming-state
polynomial transitions with a separate equality shift. Independently, all
inversion sequences are filtered from the defining prefix inequalities through
`n=8`. Direct rational-weight state transitions check 80 polynomial evaluations,
and 160 exact finite change-of-weight identities are checked. These last checks
use rational `s=exp(t)`; they assert no limiting MGF statement.

For the zero-level endpoint, an independent incoming prefix/suffix recurrence
checks ordinary Fishburn and primitive-ascent counts through `n=50`. Both
run-length transforms are checked through 50, including all 1,275 signed summands
and the exact upper index `n-1`. The constant coefficients of all 17 stored level
polynomials (including the empty object at `n=0`) agree with the primitive counts.
The verifier includes separately pinned initial values for both count sequences.

`build_fixtures.py` regenerates fixtures using closed-form rational expressions
and outgoing state recurrences. It is not called by the verifier. Regeneration
is deterministic and does not overwrite the expected summary. Shared
mathematical inputs do not make these tests a formal proof: the independence
claimed here is that the specified fixture and verification calculations use
different finite formulations, not that they constitute a second analytical
proof of the theorem.

## Corruption campaign

`run_checks.py` tests 31 independent corruptions, each made from an untouched
baseline:

- 20 data corruptions targeting eigenvalue, eigenvector, kernel probability,
  normalized `b/c/h`, weighted denominator, signed coefficient, positive and
  negative kernel entries, weighted first moment, increment moment, tracker
  drift, endpoint data, a transition coefficient, both zero-level count
  sequences, and an inverse-transform sign
- 7 verifier-equation corruptions independently dropping the equality weight,
  changing the signed-mixture coefficient, reversing the Poisson sign, changing
  the tracker sign, deleting the endpoint `-1`, omitting the level-exponent shift,
  and using `binom(n,j)` instead of `binom(n-1,j)`
- 4 schema/encoding corruptions: a missing case, duplicate key, floating JSON
  number, and unreduced rational string

All **62 corrupted runs exit nonzero**, both normally and under `-O`. Each must
fail at its expected phase and specific diagnostic; an unrelated crash or the
final fixture hash check is not accepted as mutation detection. Mathematical
fixtures are checked by equations before the expected-summary hash is compared.
The four untouched baseline runs all pass. Exact changed paths/values or source
replacements and observed failures are recorded in `corruption_results.json`;
the campaign is reproducible from its source without storing 31 redundant copies
of the fixture.

## What is and is not established

The suite checks exact finite algebra, finite recurrences, endpoint indexing,
and regression-detection behavior. There are **no floating mathematical checks**
and no tolerance-based claim of exactness.

It does **not** establish the weighted counting asymptotic, its compact-uniform
remainder, derivative estimates, moving-state bounds, the calibration integral,
transcendental inequalities such as `t <= (1+q)/M`, a large-deviation principle,
convergence of moments, the primitive/all asymptotic ratio, or the exact-atom
limit. Those are analytical arguments in the article. It also proves no
Poisson approximation, CLT, local limit theorem, variance asymptotic, or
uniformity for weights tending to zero with `n`.

## Alignment with the article

The complete mathematical definitions and proofs are in `report107.tex` and
`report107.pdf`:

- Section 2: positive state recurrence and the level polynomials
- Sections 3.2 and 4: frozen matrices, signed algebraic identity, quadratic
  corrector, and interpolated weighted first moment
- Section 6.2: circular increment and tracked-state drift
- Section 7: the exact finite change of weight
- Section 8: primitive identification and the two run-length transforms

This suite is standalone. It imports no earlier report, external analytical note,
CAS, network resource, or previously computed mathematical output.

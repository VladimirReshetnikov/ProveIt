# Report108: standalone exact finite checks

This directory is self-contained and uses Python 3's standard library only. It
requires no network, installed packages, previous report directory, or other
source tree. No uploads or external state changes are performed.

## Commands

From this directory:

    python3 verify_exact.py
    python3 -O verify_exact.py
    python3 run_checks.py
    python3 replay_standalone.py

The first two commands check all mathematical fixtures and compare the complete
result with `expected_summary.json`. The campaign runs ordinary and optimized
baselines, then deliberately damages independent temporary copies of fixture
data and equations. Every mutation must fail at its specified mathematical or
schema guard, before the generic final fixture-hash comparison. It then repeats
the untouched baselines. The full campaign also reruns the preserved weighted
report107 corruption campaign. `replay_standalone.py` copies only the enumerated
runtime files into a new isolated directory, reruns both verifiers and both
corruption campaigns, and records the outcome in `standalone_replay.json`.
All temporary directories are created within this directory and removed after
use. All correctness gates use explicit exceptions, never Python `assert`.
`python -O` therefore preserves them.

`--skip-weak` is a development-only option on `run_checks.py`, not the complete
reproduction command. `build_fixtures.py` and `weak_build_fixtures.py` are fixture
producers, not validators. They are never called by either verifier or campaign.
Expected summaries are committed baseline files; neither verification nor a
corruption campaign regenerates them after a failed validation.

## What “exact” means

All mathematical calculations in the verifiers use integers and
`fractions.Fraction`. There are no floating-point calculations, transcendental
function evaluations, numerical tolerances, or numerical calibration claims.
File hashes, subprocess status, and Python optimization flags are operational
metadata rather than mathematical evidence.

For frozen weak and shifted rows, rational r lies in (0,1] and exp(q)=r^(-M).
For r<1, q=-M log(r) is a symbolic real parameter. The stored corrector and
first moments are H/q, b/q, c/q; q is divided out before the exact rational
identities are checked. No claim that q itself is rational is made.

At r=1, the stored normalized quantities are their continuous limits. Actual
H,b,c are separately set to zero. The unweighted and shifted kernels are then
uniform, lambda=M, and the weighted kernel has lambda_w=M+w-1. Actual zero
correctors are never confused with their generally nonzero normalized limits.

For capped rows, s=exp(-p) in (0,1) and v=exp(q)>=1 are rational. The finite
sum and its geometric upper bound are rational even though p and q generally
are not. Cap-crossing fixtures use a rational t in (0,1) and integer exponents
q_old=-L log(t), q_new=-N log(t), p=-P log(t), chosen so every relevant
next-state slope is an integral power of t. Their inequalities are exact. They
do not test the analytic calibration estimate |Delta q|<=2/i.

## Coverage and independent constructions

1. Preserved weighted checks: M in {1,2,3,5,8,16}, r in
   {1/5,1/2,2/3,9/10,99/100,1}, and w in {1/10,1/2,1,3/2,7}.
   The 36 frozen cases and 180 weighted cases include weights below one.
   They check weak eigenvectors, geometric rows, the signed algebraic weighted
   representation, scaled Poisson identities, four increment moments, trackers,
   weighted equality-count polynomials through n=16, exhaustive inversion words
   through n=8, and ordinary/primitive run-length transforms through n=50.
   The negative signed coefficient for w<1 is not treated as a probability.

2. Shifted rows: d in {1,2,3,5,9,17}, giving 216 cases, 1,260 rows,
   and 12,924 individual transitions. There are 102 cases with d>M.
   Direct matrix sums verify lambda*r^(-min(d-1,l)); each stored probability
   must equal both the normalized matrix entry and
   P_weak(max(l-d+1,0),j). No state-independent shifted Perron eigenvalue is
   asserted. The scaled shifted Poisson expectation equals
   c/q + H(l')/q - H(l)/q. The tracker contains the essential +min(d-1,l)/M
   term. Uniform q=0 rows and actual zero correctors are checked separately.

3. Capped rows: 432 (M,d,s,v) cases, 2,520 finite row sums/bounds,
   and 12,600 positive-weight domination checks. The checked bound is
   [s^(-M)+v*s^(-(d-1))]/(1-s), including clipped l'=0 rows.
   The fixture producer uses the geometric closed form; the verifier sums each
   matrix row independently. This is the finite content of the capped-row
   argument, not its comparison with the asymptotic normalization n*mu/e.

4. Cap transitions: 30 parameter cases, 200 pointwise slope-drop transitions,
   2,280 full potential-transition factorizations and 600 full successor row
   bounds. Cases cover staying capped, a crossing due only to time change,
   a crossing due only to M increasing, both changes, and a q_new=0 endpoint.
   Equality is uncapped. Exact rational monotonicity also checks that an
   uncapped state cannot later become capped when q decreases and M increases.
   The full factorization includes the favorable exp((q_new-q_old)K) term.

5. Prefix entropy: d in {1,2,3,5,9}, k=1,...,8, giving 40 cases and
   231,165 inversion words in total. Every word is transformed using the
   one-based formula y_i=x_i+(d-1)i. We check its alphabet, exact threshold
   equivalence, nondecreasing runs, injective marked multiplicity encoding,
   and explicit decoding. Definition-only admissibility filters give legal
   histograms, cross-checked against the independent recurrence.
   The 180 exact bounds are
   N_(k,r) <= inversion_words_(k,r) <= binom(dk(r+1)+k-1,k).
   A separate convolution over all nonnegative block lengths verifies the
   stars-and-bars coefficient, including empty blocks. No exponential/e-based
   bound or uniform prefix estimate is inferred from these finite tests.

6. Counts: d in {0,1,2,3,4,5,6,9,17}, n=0,...,16. Fixture generation uses
   outgoing (K,L) transitions. The verifier uses an independent incoming
   recurrence with explicit non-ascent and ascent arrival ranges. d=0 is
   checked separately against ordinary Fishburn counts and direct inversion
   enumeration through n=8; d=1 matches the weighted polynomial at w=1.
   The large-d factorial endpoint is checked when d>=n-1.

## Schemas, failures, and mutation evidence

Fixture JSON has a fixed schema and complete ordered inventory. Objects reject
missing and extra keys. Lists have fixed lengths. Integer fields reject bools
and floats, rational strings must be canonical, duplicate JSON keys are
rejected, and JSON floats/non-finite constants are disallowed. All mathematical
mutations are tested independently, using fresh copies of the valid baseline.

The completed campaign contains 41 new independent mutations and 31 preserved
weighted mutations: 72 total, with all 144 ordinary/optimized corrupted runs
rejected at their named guards and all eight untouched baselines passing.

`corruption_results.json` records each edit, the exact expected guard, and both
ordinary and optimized subprocess results. `weak_corruption_results.json`
records the preserved weighted campaign. Individual stdout/stderr transcripts
are in `logs/` and `weak_logs/`. A rejected corruption establishes only that
specific regression detector; it is not a general software-security or formal
verification claim. The final expected-summary comparison catches unanticipated
changes only after all mathematical and inventory checks have executed.

## Files and provenance

- `verify_exact.py`, `fixtures.json`, `expected_summary.json`: report108 verifier,
  exact fixtures, and frozen baseline summary
- `build_fixtures.py`: independent report108 fixture producer
- `run_checks.py`: report108 extension plus preserved weighted mutation campaign
- `replay_standalone.py`, `standalone_replay.json`: isolated-copy reproduction
- `weak_verify_exact.py`, `weak_build_fixtures.py`, `weak_fixtures.json`,
  `weak_expected_summary.json`, `weak_run_checks.py`: copied report107 exact
  package. Only local filenames and temporary/log/output destinations were
  adapted; its mathematical checks and fixtures are preserved. The original
  report107 package was not changed

The exact shifted identities are the row normalization, Poisson expectation,
and tracker in the fixed-d lower proof. The new finite capped-row and marked
prefix checks correspond to Sections 5 and 7 of the sharpened fixed-d argument
and Sections 5 and 6 of the sharpened weak argument.

## Boundary of the evidence

These checks do not prove the compact-uniform/fixed-d O(log n) remainders,
fixed-ratio local analytic estimates, derivative bounds, calibrated cutoff,
negative-margin absorption, concentration or inverse-moment estimates,
Riemann-sum bounds, cancellation of asymptotic normalization terms, or the
bounded-error inverse. Those require the report's analytic proofs and audits.
The finite counts are benchmarks, not asymptotic fitting. No amplitude, power
of n, relative-error equivalent, or exact integer inverse recovery is certified.

# Report168 exact companion

Python 3.10 or later; Python standard library only. No network, package
installation, SymPy, or external CAS is required. Run the commands below from
the extracted package root. They also work from another directory when the
script path is absolute. The scripts write JSON or test results to stdout;
redirect output explicitly to save a new receipt.

## Fast exact reproduction

```sh
python -B companion/exact_matrix.py verify
python -B companion/exact_matrix.py sequence --max-n 16
python -B companion/test_exact_matrix.py
python -B -O companion/test_exact_matrix.py
```

`verify` defaults to these independent checks:

- Integer ODE recurrence through n=200, checking every division by 16
- Compressed zero/one-column-degree DP through n=40
- Rationally truncated generating function through n=30, with all 30 ODE
  residuals zero when evaluated on that independently generated series
- Entire labeled-column-degree tuple DP through n=8
- Literal enumeration of all 2^(n*n) binary matrices through n=4
- All 17 OEIS values for n=0,...,16, from strict local fixtures

The regression tests go further: rational GF through n=50, compressed DP at
n=60 in addition to all n<=40, and the integer ODE through n=2000. No giant
sequence fixture is needed. The tests include injected recurrence corruption,
nonintegral division, corrupted exact values, duplicate/missing/malformed JSON
fields, bad source records, API booleans, negative/overbound/noninteger CLI
arguments, and subprocess runs with `-S` (no site packages). They use unittest
checks and explicit exceptions, never removable Python `assert` statements.

The API functions in `exact_matrix.py` return Python integers. CLI sequence
values are decimal strings in JSON, preserving all digits for consumers that
would otherwise round large JSON numbers. Large integer formatting does not
change Python's global integer-string conversion limit.

## Explicit resource bounds

| Method or option | Allowed range |
|---|---:|
| `ode_sequence(max_n)` / `sequence --max-n` | 0..2000 |
| `compressed_dp(n)` / `verify --dp-max-n` | 0..60 |
| `gf_sequence(max_n)` / `verify --gf-max-n` | 0..50 |
| `tuple_dp(n)` / `verify --tuple-max-n` | 0..8 |
| `literal_bitmask(n)` / `verify --literal-max-n` | 0..4 |
| `verify --max-n` | 16..2000 |
| `symbolic_coefficients.py --order` | 0..8 |

Every verifier cross-check bound must also be at most its `--max-n`. For
example, a deliberately reduced verification run is:

```sh
python -B companion/exact_matrix.py verify --max-n 16 --dp-max-n 16 --gf-max-n 16
```

The literal cap is strict: n=5 would enumerate over 33 million bitmasks and is
rejected rather than silently starting. Booleans and non-built-in integers are
rejected by the counting and order APIs; CLI values must be canonical unsigned
decimal integers. Invalid arguments and missing/malformed fixtures produce a
nonzero exit status. Fixture reading is capped before parsing (16 KiB JSON,
32 KiB source-term records).

## Opt-in symbolic reproduction

```sh
python -B companion/symbolic_coefficients.py --order 4
python -B companion/test_symbolic_coefficients.py
python -B -O companion/test_symbolic_coefficients.py
```

The finite Gaussian-moment calculator computes the local Bessel amplitude H
and all corrections through the requested order. It uses exact arithmetic in
Q(sqrt(2)): with w=i*u/2^(1/4), the saddle coordinate is
s=sqrt(2)*epsilon^2*(1+epsilon*w). Gaussian moments are
E[w^(2m)]=(-1)^m*(2m)!/(4^m*m!*sqrt(2)^m), and odd moments vanish.
Negative phase powers, the constant Gaussian phase, and parity are explicitly
checked. The mathematical coefficient rule is available at every fixed
order; the executable's `--order 8` cap is a resource policy, not a theorem
restriction.

An independently constructed shifted discrete-ODE ansatz derives the same
relative corrections and prints its determining linear equations. It does
not call the Gaussian-moment generator or take its coefficients as input.
The regression suite checks both routes through every order 0..8, the four
displayed corrections, H through s^4, and the first two logarithmic constants.
Full symbolic computation is opt-in rather than an import-time side effect.
It is small here and needs no optional dependencies.

Both derivations normalize c_0=1. The ODE recurrence alone does not determine
the absolute leading asymptotic constant or prove existence of the expansion.
The report's analytic proof supplies the normalization, all-arcs control,
fixed-order remainders, and inverse statements. Finite exact checks do not
replace that proof and establish no historical-priority claim.

## Local fixtures and receipts

- `data/oeis_fixtures.json`: exactly 17 decimal-string values, indices 0..16
- `data/oeis_term_records.txt`: only the frozen source's three factual term
  records, used for a second fixture-format check
- `data/fixture_provenance.json`: public source URL, original retrieval time,
  Git blob SHA, full-source SHA-256, and delivered-fixture hashes
- `data/exact_verification.json`: saved default exact verification result
- `data/symbolic_order4.json`: saved exact order-four moment/ODE result
- `data/tests_{exact,symbolic}_{normal,optimized}.txt`: saved normal and `-O`
  regression-test receipts

The complete third-party OEIS entry is not part of the deliverable. No command
requires that file or an internet connection.

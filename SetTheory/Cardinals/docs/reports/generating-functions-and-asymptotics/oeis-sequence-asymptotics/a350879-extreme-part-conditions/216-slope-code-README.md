# Report216 reproducibility code

This is the small public implementation accompanying Report216. It excludes the
empty partition and accepts fixed integers `k >= 2`, `b >= 0`. `E` means
`largest part = k * number of parts + b`; `T` means the corresponding `>=` tail.
There is no `k = 1` or growing-parameter claim.

## Run

From the Report216 directory, using Python 3.10 or later:

```sh
python code/reproduce.py --exact --check
python -O code/reproduce.py --exact --check
```

These standard-library-only commands recompute the finite checks and compare the
fresh output bytes with the saved receipts. They do not modify the package.
Explicit exception guards remain active under `-O`; the two commands generate
identical semantic receipts. Python 3.12.14 was used for the distributed receipts.
A different Python version changes recorded provenance, so use `--out` to inspect
fresh results rather than expecting the provenance bytes to match.

To regenerate into an independent directory:

```sh
python code/reproduce.py --exact --out /tmp/report216-fresh
```

This writes `results/` and, when requested, `tables/` beneath that directory.
It creates missing directories and replaces the named output files if present.
Without `--check`, `--out`, or `--write`, the program runs and reports its checks
without writing files. `--write` explicitly replaces the author baselines in
`code/results/` and the report's `tables/` directory. `--exact` is the default.

### Optional numerical diagnostics

The exact core has no third-party dependency. To run the optional diagnostics,
install mpmath in your preferred environment; the recorded version is 1.3.0:

```sh
python -m pip install mpmath==1.3.0
python code/reproduce.py --diagnostics --check
# Or regenerate everything outside the package:
python code/reproduce.py --exact --diagnostics --out /tmp/report216-all
```

Diagnostics use 80 decimal digits and recompute the integer sieve counts through
`n = 10001` from scratch. They never trust a saved coefficient or count receipt.
Both kinds are tested for `(k,b) = (2,0), (2,1), (3,0), (2,3)`, at `n = 1000`
and `10000`, using orders `0,1,2,3,6`. The optional run is slower than the exact
small-range checks. Floating-point outputs and TeX tables are byte-stable on the
same recorded toolchain; no timestamps or machine-specific paths are included.

**These are NON-CERTIFIED numerical diagnostics.** Eighty-digit arithmetic is
not an interval proof or an explicit bound for an asymptotic remainder.
Higher truncation order need not improve a fixed finite input. Inverse errors
are real-index errors, not a claim that taking an unqualified ceiling determines
the integer threshold.

## Contents and API

- `extremes.py`: exact finite q-sieve, exponential-product radial coefficients,
  factorial transfer polynomials, and triangular inverse reversion
- `independent.py`: separate finite algorithms used to cross-check those results
- `reproduce.py`: tests, strict receipt validators, optional diagnostics and tables
- `results/exact_checks.json`: compact test coverage, explicit negative controls,
  interpreter version, and SHA-256 hashes of the three source files
- `results/coefficients.json`: exact forward and inverse coefficients through
  order six for the eight representative cases
- `results/selected_counts.json`: a few exact counts per representative case;
  the full large integer arrays are intentionally not included
- `results/diagnostics.json`: selected exact large counts, exact finite threshold
  checks and optional non-certified numerical errors
- `../tables/forward_table.tex`, `../tables/inverse_table.tex`: complete generated
  LaTeX table environments, with captions and labels, requiring no extra package

When importing from the `code` directory:

```python
from extremes import exact_counts, forward_coefficients, inverse_coefficients
counts = exact_counts("E", 2, 0, 160)       # integers X(0), ..., X(160)
c = forward_coefficients("E", 2, 0, 6)     # c[0], ..., c[6]
u = inverse_coefficients("E", 2, 0, 6)     # u[0]=0, ..., u[6]
print(c[1].record())                      # {'-1': '-3', '0': '-31/2'}
```

Every coefficient is a `Laurent` polynomial in the formal variable `A`.
Its finite `.terms` tuple contains `(integer exponent, Fraction coefficient)`
pairs; `.record()` uses canonical exponent strings and reduced rational strings.
The empty dictionary is the zero polynomial. Forward `c_m` multiply `t^m` in
`X(n)/(k! B(n) t^s)`, where `s=k` for E and `s=k-1` for T. Inverse `u_j` multiply
`w0^(-j)` in `delta`; the real index is `1/24 + (w0 + delta)^2/(4A)`.
The generators accept any nonnegative fixed order, subject to computation time;
order six is the depth of the saved checks, not a built-in limit. Inputs reject
booleans, non-integral parameters, negative order, and inexact Laurent constants.
No floating-point value enters the exact core.

The receipt schema is `Report216-v1`. Count values are canonical nonnegative
integer strings, avoiding downstream JSON floating-point conversion. Individual
coefficient/count records can be checked by
`reproduce.validate_coefficient_case` and `reproduce.validate_selected_counts`;
they verify shape and canonical encoding, then regenerate the mathematics.
The normal CLI reads saved files only for exact byte comparison in `--check`.
Unexpected or modified content therefore cannot silently become trusted input.
Source hashes provide provenance, not a cryptographic authenticity guarantee.

## What is independently checked

For all 98 combinations of kind, `k=2..8`, and `b=0..6`, every integer count
through `n=160` is compared against an exact-length, bounded-largest-part
coin-change DP. The DP does not use the q-sieve or Euler's pentagonal recurrence.
Its increments classify the largest part exactly, and its totals are separately
checked against unrestricted coin change. The core uses the pentagonal recurrence
and successive finite differences. In all, there are 15,778 count comparisons.
The identity `E(k,b)=T(k,b)-T(k,b+1)` is also checked wherever both tails occur
in that grid.

For 72 parameter/kind cases (`k=2..10`, `b in {0,1,2,7}`), the radial coefficients
are independently recovered as moments of the fully expanded finite
q-polynomial. Transfer polynomials are obtained by differentiation recurrence
and compared with the factorial formula through `ell=20`. Forward coefficients
and first-order closed forms are checked through relative order six. Inverse
coefficients are checked through order six by substituting into a separately
implemented formal residual: the generator uses finite log powers, while the
check computes the logarithm by integrating `F'/F` and composes with Horner's
rule. The displayed formulas for `u1`, `u2` and `u3` are also checked. There are 690
checks of the sufficient Cauchy truncation depth.

The 23 explicit negative controls include invalid parameters, non-finite or
inexact coefficient inputs, a deliberately false guard, malformed rational
receipts, changed forward/inverse coefficients and poisoned exact counts.
These are functional defensive checks, not a security audit or sandbox.

The distinct verification algorithms were adapted from the research-stage
independent audit and the main exploratory implementation. They are genuinely
different finite computations, but the public package does **not** claim
clean-room authorship, organizational independence, or an independent proof of
the analytic theorem. The finite tests do not prove the asymptotic remainder.

For each numerical target `y=X(n)`, the diagnostics scan every exact count from
zero through `n` and verify that the first index reaching `y` is `n`, as well as
checking the adjacent counts. This proves those particular integer threshold
statements by finite computation. It does not certify an inverse error bound.

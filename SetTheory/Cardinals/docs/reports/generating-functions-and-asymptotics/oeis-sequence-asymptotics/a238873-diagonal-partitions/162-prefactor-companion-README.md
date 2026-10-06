# Bounded companion for Report162

Python 3.10+; standard library only. The companion performs no network requests and has no file-writing API. Every CLI command prints one deterministic JSON document to stdout. Shell redirection is the caller's responsibility; use a new directory and `set -C` to avoid overwrites. Runtime checks use explicit exceptions, not removable assertions.

## Commands

```sh
python3 -B companion/prefactor.py counts [--max-n 400]
python3 -B companion/prefactor.py series [--max-n 80]
python3 -B companion/prefactor.py verify
python3 -B companion/prefactor.py illustrations
python3 -B companion/prefactor.py threshold --value 1000000 [--max-n 400]
```

Brackets denote optional arguments and are not typed. Integers use canonical nonnegative ASCII decimal notation: no signs, whitespace, leading zeroes except `0`, exponents or Unicode digits. Values are parsed only after a length and notation check. Unknown commands and arguments fail. Domain errors produce a nonzero exit status.

- `counts`: 0 <= max_n <= 400; exact integer multiplicity DP, including A(0)=1. JSON count values are decimal strings
- `series`: 0 <= max_n <= 100; independent reciprocal-H formal q-series inversion, including the staircase weight shift. Default 80
- `verify`: fixed work only; exact counts through 400; independent series match through 80; direct enumeration through 28; largest-part injection; rational tilt over multiplicity vectors of lengths 0 through 6 and entries 0 through 3; Airy differential-polynomial identities; inverse cross coefficient
- `illustrations`: fixed work only; approximate constants and normalized finite log residuals at n=25,50,100,200,400, from actual exact counts. It uses rounded Airy reference inputs and ordinary floating point, with no root certification or numerical fitting
- `threshold`: 1 <= value <= 10^200 and 0 <= max_n <= 400. Search the exact counts for the first crossing. Output status is `reached` or `unreached`; no asymptotic estimate is substituted. Value 1 has threshold 0, with no previous count

## Python interfaces

Import `prefactor.py` from this directory. The supported computational API is:

- `counts(max_n=400) -> list[int]`
- `q_series(max_n=80) -> list[int]`
- `enumerate_checks(max_n=28) -> dict`, with 0 <= max_n <= 32
- `airy_algebra() -> dict`, fixed rational polynomial check
- `tilt_checks() -> dict`, fixed exact finite vectors and q=2/3,3/4
- `verify() -> dict`, fixed bounded verification suite
- `threshold(value, max_n=400) -> dict`
- `illustrations() -> dict`, fixed noncertified approximate illustrations
- `main(argv=None)`, CLI entry point

All supported integer APIs require `type(value) is int`: bool, float, Fraction, str and None fail rather than coerce. Their bounds match the CLI. Other functions are internal implementation helpers, not supported computational APIs. All execution is bounded by these entry points; no arbitrary precision, vector length, workload or source-file option is exposed.

## Counting invariant

After processing size v, dp[k][w] counts admissible multiplicity vectors using parts at most v, of length k and weight w. Initial state dp[0][0]=1. Adding one copy of v uses dp[k][w] += dp[k-1][w-v] in increasing w, allowing unbounded repetitions. Restrict k <= v to enforce the new cumulative barrier, and k <= floor((sqrt(8N+1)-1)/2) by the triangular weight bound. Exact Python integers cannot overflow. Complexity is O(N^2 sqrt(N)) arithmetic operations and O(N sqrt(N)) cells, with N <= 400. Integer bit lengths are bounded indirectly by this fixed N and the ordinary partition count.

The independent formal series expands (-1)^j q^(j^2)/(q;q)_j and forms c_k = -sum(h_j c_(k-j)). It then shifts the coefficient of c_k by k(k-1)/2. It does not call the primary DP. The conservative operation bound is O(N^3) with N <= 100. Direct enumeration recursively produces ordinary increasing partitions; its separate cap of 32 controls its exponential growth.

## Exact and approximate claims

`counts`, `series`, `enumerate_checks`, `airy_algebra`, `tilt_checks`, `verify`, and `threshold` use exact integer/Fraction computations. Their finite checks do not prove an asymptotic theorem or validate Li's analytic uniform remainder. The convention prefix is a small literal regression fixture, also reproduced independently by the two exact routes.

The Airy decimal inputs in `illustrations` are rounded reference evaluations to 54 decimal places obtained with mpmath at 60 working decimal digits during independent algebra checks. They are not certified enclosures and are converted to floats before use. Output is formatted to 12 significant digits; that formatting is not an accuracy certificate. Exact computations do not use these constants. Illustrations may differ in last digits across math-library platforms.

Run tests normally and under optimization:

```sh
python3 -B -m unittest discover -s companion -p 'test_prefactor.py' -v
python3 -O -B -m unittest discover -s companion -p 'test_prefactor.py' -v
```

The companion is a reproducible finite check, not a security sandbox or proof assistant. It does not estimate a certified finite crossover, fit the amplitude, solve an asymptotic inverse by rounding, or infer a pointwise correction from radial data.

# Report 165: bounded exact companion

This self-contained companion checks finite coefficient identities and fixed-order
algebra for odious/evil restricted partitions. It uses **Python 3.10 or later,
standard library only**. Running it needs no network, symbolic algebra package,
third-party numerical package, shell helper, or input report directory.

The analytic proofs are in the report. Neither a finite coefficient table nor an
asymptotic-fit illustration proves the analytic theorem. This companion supplies
**no interval enclosure, effective asymptotic error constant, certified onset of
eventual monotonicity, or automatic rounding of asymptotic inverse formulas**.

## Contents

- `companion.py`: implementation and bounded command-line entry point
- `test_companion.py`: 16 tests, run in normal and optimized Python modes
- `oeis_prefixes.json`: four frozen numerical prefixes and source metadata,
  extracted from the official OEIS records verified on 3 October 2026
- `reference_run/`: checked output of the fixed suite
- `test-results-normal.txt`, `test-results-optimized.txt`: recorded test output
- `verification.json`: deterministic summary of checks and reference-output hashes

No external PDF or complete research article is included. The prefix fixture
contains numerical facts, record revisions, official record links, and hashes of
the frozen input records, rather than copies of the complete OEIS records.

## Reproduce

From this directory:

```sh
python3 -B -m unittest -v test_companion
python3 -B -O -m unittest -v test_companion
python3 -B companion.py --output-parent "$PWD" --output-name my_run
```

Use the physical absolute path of an existing, trusted directory as
`--output-parent`. It must be owned by the current user and not group- or
world-writable. No component may be a symlink. If `$PWD` is a logical symlink
path, use the physical path from `pwd -P` instead. Choose a new output name for
each run; the program deliberately refuses to reuse `reference_run` or any other
existing destination. The output writer requires POSIX `O_NOFOLLOW`,
`O_DIRECTORY`, directory-relative file operations and `fsync`; it fails closed
where these are unavailable.

A complete run creates four files:

1. `exact_results.json`
2. `numerical_illustrations.json`
3. `SHA256SUMS`, covering the two JSON data files
4. `COMPLETE.json`, written last after the data files have been flushed

JSON has sorted keys, ASCII encoding, two-space indentation and a final newline.
Exact results have no timestamps, paths, random values, runtime details, or
floating-point numbers. Counts and targets are decimal strings; rational values
are canonical `numerator/denominator` strings. Exact JSON is byte-deterministic
for these fixed inputs. Numerical output is repeatable on the tested Python and
math-library platform; no promise of last-digit cross-platform equality is made.

## Fixed scope and strict input contract

- Coefficient degrees: `0 <= n <= 512`
- Signs: exactly `-1` (odious) or `+1` (evil)
- Caps: unrestricted (`None`) or `1, 2, 3, 5`
- Bessel orders: `0` through `6`, inclusive; order 6 means seven coefficients
- Bessel beta values: `Fraction(-1,4)`, `Fraction(0)`, `Fraction(3,4)`
- Integer threshold targets: `0 <= y <= 10^24`
- Formal inverse order: fixed at `6`

The command line exposes no workload, order, precision, tolerance or arbitrary
expression setting. The small importable functions permit only the declared
bounded arguments. All integer parameters require exact Python `int`; booleans,
float values such as `512.0`, integer subclasses, numeric strings, and fractions
are rejected. Beta requires exact `Fraction` with one of the three listed values.
No implicit coercion or rounding enters an exact check.

### Independently structured coefficient methods

`product_counts` selects parts with `int.bit_count` and multiplies a sparse
geometric part factor into a *fresh* coefficient array for every part. The capped
factor is `1+q^k+...+q^(mk)`. Only positive parts are considered, so zero is never
an evil part. The empty partition gives the coefficient `p(0)=1`.

`euler_counts` separately constructs signs from the binary recursion
`epsilon(2j)=epsilon(j)`, `epsilon(2j+1)=-epsilon(j)`. For each integer it enumerates
divisor pairs to build `s(j)=sum_{d|j, allowed} d`. Its logarithmic-derivative
coefficients are

```text
b(j) = s(j)                                  unrestricted
b(j) = s(j) - (m+1) s(j/(m+1))               capped, if (m+1)|j
b(j) = s(j)                                  capped, otherwise
n p(n) = sum_{j=1}^n b(j) p(n-j).
```

Every division is checked for zero remainder and every result for nonnegativity.
The two independently structured methods agree for all 513 indices of all ten
families. Four official prefixes match completely: A067590 (54 terms), A067591
(63), A116492 (69), A116491 (74).

### Exact ordinary thresholds

`exact_threshold(sigma, cap, target)` scans all indices beginning at zero and
returns

```text
T(y) = min{n >= 0 : p(n) >= y}
```

if it finds a hit by 512. This is a **global first minimum**, not a first minimum
on an assumed monotone tail: all smaller nonnegative indices were checked, and
larger indices cannot alter a first minimum. A hit is valid even where the evil
sequence decreases. In particular, targets zero and one have threshold zero.

If no hit is found, the function raises `ThresholdNotFound`; the JSON records
`not_found_through_bound` and `global_threshold: unresolved`. This does not mean
the threshold is infinite and does not offer a guessed larger threshold. The
reference output includes the unresolved target `10^24` for every family.

### Rational Bessel coefficient algebra

Let

```text
r_j(beta) = (-1)^j product_{r=1}^j [4(beta+1)^2-(2r-1)^2] / (j! 16^j)
B_j(beta,a) = r_j(beta) a^(-j/2).
```

The irrational scale remains symbolic. Three calculations agree exactly through
`j=6` at each of the three beta values used by the report:

1. Direct product formula
2. Recurrence derived by substituting `I_nu(x)=e^x x^(-1/2) H(x)` in the modified
   Bessel differential equation, with `nu^2=(beta+1)^2`
3. Direct rational Gaussian saddle expansion at `a=1`, through degree 12 in
   `q=sqrt(t)`, integrating monomials with exact Gaussian moments

The six odd powers `q, q^3, ..., q^11` vanish exactly. This checks the three
relevant rational beta values; it is not an identity checker for arbitrary beta.

### Exact fixed-order inverse reversion

Define `p=beta/2+3/4`, `z=sqrt(a(x+lambda))`, and let `z0` be the large positive
solution of the leading equation

```text
2z0 - 2p log(z0) + log(K a^p) = log(y).
```

The program works formally in `Q[u]/(u^7)`, with `u=1/z0`, and finds rational
`d_1,...,d_6` such that `z=z0+delta`, `delta=sum d_j u^j`. It cancels the residual

```text
2 delta - 2p log(1+u delta)
  + log(sum_{j=0}^6 r_j [u/(1+u delta)]^j)
```

through `u^6`. A separate multiplicative composition check, using the exponential
and generalized binomial series without evaluating that logarithmic residual,
also gives the identity through `u^6`.

The JSON additionally gives `c_0,...,c_5` for

```text
x = z0^2/a - lambda + (sum_{j=0}^5 c_j z0^(-j))/a + higher terms.
```

Only these six coefficients are claimed: computing `c_6` would need `d_7`, which
is outside the declared order. Since `c_0=-r_1`, the constant corrections are
exactly `1/48 + 15/(16 pi^2)` for unrestricted odious,
`1/48 + 135/(16 pi^2)` for unrestricted evil, and
`-m/48 + 3/(16 a_m)` for a fixed cap. The exact parameter records specify
`a/pi^2`, beta and lambda as rational numbers.

This is coefficient algebra, not a numerical evaluation of a Lambert W branch,
not a proof of a particular numerical inverse enclosure, and not permission to
replace a rounding-aware enclosure by the ceiling of a truncated expansion.

## Numerical illustrations are separate

Only `numerical_illustrations.json` uses floating-point arithmetic. It compares
one-term and seven-term asymptotic truncations to the exact counts at
`n=64,128,256,512`, and lists capped odious/evil ratio residuals. The audit's
decimal approximation of `d=D'(0)` is converted deliberately to Python binary64;
it is not independently recomputed or interval-certified here. Powers, logs and
exponentials used in these examples have ordinary floating-point roundoff.

Displayed floating results are explicitly rounded to **13 significant decimal
digits**. Those displayed digits are not a claim of 13 correct digits. Each ratio
residual is also supplied as an exact rational `(p_odious-(m+1)p_evil)/p_evil`.
The files explicitly label interval, onset and error-bound certification false.
Higher-order finite truncations need not be better at a particular small index.
No numerical threshold is calculated from an asymptotic truncation.

## Output safety and failure behavior

The selected existing parent is opened one path component at a time with
`O_NOFOLLOW|O_DIRECTORY`, and its ownership and mode are checked. The new child
directory is created with `mkdir` relative to the pinned parent descriptor, so
any pre-existing file, directory, or dangling symlink causes refusal. Child files
are fixed names opened with `O_CREAT|O_EXCL|O_NOFOLLOW` under the pinned child
descriptor. New directories use mode 0700 and new files 0600.

There is no overwrite option, recursive parent creation, symlink resolution,
network fetch, or cleanup that could delete an existing object. On failure, an
incomplete private output directory may remain; it is not silently reused.
`COMPLETE.json` is the completion marker. These controls assume the chosen parent
and the executing user account are trusted; they are not an isolation boundary
against a hostile process running as that same user or against root.

Tests cover repeated writes, existing files and directories, dangling destination
symlinks, symlink parents and ancestors, malformed names, writable parents,
missing parents, and absence of a completion marker after injected failure.
All mathematical guards use explicit exceptions rather than Python `assert`, so
`python -O` does not disable them. Deliberately corrupted coefficient and inverse
checks are tested in both execution modes.

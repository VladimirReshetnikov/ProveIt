# Report160 bounded companion

Python 3.10 or later, standard library only. The companion performs exact
finite checks and produces separately labeled numerical illustrations. It has
no Airy-function dependency, no unbounded search, and no file-writing API.
It makes no network requests. Commands print deterministic JSON to standard output.

From the report directory:

```sh
python -B companion/airy_shape.py counts
python -B companion/airy_shape.py verify
python -B companion/airy_shape.py illustrations
python -B companion/airy_shape.py shape
python -B companion/airy_shape.py threshold --value 1000000 --max-n 200
python -B -m unittest discover -s companion -p 'test_airy_shape.py' -v
python -B -O -m unittest discover -s companion -p 'test_airy_shape.py' -v
```

The module can also be imported from its own directory as `airy_shape`.
All runtime guards and mathematical checks use explicit exceptions, never
Python `assert`. Integer APIs reject `bool`, floats, strings, and out-of-range
integers. Floating-point APIs accept only finite, domain-bounded actual
`int`/`float` values and reject `bool`. Probability inputs must be actual
`fractions.Fraction` objects, with denominator at most 100.

## Commands and bounds

- `counts --max-n N` computes the exact A238873 coefficients from zero through
  `N`, with `0 <= N <= 400`. The empty list contributes one at zero. The class
  consists of weakly increasing positive parts with `lambda_i >= i`
- `verify --max-n N --enumerate-to E` checks all implemented finite identities,
  with `0 <= E <= min(N,32)`. Defaults are `N=400`, `E=28`. Its source comparison
  uses 61 attributed OEIS terms when `N>=60`. Direct enumeration is independent
  of the counting recurrence and also checks counts resolved by length
- `illustrations` gives source-supplied Airy constants, an independently
  summed positive-series area identity, exact finite counts and rational mean
  lengths at `n=25,50,100,200,400`, the displayed two-term logarithmic expression,
  bounded reference-product-law means, and continuous threshold expressions
- `shape --points P` supplies coordinates for the density `m`, cumulative curve
  `g`, and row curve `f`, with `3 <= P <= 1001` and default `P=121`. The junction
  is inserted explicitly, so the default has 122 coordinates per curve. The
  row grid stops at `0.99 * 2 log(2)`, below its divergent endpoint
- `threshold --value V --max-n N` finds the exact first `n>=0` with `A(n)>=V`
  inside the bounded range. `1 <= V <= 10^200`; the threshold of one is zero.
  An unreached threshold is reported as unreached; no extrapolation or
  rounding of an asymptotic expression is performed

The default verification run takes about one second on the build machine;
the complete test suite takes a few seconds. The source reader is bounded to
32 KiB, rejects nonregular files and symlink leaves, and validates attribution,
numeric types, duplicate keys, lengths, and magnitudes. It reads only data, not
source programs. Its optional Python-level path argument is a testing aid,
not a file-access security boundary. No input file path is exposed by the CLI.

## Exact counting recurrence

Let `d_j(k,w)` count admissible lists of weight `w`, length `k`, and largest
part at most `j`. For `k<=j`, removing one largest part `j` gives

```text
d_j(k,w) = d_(j-1)(k,w) + d_j(k-1,w-j).
```

The second term preserves every earlier cumulative restriction, and the new
last restriction is exactly `k<=j`. Entries with negative weight or length
are zero; the empty-list entry is one. Ascending length updates implement
this recurrence in place. The bound `k(k+1)/2<=w` caps the length. The program
uses `O(N^2 sqrt(N))` time and `O(N sqrt(N))` memory. The separate recursive
enumerator does not use this recurrence, and ordinary partition numbers are
computed by a second, unrestricted coin-change recurrence.

## What the finite checks cover

The `verify` command checks:

1. Indexed/cumulative barrier equivalence on every ordinary partition through
   the enumeration bound, and the exact length-resolved counts
2. The largest-part monotonicity injection, including the empty partition,
   image uniqueness, and the inverse
3. The exact generalized-inverse relation `lambda_k<=j` if and only if
   `C_j>=k`, including `j=0`
4. The left-endpoint prefix area and weight identity
   `W_P=M(M+1)/2+area-M*H_M`, on arbitrary multiplicity vectors, including
   paths that leave the nonnegative half-line
5. The exact prefix factor `4^M`, the probability normalization, and terminal
   factor `(2q^M)^(-H_M)`, with `q=exp(-t)` represented by a rational
6. Finite full-product pointwise identities, including cutoffs zero and the
   full vector length, and exact finite-tail coefficient retilting ratios
7. Rational cutoff signs, including the exact equality case `q=1/2`, and
   the upper-cutoff bound `0<W<=1` on admissible sample prefixes
8. Geometric martingale normalization and exact finite-horizon survival
   probabilities. Every discarded transition is already killed, so no
   geometric support truncation is presented as an exact computation

The default coverage counts are recorded in `../data/finite_checks.json`.
These checks validate finite definitions, identities, and inequalities.
They do not certify an Airy asymptotic, local limit theorem, infinite-time
survival bound, limit shape, concentration theorem, or effective finite onset.

## Approximate constants and shape

The source-supplied input is `zeta = 2.3381074105`, the positive magnitude
of the first Ai zero in [NIST DLMF Table 9.9.1](https://dlmf.nist.gov/9.9.T1),
which supplies ten decimal places. The code does not find or certify an Ai
zero. It uses the exact symbolic definitions in the report with this decimal
only for illustrations. Other displayed constants are ordinary binary
floating-point calculations, rendered as twelve-significant-digit strings.
That output precision is not a claim of twelve significant digits of accuracy.

The area check independently sums 80 terms of `Li_2(1/2)`. The reported
positive-series tail bound is analytic for the omitted terms; it does not
include floating-point rounding error and is not an interval enclosure.
Approximate identity tests likewise test implementation consistency rather
than mathematical validity or numerical certification.

The product-law expected lengths are not expectations under the uniform
fixed-size law. The latter's finite means are separately computed exactly
from the length-resolved counts. Small-`n` discrepancies from the two-term
expression do not supply an error constant or an asymptotic onset. The
continuous threshold expression is not an asserted integer first crossing.

The shape coordinates describe analytic limiting curves, with no sampled
partitions, confidence bands, endpoint fluctuation law, or claim that half
of the discrete rows have exact contacts `lambda_i=i`.

## Packaged data and reproduction

`../data/oeis_prefix.json` is the only input. Its 61 numerical terms and source
attribution were transcribed unchanged from Report158's frozen numerical
extract, and its `source_snapshot_sha256` refers to that original source
snapshot, not to this JSON file. The excerpt is data only. Reports158 and159
are immutable references and are neither imported nor modified by this code.

The four deterministic generated outputs are:

| Command | Packaged output |
|---|---|
| `counts` | `data/counts.json` |
| `verify` | `data/finite_checks.json` |
| `illustrations` | `data/illustrations.json` |
| `shape` | `data/shape_coordinates.json` |

To compare regenerated data without overwriting the release, create a new
directory and use shell no-clobber mode. From the report directory:

```sh
mkdir reproduction
set -C
python -B companion/airy_shape.py counts > reproduction/counts.json
python -B companion/airy_shape.py verify > reproduction/finite_checks.json
python -B companion/airy_shape.py illustrations > reproduction/illustrations.json
python -B companion/airy_shape.py shape > reproduction/shape_coordinates.json
cmp data/counts.json reproduction/counts.json
cmp data/finite_checks.json reproduction/finite_checks.json
cmp data/illustrations.json reproduction/illustrations.json
cmp data/shape_coordinates.json reproduction/shape_coordinates.json
```

The JSON contains no clock readings, random seeds, platform paths, or timing
fields. Exact outputs are platform-independent within the supported Python
range. Approximate decimal outputs are reproducible on the same Python/math
platform; a different platform's math library can affect last digits.
Tests compare those floating-point snapshots on the build platform. Test logs
are execution receipts and include a variable elapsed-time line; they are
not among the deterministic JSON outputs.

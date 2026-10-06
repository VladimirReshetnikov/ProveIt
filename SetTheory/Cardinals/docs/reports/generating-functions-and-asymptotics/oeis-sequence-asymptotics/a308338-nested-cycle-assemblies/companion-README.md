# Report 167: bounded exact companion

This companion checks the finite nested-cycle model

- `P(z) = product_{m>=1} (1+z^m/m)`
- `F(z,u) = exp(u(P(z)-1))`
- `B_n = n! [z^n] P(z)` (A007838)
- `T(n,k) = n! [z^n u^k] F(z,u)` (A392471)
- `a_n = sum_k T(n,k)` (A308338)

A component is a nonempty set of labeled cycles with distinct lengths. Its
lengths specify a unique decreasing nesting order. The components themselves
form an unordered set. The empty extension is `T(0,0)=a_0=B_0=1`.

## Run

Python 3.9 or later is sufficient for the exact computations and tests. They
need no third-party package, installation, source download, or network access.
Run from this directory, or use an absolute path to the script.

```sh
# Full dependency-free bounded verification, using all published fixtures.
python -B verify.py
python -B -O verify.py

# Complete exact arrays, including the triangle through n=100.
python -B verify.py --include-data

# Smaller scope; secondary bounds default to min(n, their maximum).
python -B verify.py --n 12
python -B verify.py --n 0
python -B verify.py --n 100 --power-n 20 --literal-n 6

# Regression tests, including deliberately false identities and bad inputs.
python -B test_exact_nested.py
python -B -O test_exact_nested.py

# Optional exact symbolic checks, only if SymPy is already installed.
python -B symbolic_checks.py
python -B -O symbolic_checks.py
```

The optional symbolic checks use SymPy; the captured results use **1.14.0**.
It is not needed by the default verifier or regression suite. Missing SymPy makes only
the optional script return exit status 2 and a clear JSON message.

Successful commands emit one deterministic JSON object to stdout and do not
write result files. Redirect stdout to a location of your choice if desired.
`verify.py` reads only the packaged `../data/published_fixtures.json`; generated
results are never used as reference input. No program retrieves external
sources. CLI scripts disable bytecode writes before importing local modules;
`-B` also does this for API imports. No computation is performed on import.

CLI status is 0 for success/help, 1 for a failed mathematical check, and 2 for
invalid input or a missing optional dependency. `argparse` supplies ordinary
text help and syntax-error messages; completed verification and validation
failures emit JSON. Bounds and mathematical checks use ordinary conditionals,
so optimization (`python -O`) does not remove them.

## Deliberate finite bounds

| Computation | Allowed maximum |
| --- | ---: |
| Integer component, nested counts, and full Bell triangle | `n=100` |
| Independent rational EGF component and nested counts | `n=100` |
| Independent complete rational-power triangle | `n=30` |
| Literal permutations and admissible cycle groupings | `n=7` |

The secondary bounds must also be at most `n`. Public APIs reject booleans,
nonintegers, negative sizes, and values above the relevant limit. The limits
keep this a bounded reproducibility check; no improved complexity claim is
made. The integer triangle includes column zero and has 5,151 entries through
`n=100`; its nonempty part has 5,050 entries.

## Independent computational paths

1. **Integer cycle product.** Start with `B[0]=1`. For each cycle length `m`,
   update descending sizes by
   `B[n] += binomial(n,m)*(m-1)!*B[n-m]`. Descending updates permit length `m`
   once, and `(m-1)!` is the number of cyclic orders on its chosen labels.
2. **Integer Bell recurrence.** Choose the component containing the least
   label:
   `T(n,k)=sum_{m=1}^n binomial(n-1,m-1)*B[m]*T(n-m,k-1)`.
   A separately implemented scalar least-label recurrence checks every row
   sum. Empty objects and the zero component-count column are explicit.
3. **Rational logarithmic-derivative EGF recurrence.** Compute
   `nu[r]=sum_{d|r} (-1)^(r/d-1)/d^(r/d-1)` without the cycle-product updates.
   With `p[0]=1`, set `n*p[n]=sum_m nu[m]*p[n-m]`. Then `f[0]=1` and
   `n*f[n]=sum_m m*p[m]*f[n-m]`. Scaling by `n!` must produce integers, checked
   explicitly, and gives independent component and total counts through 100.
4. **Rational powers.** Explicit truncated convolutions form every `(P-1)^k`.
   The coefficient `n![z^n](P-1)^k/k!` is tested for integrality and compared
   with the complete Bell triangle through 30. This does not use the Bell
   recurrence or its row sums.
5. **Literal construction.** Enumerate every permutation through size 7,
   extract its labeled cycles, and recursively partition those cycles into
   unordered groups with no repeated length in a group. Each group is one
   component. Canonical creation order of groups avoids ordering factors.
   This path uses neither EGF nor Bell recurrence.
6. **Published numeric fixtures.** Compare all 23 displayed A007838 terms,
   22 displayed A308338 terms, and 55 displayed A392471 entries when `n=100`.
   Small runs state explicitly how many available terms were checked.
7. **Structural checks.** Verify exact nonnegative integrality, complete row
   sizes, `T(n,1)=B_n`, `T(n,n)=1`, `T(n,n-1)=binomial(n,2)`, positive interiors,
   and strict increase `a_n>a_(n-1)` for `n>=2` in the computed range.

All arithmetic above is integer or `fractions.Fraction` arithmetic.

The optional symbolic script generates the local Gaussian expansion through
fourth order from its logarithm, integrates monomials by exact Gaussian
moments, and checks the displayed unperturbed R1/R2 terms and logarithmic cross
term. It also checks exponentiation of the component expansion, the outer
amplitude through second order, logarithmic degrees and leading coefficients,
B/B3 arithmetic decompositions, the mean/variance constants, and the explicit
first refined correction polynomials M1 and V1. The B/B3
checks verify the stated arithmetic pieces, not the infinite-tail summations
that produced those pieces. Those derivations remain in the report.

## In-memory API

```python
from exact_nested import (
    component_counts, nested_counts, nested_triangle, rational_egf_counts,
    rational_power_triangle, literal_nested_triangle, exact_moments,
    exact_inverse,
)

base = component_counts(100)       # B[0],...,B[100], Python integers
counts = nested_counts(100)        # a[0],...,a[100]
rows = nested_triangle(100)        # rows[n][k], including zero column
independent_base, independent_counts = rational_egf_counts(100)
power_rows = rational_power_triangle(30)
literal_rows = literal_nested_triangle(7)
moments = exact_moments(100)       # exact Fraction mean and variance
threshold_index = exact_inverse(45, n=100)  # 5, since a_4=44 and a_5=270
```

`exact_inverse(y,n)` accepts a positive integer threshold and returns the least
index in `0..n` whose exact count reaches it. It raises `ValueError` if the
threshold exceeds `a_n`; it does not guess beyond the bounded range. Under the
empty extension, `exact_inverse(1)=0`, since `a_0=a_1=1`. No asymptotic rounding
or unproved separation from an integer is used. `exact_moments` selects an
object uniformly from all size-`n` objects and returns exact rational moments.

Invalid public arguments raise `ValueError`. A failed mathematical check raises
`CheckFailure`. Underscore-prefixed functions are internal helpers.

## Captured evidence

The source package includes:

- `../data/published_fixtures.json`: frozen published numeric terms with source
  URLs, revision headers, and hashes of the previously saved source text
- `../data/full_verification.json`: a deterministic exact-check summary and
  selected rational moments
- `../data/exact_data_100.json`: the same summary plus all exact component
  counts, nested counts, and triangle entries through 100 as decimal strings
- `../data/tests.normal.json`: eight regression groups, including deliberately
  failed checks, invalid inputs, CLI behavior, exact moments, and exact inverse
  threshold equality cases
- `../data/symbolic.normal.json`: optional exact symbolic check results,
  including the SymPy version

The exact verifier, regression suite, and optional symbolic checks were each
run in normal and optimized Python. Each pair of outputs agreed byte for
byte. The commands above repeat those comparisons; the packaged normal outputs
are evidence, not verification input. See `PROVENANCE.md` for public source
attribution and scope.

## What these results do and do not certify

These are **exact finite checks**, not a proof that a tested identity holds for
all sizes. They do not certify the analytic expansion's remainder constants,
its effective onset, complex uniformity, suppression of all secondary arcs,
a central or local limit theorem, historical priority, or numerical enclosures
of transcendental constants. The report supplies the analytic argument and
states its credited hypotheses separately.

No floating-point asymptotic diagnostics are included or required. Any decimal
asymptotic comparisons elsewhere in the report remain explicitly uncertified;
they are not made certified by agreement with these exact finite counts.
Third-party PDFs, HTML, repository code, and source snapshots are not packaged
or fetched by this companion.

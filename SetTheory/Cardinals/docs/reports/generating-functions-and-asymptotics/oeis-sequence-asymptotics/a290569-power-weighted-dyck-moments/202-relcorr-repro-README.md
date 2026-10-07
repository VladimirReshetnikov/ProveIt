# Report 202 finite reproduction

This component is portable. All paths used by the programs are relative to the
component or are explicit output arguments. No network, private working tree,
source PDF, NumPy, SymPy, or external data download is required.

## What is and is not checked

`check.py` uses only Python's standard library. At the release setting
`--max-n 64`, its 4,549 exact predicates comprise:

| Category | Count |
|---|---:|
| Integer transfer DP versus independent path-continuant division | 715 |
| Full path enumeration versus DP, through n=8 | 126 |
| Exact occupation-mass identities | 126 |
| Non-last-descent counts | 504 |
| Primitive negative excursion k=1 weights | 504 |
| Truncated marked-excursion deletion identities | 1,918 |
| Exact rational change-of-measure identities | 36 |
| Reciprocal-cosine/secant convolution coefficients | 65 |
| Formal secant-operator constant coefficients, including odd zeros | 41 |
| Finite sine-product/factorial identities | 128 |
| Oscillatory product telescoping identities | 128 |
| Positive rational oscillatory anchors | 128 |
| Oscillatory formal logarithmic coefficients | 2 |
| Equal-linear polynomial logarithmic coefficients | 6 |
| Quadratic Stirling coefficient arithmetic | 1 |
| Rational Catalan branching convolution identities | 72 |
| Pinned fixture identities | 49 |

There are 4,421 equalities and 128 positive rational predicates. These are finite
identities and algebraic checks, not exact verification of any limit theorem.
The 715 integer moment values and exact rational occupation/product data are
saved in `generated/exact_data.json`; integers and fractions have canonical
string encodings so readers do not silently round large integers.

The seven fixture sequences are the moments at n=0,...,6 for h, h^2, h^3, h^4,
4h^2-1, h^2(4h^2-1), and the rational oscillatory quartic weights. They were
frozen from full path enumeration, and are checked against the distinct transfer
recurrence. They are not advertised as externally sourced sequence tables.
The quadratic anchors also have an independent reciprocal-cosine convolution
and the formal operator L=(1+z^2)d/dz+z.

`diagnostics.py` is imported only when requested. It uses mpmath 1.3.0 at 90
working decimal digits and prints 40 significant digits. Printed digits are not
certified accuracy or interval bounds. At nmax=256 it performs 268 separately
classified numerical predicates: nine finite-cutoff regularization comparisons,
two special-constant comparisons, three independent infinite-product route
comparisons, 250 interpolation/inverse algorithm comparisons, and four finite
occupation-mass comparisons. The analytic regularization truncation bound is
itself evaluated numerically; floating-point roundoff is not enclosed.

Convergence rows cover:

- Bulk q=2 changes h^p -> h^p(1-1/(4h^2)), for p=2,...,6
- Critical changes h^p -> h^p+1/h, for p=1,2,3
- Endpoint changes of the height-one weight from 1 to 2, for p=1,...,5
- A genuinely oscillatory cumulative example, for p=2,3,4,5
- Two quadratic and two quartic absolute polynomial compositions
- Relative inverse displacement in the three regimes, plus bulk and endpoint
  examples whose displayed coefficient vanishes
- Finite local occupations for p=2,4 at n=32,64, below the arch top

No convergence row is used as a tolerance test of its limiting prediction.
The local rows do not claim convergence at the singular arch top or a rate.
The inverse rows use the exact base log-linear interpolation at the normalized
threshold Y/P, evaluated in multiprecision, and allow a nonmonotone early
prefix. They are not Lambert approximations or effective rounding rules.

For the cumulative example,

    a_0=1,  a_h=1+1/(3h)+(-1)^h/(4h^2),
    lambda_h=h^p,  tilde_lambda_h=h^p a_h/a_(h-1).

The finite product is exactly a_N. Its logarithmic partial sum has S=0 and
A=1/3. The even and odd limits of h^2 f_h are 1/6 and -5/6. The exact tests
check the rational telescoping identity and the formal degree-two logarithmic
coefficients; the analytic limiting argument is in the article. Its p=4
cumulative target is pi/12. The data at n=256 give approximately
0.2615449207687646966460419523252892644166.

No general-p absolute candidate coefficient is generated or asserted here.
In particular, source-conditional stronger Freud implications remain
conditional; numerical evidence does not repair an unavailable primary-source
hypothesis. An improved little-o conclusion after cancellation is not a claim
about the next nonzero correction.

## Commands

From this directory, using a *new* output directory on every generation:

    python -S check.py --max-n 64 --out ../exact-replay
    python check.py --diagnostics --out ../complete-replay
    python -O check.py --diagnostics --out ../optimized-replay
    python check.py --verify generated --diagnostics
    python -O check.py --verify generated --diagnostics
    python -S test_guards.py
    python test_guards.py --diagnostics
    python -O test_guards.py --diagnostics

`--verify` checks strict member inventories, canonical JSON and SHA-256 hashes,
then recomputes both exact data and exact check counts. `--verify --diagnostics`
also recomputes the complete numerical file. Without `--diagnostics`, numerical
files present in the verified directory receive schema/hash checks but no
numerical replay. A manifest is an integrity check, not a signature.

The release uses exact nmax=64 and diagnostic nmax=256. Other supported values
are exact 16..256 and diagnostic 64..512; changing them intentionally changes
outputs and counts. The release mode pins 90 decimal digits and mpmath 1.3.0.
No output directory is overwritten. Exact standalone mode is tested with
`python -S`, with site-packages disabled, and leaves its source untouched.

The 87 standard-library guard checks and 23 additional optional numerical
checks reject malformed JSON, bool-as-int inputs, noncanonical fractions,
wrong fixtures, unsafe member names, symlinks, hash mismatches, inconsistent
exact counts, and generated values even after their checksums are recomputed.
The full numerical guard also rejects a plausible altered diagnostic whose
manifest was recomputed. A deliberate replacement of an explicit guard by a
Python `assert` is detected in optimized mode. No production check uses
`assert`. Normal and optimized guard receipts are identical.

## Files and provenance

- `check.py`: exact recurrences, enumeration, fixtures, strict output validation
- `diagnostics.py`: optional multiprecision computations and schema validation
- `test_guards.py`: adversarial tests, including normal/-O runtime probes
- `data/fixtures.json`: seven finite sequences and two parity coefficients
- `generated/exact_checks.json`: exact predicate inventory
- `generated/exact_data.json`: exact moments and rational data
- `generated/numerical_diagnostics.json`: numerical rows and predicate inventory
- `generated/manifest.json`: generated-file hashes, lengths, and exact allowlist
- `requirements.txt`: pinned optional numerical dependency

The implementation recombines finite recurrences and examples used while
checking the article's proofs, with strict portable I/O and active runtime
checks. This implementation's checks are reproduction support, not a new
independent mathematical audit. The article contains the complete proofs
and names the relevant classical sources.

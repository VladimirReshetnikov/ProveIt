# Report146: new exact finite-algebra companion

This is a new Python standard-library companion for the all-fixed-orders,
third-order, inverse, ratio, and acceleration algebra in Report146. It uses
`fractions.Fraction`, integer arithmetic, and finite polynomial coefficient
maps. It does not use floating-point arithmetic, SymPy, numerical fitting,
network access, downloads, or old computational archives.

**A successful run verifies finite exact identities only.** It does not prove
uniform remainders, the signed-convolution bound, absolute or uniform moment
convergence, the all-orders induction, the critical infinite-tail boundary
condition, Newton convergence, the first-crossing theorem, interval-evaluator
termination, effective thresholds, or new decimal digits of any connection
constant or of the placement rate. Those are analytic results or inputs in
the report and its included foundation articles. In particular, the optional interval
examples below are synthetic rational data, not evaluations of the placement
sequence or a new rate-enclosure iteration.

## Reproduce

Python 3.9 or later and a POSIX filesystem with directory-descriptor and
no-follow support suffice. The recorded run used Python 3.12.14 on Linux.
From this directory, run:

```sh
python3 -I checks.py
python3 -I -O checks.py
python3 -I test_checks.py
python3 -I -O test_checks.py
```

All four commands must exit zero and print JSON with `"status": "passed"`.
`-I` isolates imports from the current directory and user site packages.
`-O` disables Python `assert` statements; neither source file contains any.
The verifier uses explicit checked exceptions; the adversarial suite uses
`unittest` methods, which remain active under optimization. The adversarial
suite normally takes tens of seconds; its negative tests deliberately run
the full verifier on schema-valid but false fixtures and run fresh CLI
subprocesses. It writes only uniquely named temporary test files inside this
companion directory and removes them after each test.

To write fresh receipts without overwriting any file:

```sh
python3 -I checks.py --output replay-receipt.json
python3 -I test_checks.py --output replay-tests-normal.json
python3 -I -O test_checks.py --output replay-tests-optimized.json
```

Choose new names for subsequent runs. Existing targets are deliberately
refused. The supplied `receipt.json` is the normal verifier receipt;
`tests-normal.json` and `tests-optimized.json` are the adversarial receipts.
The latter record source hashes, the fixture's byte hash, optimization mode,
and the number of test methods and object/integer sites attacked. Verifier
receipts record the canonical JSON fixture hash and implementation hash.
Normal and optimized verifier results agree after removing only
`python_optimization`. The test receipts likewise differ only in that field.
No timestamps or machine-specific absolute paths enter these receipts.

The default fixture is always resolved beside `checks.py`, irrespective of
the working directory. To check a different bounded fixture already present in this directory, pass
its simple filename with the `--fixture` option.

Only simple JSON filenames in this companion directory are accepted for
inputs and outputs. Absolute paths, path separators, `.`/`..` components,
embedded NUL, symlink files, symlink ancestors, directories, and special
files are rejected. Ancestors are opened one component at a time with
`O_DIRECTORY | O_NOFOLLOW`; leaf reads use `O_NOFOLLOW | O_NONBLOCK` and a
regular-file check. New output creation uses a held directory descriptor,
`O_CREAT | O_EXCL | O_NOFOLLOW`, and mode 0600. There is no check-then-overwrite
window and no CLI route for writing outside this directory. Shell redirection
is outside these safeguards; do not redirect over a file you want to keep.

## What is independently recomputed

1. **Logarithmic coefficient models.** With `u=1-z` and `L=-log(1-z)`, repeated
   finite convolution of `[z^n]L=1/n` is compared with
   `q!/n * e_(q-1)(1,1/2,...,1/(n-1))`. The empty and zero-index cases are
   included. Multiplication by `u^a` is finite signed binomial convolution.
   Products `u^a L^q * u^b L^s = u^(a+b)L^(q+s)` are checked coefficientwise,
   and the supplied fixture contains independently stated rational anchors.
   This checks exact coefficients, not their asymptotic expansions.

2. **Signed discrete Taylor identity.** Rational sequences with both signs
   test the exact Newton formula, including its signed remainder and the
   sum of its nonnegative binomial weights. Cases `i<M`, `i=0`, and full-length shifts are treated without
   negative sequence indices. The finite identity does not certify a bound
   on any unknown infinite residual sequence.

3. **Critical inverse algebra.** Every unit vector through the fixture's
   index bound is transformed independently by integrating its finite
   expansion `(1-u)^m`. Its coefficients are compared with the explicit
   local-plus-tail matrix weights, including all finite-support boundary
   cases. For `u^a L^q`, the displayed antiderivative is checked by exact
   derivative cancellation, by its coefficient equation, and by the exact
   finite-tail identity

   ```text
   T_K(h)_n - y_n = (n+1)/(K+2) * [h_K/(K+3) - y_(K+1)],
   T_K(h)_n = h_(n-1)/(n+2)
              - 2(n+1) sum_(k=n)^K h_k/[(k+1)(k+2)(k+3)].
   ```

   The boundary term is retained. A negative-control test confirms it is
   nonzero in a logarithmic example; a finite truncation is never presented
   as the infinite inverse. The critical constant term is explicitly
   checked as `-q!/(a+3)^(q+1)`. Justifying the integral at zero and the
   infinite-tail limit remains an analytic obligation.

4. **Kernel and third-order constants.** The first three Stirling-remainder
   coefficients are obtained by triangular finite difference matching.
   Formal exponential recurrences construct the first three `G_k(v)` and
   `H` coefficients; rational polynomial integration gives
   `b_3=25009/362880`, `h_3=-71329/51840`,
   `<U,U>=-7/360`, and `<U,V>=173/15120`.
   The coefficient of the unspecified scalar `C` in the last pairing
   vanishes because `integral U=0`. The same exact zero eliminates the
   prospective `u L^3` term. Algebra in the formal scalar `S_A` gives

   ```text
   L_2 = 617/11340 - (7/270) S_A,
   [log n / n^3] x_n = 323/22680 - (7/540) S_A,
   [log n / n^3] W_n/(A sqrt(n) r_*^n)
       = 22/2835 - (7/540) S_A.
   ```

   The `K_x` index rearrangement and `B_3=K_x+C/2+3/32` normalization shift
   are also checked. No value is assigned to `S_A`, `B_2`, `K_x`, or `B_3`.

5. **Finite scalar moments.** At every supplied order, explicit enumeration
   of `(k,p,q)` with `1<=q<=p<=M`, `0<=k<=M-p` has cardinality
   `M(M+1)(M+2)/6`. The allowed exponent inequalities are checked at each
   index. These are indexed upper counts, not minimality or independence
   claims; finite enumeration does not prove convergence of the moment sums.

6. **Formal root inversion.** A sparse multivariate rational polynomial ring
   treats `b,c,k,a,d,e,lambda_inverse,ell` as independent symbols. The program
   expands the exact smooth-model substitution and solves triangularly for
   the first three correction polynomials. Against independently stated
   fixture monomials it checks

   ```text
   R_1 = b/lambda,
   R_2 = (c ell+k)/lambda + b/(2lambda^2),
   R_3 = (a ell^2+d ell+e)/lambda
         + (c ell+k)/(2lambda^2) - b^2/lambda^2
         + b/(4lambda^3).
   ```

   Substitution cancels coefficients through order three exactly. The next
   residual is explicitly nonzero, and a deliberate mutation breaks the
   cancellation. The Newton exponent recursion `p_(k+1)=2p_k+2` is compared
   with `p_k=3*2^k-2` for eight finite indices. These are formal coefficient
   and integer identities, not root-convergence or ceiling-bracket proofs.

7. **Ratio and dyadic acceleration.** Exact formal quotient algebra, keeping
   arbitrary third-order forward symbols until they cancel, gives

   ```text
   rho_n/r_* = 1 + 1/(2n) - 3/(8n^2)
                + [(7/270)log n + 32/135 - 2B_2]/n^3
                + terms of higher formal order.
   ```

   Finite multiplication constructs the accelerator polynomial
   `Q_J(E)=product_(j=1)^J [(E-2^(-j))/(1-2^(-j))]^max(1,j-1)`
   for `J=1,...,6`. Its weights preserve constants and satisfy every
   requisite weighted power-moment cancellation. At `J=3` the weights are
   exactly `(1,-22,168,-512,512)/147`. They kill the three inverse powers
   and the third-power logarithm algebraically. The analytic error estimate
   for extrapolating the actual sequence is not a conclusion of this test.

8. **Optional finite interval checks.** Synthetic positive rational input
   intervals for `a,v,C`, including a negative refined numerator, test
   `A=z+v`, `B=z+v/a`, `P=z+v/a-C/a^2` against the outward endpoint rules.
   Endpoints and midpoints are exact fractions. Additional finite checks
   cover strict interior choices, reciprocal width, coarse intersection
   geometry, and the rational contraction constants `1203/1600` and
   `313/400`. No transcendental function or placement coefficient is
   evaluated, and no new rate digits are certified.

## Closed fixture and adversarial tests

`fixture.json` is newly authored for this report. The top-level schema and
every nested object have exact allowed key sets. Inputs are data only, never
expressions evaluated by Python. Expected values have semantic force:
they are compared with the independently recomputed identities above,
rather than merely checked for syntactic shape or echoed to the receipt.
Parameters are allowed to vary only within bounded domains.

- JSON duplicate keys, including escaped-equivalent names, are rejected at
  every object level
- JSON noninteger numbers, NaN, and infinities are rejected before validation
- Integer fields use exact `type(x) is int`; booleans, floats, strings, and
  null cannot substitute for integers
- Rationals must be reduced strings `numerator/positive_denominator`, with
  no leading zero, plus sign, negative zero, whitespace, or zero denominator
- Numerators and denominators have at most 24 digits; fixture bytes are at
  most 65,536, lexical nesting at most 24, and structural punctuation at most
  6,000 before JSON parsing
- Array sizes, index ranges, moment order, polynomial degree, monomial count,
  and integer-token length are explicitly bounded; sparse terms are unique,
  lexicographically ordered, and nonzero
- Unknown or missing keys are attacked at every object in the shipped
  fixture; every integer site is attacked with bool/float/string/null
- Every expected rational coefficient or endpoint is perturbed to a different
  *schema-valid* value and must fail exact semantic verification; every
  moment count is likewise perturbed
- CLI tests cover genuine success, invalid fixture rejection before output,
  duplicate keys, no overwrite, no traversal, no external path, symlink and
  dangling-symlink targets, symlink ancestors, directory/FIFO rejection,
  oversized files, non-cwd invocation, and optimization-safe checks

The shipped fixture requests log-model coefficient indices through 24, log degree through four,
unit vectors through index 14, logarithmic inverse tails through 24, scalar
moment orders 1 through 10, and accelerator orders through six. Increasing a
parameter inside its accepted range gives more finite tests, never an
analytic proof. The tests intentionally include signed inputs and boundary
terms rather than assuming favorable signs or silently discarding endpoints.

## Analytic labels and design provenance

The fixed fixture labels identify obligations **not proved by this program**:

- A1: normalized placement recurrence and all-index positivity
- A2: cleared second-logarithm rate and second-order constant identification
- A3: critical boundary condition for the exact inverse
- A4: uniform kernel remainders, signed convolution bounds, convergent moments
- A5: fixed-order forward remainder and positive-prefix argument for root inversion
- A6: real-axis bounds and evaluator termination for rate enclosures

A4 and parts of A5/A6 are conclusions proved in Report146, rather
than extra assumptions of the article's theorem. They are external analytic
obligations from the finite companion's perspective. For the analytic arguments, consult these sections of the included article:

- Report146, “The exact kernel and its uniform expansion” and “Exact coefficient models”
- Report146, “Signed convolution and endpoint moments” and “The forcing identity and the induction”
- Report146, “A finite scalar recursion” and “The explicit third order”
- Report146, “The first logarithm in the consecutive ratio”
- Report146, “All fixed orders of the threshold inverse”
- Report146, “A computable refinement of the exponential rate”

The included foundation sources supply the prior placement recurrence,
normalization, rate bracket, critical inverse, and first two corrections:

| Included source | SHA-256 |
|---|---|
| `../foundation/Report144.tex` | `cf59fa5799913142869a7a79e2b8ec4d04a9c174fdfc7f76d53f86e7d63d44c4` |
| `../foundation/Report145.tex` | `9e14d0c4797f0387d4441e1e6b4cd751e4d8577f693de640dcdaff63c8769d5b` |

The archive-level `../SHA256SUMS` identifies the final Report146 source and
all companion artifacts; `../SOURCES.md` records the article's dependency
boundary. The companion does not need the development material to run.

The Report145 companion README and initial implementation were inspected for
its design conventions: canonical exact rationals, explicit exceptions,
closed fixtures, and no-overwrite receipts. No Report145 implementation,
fixture, result, or old numerical archive was copied into this companion.
The present coefficient-basis engine, signed Taylor samples, finite inverse
checks, sparse three-order inverse ring, kernel construction, ratio and
dyadic tests, and bounded CLI validation are newly implemented here. The
optional ratio/accelerator identities come from the integrated Report146
continuation and are independently recomputed by the finite algebra above.

The companion consists only of this README, `checks.py`, `test_checks.py`,
`fixture.json`, and the three recorded JSON receipts. It can be relocated
with the report archive and replayed without access to the source research
folders. Source hashes are provenance, not a substitute for analytic proof.

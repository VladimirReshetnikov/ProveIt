# Verification scripts

These scripts audit finite algebraic calculations and provide independent numerical comparisons for the accompanying article. The proofs in the article establish the general identities and continuation statements. The scripts do not perform formal proof checking, and their decimal calculations are not interval certificates.

## Requirements and execution

The scripts require Python 3 and the third-party packages `mpmath` and `sympy`. The preparation environment used Python 3.12.14, mpmath 1.3.0, and SymPy 1.14.0. `verify_derivative_pair.py` uses only mpmath; the other four use both packages. All other imports are from the Python standard library. No external data, network access, TeX installation, or computer algebra system is required to run them.

Install the dependencies in the Python environment of your choice:

```bash
python3 -m pip install mpmath==1.3.0 sympy==1.14.0
```

From this directory, run the scripts individually:

```bash
python3 check_beta.py
python3 centered_checks.py
python3 check_quartic.py
python3 verify_collision.py
python3 verify_derivative_pair.py
```

Each command takes no arguments and writes its JSON report beside its own script, replacing the existing report after successful completion. The scripts also print results or progress to standard output. Run Python without `-O`, because mathematical checks use assertions. If a run terminates before writing its report, a previously supplied JSON file may still be present; its existence alone does not establish that the new run completed.

Runtime depends on the Python environment and numerical libraries. High-precision quadrature, infinite-sum acceleration, zeta derivatives, and repeated Mellin evaluations account for most of the work. The supplied quartic report records approximately 14.6 seconds for its preparation run; the other reports do not record elapsed time. Displayed decimal digits are working or output precision, not a guarantee that every displayed digit is correct.

## Script and output map

| Script | JSON report | Main subject | Decimal working precision |
| --- | --- | --- | --- |
| `check_beta.py` | `beta_checks.json` | Beta–Hurwitz integrals, Fourier coefficients, logarithmic Stieltjes moments, Gamma and cubic identities | 60 |
| `centered_checks.py` | `centered_checks.json` | Centered harmonic polynomial poles and trigamma-square moments | 65; 105 for the explicit head-and-tail calculation |
| `check_quartic.py` | `quartic_checks.json` | Quartic Tornheim rays and formal relation spaces | 55 |
| `verify_collision.py` | `collision_verification.json` | Cubic and quartic cluster counterterms and collision limits | 55 |
| `verify_derivative_pair.py` | `derivative_pair_verification.json` | Repeated-pole pairs and their reflection identity | 65 |

The JSON reports are recorded calculation results, not immutable reference files against which the scripts compare their output. Floating-point formatting and final digits may vary between library versions.

## `check_beta.py`

The exact SymPy calculations verify the normalized Fourier coefficient expansion through quadratic order in its parameter, at Fourier indices 1, 2, 4, and 7. These are finite coefficient checks; the all-index derivation is in the article.

The mpmath calculations compare independently evaluated expressions for:

- The beta-weighted Hurwitz integral at integer beta orders 1, 2, and 3, using a complex spectral parameter and a finite Fourier sum.
- A nonintegral polylogarithmic Euler-transform representation.
- Three beta-weighted log-Gamma integrals and the corresponding derivative of the beta mean.
- The first logarithmic Stieltjes moment and the second logarithmic harmonic bridge.
- An incoming cubic finite-part identity and the new combination that eliminates its harmonic constant.

The cubic finite part is computed by local Laurent subtraction followed by quadrature. The harmonic coordinate is computed from a finite digamma sum and a truncated Stirling–Hurwitz tail. These numerical procedures do not include an interval error analysis. The asserted absolute tolerances are `1e-40`, except `1e-28` for the nonintegral Euler transform, whose quadrature has integrable endpoint singularities. The report records the two evaluated sides, their computed discrepancy, and each tolerance; `all_passed` summarizes these finite checks.

## `centered_checks.py`

The exact symbolic portion checks:

- The centered formal translation recurrence through degree 14.
- The affine relation between harmonic-order expansions and digamma derivatives for orders 2 through 8, through the same finite degree.
- Six polynomial examples of the parity criterion, including invariant numerators, a noninvariant raw square, and a delayed first pole.
- The near-miss numerator whose first odd coefficient vanishes but whose next odd coefficient is `5*Z2/2 - 1`.
- Nine Faulhaber block constants, for odd block indices 3 through 19.

Here `Z2`, `Z3`, and so on are symbolic placeholders for zeta values. The near-miss check explicitly substitutes the known relation `Z4 = (2/5)*Z2**2`. The report also tabulates the exact rational and zeta(3) coefficients of the all-moment formula for moment indices 0 through 10. Generating that table is evaluation of the closed formula; the separate Faulhaber calculations and direct sums provide its finite cross-checks.

At 65 working digits, mpmath's infinite-sum routine evaluates the four ordinarily convergent bracketed moments with indices 0 through 3 and compares them to the closed formula, with asserted discrepancy below `1e-48`. These checks do not sum the divergent unbracketed expressions.

An independent calculation evaluates moment indices 0 through 6 using 64 head terms, a finite Bernoulli tail with parameter `K=30`, and 105 working digits. The infinite tail of the finite squared polynomial is summed using Hurwitz zeta values. Its truncation has an analytic bound, proved in the article's verification note.

Specifically, put

$$
T(x)=\psi'(x+\tfrac12),\qquad
A_K(x)=\sum_{j=0}^{K}B_{2j}(\tfrac12)x^{-2j-1},\qquad
C_K=\frac{2(2K+2)!}{(2\pi)^{2K+2}}.
$$

For real `x > 0`, the hyperbolic-cosecant partial fraction expansion and the trigamma Laplace integral imply

$$
0<T(x)\le x^{-1},\qquad
|T(x)-A_K(x)|\le C_K x^{-2K-3}.
$$

With `a=N+1/2` and

$$
C_A=\sum_{j=0}^{K}|B_{2j}(\tfrac12)|a^{-2j},
$$

the weighted squared-tail error for moment index `M` is bounded by

$$
C_K(1+C_A)\zeta(2K+4-2M,a).
$$

The JSON fields `absolute_difference` and `analytic_tail_error_envelope` record the comparison. All seven recorded discrepancies lie below their envelopes. The bound rigorously controls asymptotic-tail truncation in exact arithmetic. The mpmath evaluations of the head, Hurwitz zeta tail, closed-form target, and envelope are not interval enclosures, so the script is not a complete certified numerical enclosure.

## `check_quartic.py`

Exact SymPy simplification checks the quartic ray formula against its direct coordinate expansion, its cyclic sum, its diagonal and Euler specializations, and the elementary terms in two integral coordinates. Exact integer counts verify the stated formal dimension formulas through order 30. The script also verifies a fifth-order polynomial obstruction: it vanishes on the tested boundary and full diagonal but is not the zero polynomial.

These checks concern identities of formal polynomials and rational functions. They make no claim of arithmetic independence of the evaluated Tornheim constants. The all-order relation-space proof remains the argument in the article, rather than a consequence of counting finitely many orders.

The numerical portion computes the quartic coordinates from Gamma-remainder and Mellin-integral expressions. It then obtains fourth ray derivatives by a 15-node finite-difference formula applied to an independently implemented Mellin continuation. The four tested slopes are `(1,1,1)`, `(1,0,2)`, `(1,2,2)`, and `(1,-2,3)`. Each computed discrepancy is required to be below `1e-24`.

The Mellin expansions, large-variable sums, and finite differences are truncated numerical procedures. Their combined errors are not enclosed by intervals in this script. The reported `error` is the discrepancy between the two numerical routes, not a proved error bound for either route. The default finite-difference spacing and cutoffs are visible in the source.

## `verify_collision.py`

Two exact SymPy calculations check the hierarchical cubic counterterm expansion for shifts `(0,e,e+e**2)` through its finite terms, and the constant term of the equally spaced quartic counterterm for shifts `(0,e,2*e,3*e)`.

The numerical calculation evaluates the separated finite-part circle integral by subtracting each actual pole on its own interval and adding the corresponding elementary finite primitive. This evaluation does not use the proposed collision counterterm to calculate the separated integral. The merged cubic and quartic finite parts are independently evaluated by endpoint Laurent subtraction.

The script then records results at `e=0.03, 0.01, 0.003, 0.001`. In its notation, `C` is the separated finite part, `T` the local counterterm, and `Q` the merged finite part. The field `C_minus_T_minus_Q` is a finite-separation remainder in a limit statement:

$$
C(e)-T(e)\longrightarrow Q\quad(e\downarrow0).
$$

It is not an error in a claimed equality at positive `e`, and it is not a quadrature error estimate. The recorded remainders approach zero in the tested examples, as the theorem predicts. The script intentionally does not assert that they are zero or below a fixed numerical tolerance. Its symbolic assertions establish only the two stated finite expansion checks; convergence for general configurations is proved in the article.

The collision script uses `f(x)=-digamma(x)`. Consequently its merged cubic value `Q_3` has the opposite sign from the cubic finite part of `digamma(x)**3` reported as `Q` in `beta_checks.json`.

## `verify_derivative_pair.py`

This mpmath-only script independently evaluates finite parts for derivative orders `(1,0)` and `(0,1)` at the same four positive separations. It removes the double or simple pole by local Taylor subtraction, then integrates the regular remainder and restores the elementary finite primitive. A short Taylor approximation is used very close to an interval endpoint to limit cancellation; its error is not enclosed by interval arithmetic.

The fields `C_minus_T` and `C_minus_T_minus_zeta2` record the approach of each counterterm-subtracted expression to zeta(2). As in the cluster script, the second field is a genuine finite-separation remainder, not an equality error or an estimate of numerical integration error.

There is also a separate numerical equality check at each fixed separation:

$$
C_{1,0}(e)+C_{0,1}(e)=\frac{\pi^2}{\sin^2(\pi e)}.
$$

The script asserts a computed absolute discrepancy below `1e-35` for this reflection identity, and records those discrepancies under `independent_reflection_identity`. This supplies an independent consistency check on the finite-part quadrature. It does not turn the separately recorded collision-limit residuals into numerical errors or certify the full general repeated-pole theorem.

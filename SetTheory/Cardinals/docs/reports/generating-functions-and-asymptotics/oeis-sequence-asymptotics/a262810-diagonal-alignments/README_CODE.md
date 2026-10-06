# Report177 exact-rational verifier

This directory is a self-contained, standard-library-only arithmetic supplement. It verifies exact finite identities and coefficient calculations. It does **not** turn finite tests into proofs of the analytic remainder estimates, asymptotic expansion, or central limit theorem; those proofs belong to Report177.

## Run

Use Python 3.9 or later. No package installation, network access, SymPy, mpmath, decimal, or floating-point arithmetic is needed.

```sh
CHECK_DIR=$(mktemp -d)
python3 -E -B verify_report177.py --output "$CHECK_DIR/checks.json"
python3 -E -B -O verify_report177.py --output "$CHECK_DIR/checks.optimized.json"
cmp "$CHECK_DIR/checks.json" "$CHECK_DIR/checks.optimized.json"
cmp checks.json "$CHECK_DIR/checks.json"
python3 -E -B verify_report177.py --order 5 --output "$CHECK_DIR/checks.order5.json"
cmp checks.order5.json "$CHECK_DIR/checks.order5.json"
python3 -E -B check_reproducibility.py --output "$CHECK_DIR/reproducibility.json"
```

Use fresh output paths outside the extracted release package: its inventory is immutable. The default fixed coefficient order is 3. `--order J`, for any integer `J >= 3`, invokes the same finite algorithm through order J. It is not a lookup table restricted to the displayed coefficients. Higher orders require more time and memory. Internally the coefficient functions also accept nonnegative orders, including 0. Both programs write JSON only to the explicit `--output` path, or to stdout when no path is supplied. They do not alter source files, upload results, or write outside the selected output path except for the reproducibility check's automatically cleaned temporary directory.

JSON has sorted keys and exact reduced rational strings, with no timing or machine-specific metadata. The default result includes negative-input tests in separate normal and `-O` subprocesses; `-E` makes those modes independent of the `PYTHONOPTIMIZE` environment variable. The recorded optimization levels are 0 and 1. The cached public Bernoulli helper uses `typed=True`; six explicit tests first warm integer keys 0 and 1, then reject equivalent bool, float, and Fraction inputs. The public `weak` parameters require genuine bool values and are tested against integer, float, and Fraction lookalikes. All correctness and input guards are ordinary exceptions, never removable assertion statements. A failed identity gives a nonzero exit code.

## Files and coverage

- `verify_report177.py`: exact polynomial, coefficient, count, distribution, tail, and moment algorithms
- `checks.json`: deterministic default-order output, including every rational enclosure endpoint and the complete finite distributions
- `checks.order5.json`: an extension test through L5/C5, including agreement with the independent Gaussian route at all five orders
- `check_reproducibility.py`: reruns the normal and optimized default calculations, compares both byte-for-byte with the frozen output, reruns order 5, rejects an invalid CLI order, and checks that the verifier's imports are standard-library modules and that its syntax tree has no assertion statements
- `reproducibility.json`: results and output SHA-256 digests from that check

The default run verifies:

1. B1–B4 by Bernoulli polynomial construction, by comparison with the stated formulas, and by direct centered power sums at n=1,…,10
2. R0–R3, L1–L3, and C1–C3 by a gamma-central-moment coefficient calculation, and R0–R3 independently by a Gaussian Laplace calculation
3. Complete binary column-count distributions for n=1,…,10 by positive binomial-basis multiplication versus forward differences
4. Thirty exact positive-series rational enclosures, for n=1,…,10 and u=1/2,1,2, each with relative tail bound at most 10^-70
5. Independent grid recursion for both binary and nonnegative-entry full distributions through n=3
6. The marked A316677 polynomial convolution, its known total-count factor 2^(n−1), and exact first and second moments at all thirty (n,u) pairs
7. The exact auxiliary-M moment identities, using separate difference tables for inserted m and m² factors
8. Forty-five invalid-input or failed-invariant tests in both normal and optimized interpreters

The order-5 extension additionally verifies B1–B6 against centered sums and two independent R0–R5 coefficient calculations. Its extra polynomials are computational extension checks, not additional novelty claims.

## Exact all-fixed-orders coefficient construction

`Poly` is a small sparse Laurent-polynomial implementation. Its coefficients are `fractions.Fraction`; integer exponent tuples may be negative because the y-dependent calculation uses y^-2r. Addition, multiplication, integer powers, differentiation, substitution at y=1, and evaluation are implemented locally.

### Centered power sums, without interpolation

Bernoulli numbers use B0=1 and

    B_m = -sum_{k=0}^{m-1} binom(m+1,k) B_k / (m+1),

so B1=−1/2. Bernoulli polynomials are constructed by their finite defining sum. The verifier forms exactly

    n [B_(2r+1)((n+1)/2) − B_(2r+1)((1−n)/2)] / [2r(2r+1)].

Bernoulli summation identifies this with n/(2r) times the centered 2r-th power sum. Reflection makes it an even polynomial in n, which the code checks, and replacing n^(2j) by N^j produces B_r(N). Thus neither the polynomial degree nor its coefficients are inferred from finite test values. Direct sums supply a separate finite consistency test.

### Gamma route

Write epsilon=1/N and z=lambda. To depth J only r <= J+1 can contribute, since deg B_r=r+1. The code collects

    -sum_r B_r(epsilon^-1) z^(2r) epsilon^(2r) y^(-2r)
      = -z²/(24y²) + sum_{j=1}^J g_j(y,z) epsilon^j + higher terms.

The exponential recurrence gives H0=1 and

    H_j = (1/j) sum_{r=1}^j r g_r H_(j-r).

The exact signed gamma central-moment polynomial is

    mu_r(epsilon) = sum_{j=0}^r (-1)^(r-j) binom(r,j)
                    product_{i=1}^j (1+i epsilon).

Its valuation is at least ceil(r/2), checked algebraically for every moment used. Hence only derivatives through 2(J−q) contribute to epsilon^J from epsilon^q H_q. Repeated differentiation of exp(−z²/(24y²)) H_q is implemented without transcendental functions using the twisted operator

    T(f) = d f/dy + (z²/12)y^-3 f.

The expectation coefficient is obtained from T^r(H_q)(1) mu_r/r!. Logarithmic coefficients follow from

    L_j = R_j − (1/j) sum_{r=1}^{j-1} r L_r R_(j-r).

Finally, with b_r=B_(2r)/[2r(2r−1)],

    C_j = L_j − b_(j+1) + indicator(j odd) b_((j+1)/2).

The finite polynomial algorithm computes each fixed order exactly. The report separately justifies its asymptotic use: retain Taylor degree 2p+1 to bound the remainder by the absolute (2p+2)-th moment, then omit that odd term because it does not affect coefficients through epsilon^p. No numerical differentiation of a remainder is used.

### Independent Gaussian route

Set t=N^-1/2 and y=1+tv. The unnormalized gamma density has Gaussian factor exp(−v²/2) and the formal correction

    sum_{k>=3} (-1)^(k+1) v^k t^(k−2)/k.

Separately expand the centered product perturbation with

    (1+tv)^(-2r) = sum_{ell>=0} (-1)^ell binom(2r+ell−1,ell) (tv)^ell,

cancel its constant −z²/24, exponentiate through t^(2J), and replace even Gaussian monomials by

    E[v^(2k)] = (2k)!/(2^k k!),    E[v^(2k+1)] = 0.

Divide the resulting numerator series by the gamma density's own Gaussian normalization series. The code checks all odd t powers vanish and all even coefficients agree with the gamma-central-moment route. The two routes share the exact B_r polynomial input and elementary polynomial arithmetic, but do not share their expectation calculation.

## Independent finite counts and tails

For p_n(m)=binom(m,n)^n, the forward-difference method evaluates p_n at 0,…,n² and constructs d_(n,j)=Delta^j p_n(0). The independent positive method starts with 1 and multiplies n times by binom(m,n), using

    binom(m,r) binom(m,n)
      = sum_j binom(j,r) binom(r,r+n−j) binom(m,j).

All summands are nonnegative integers. Its full coefficient vector must equal the difference vector.

The positive series at rational u>0 is

    A_n(u) = 1/(1+u) sum_{m>=n} [u/(1+u)]^m binom(m,n)^n.

If t_m is the m-th summand and rho=u/(1+u), its exact ratio is

    r_m = t_(m+1)/t_m = rho [(m+1)/(m+1−n)]^n.

This ratio decreases with m and tends to rho<1. Once r_m<1, the unsummed tail after the last included term t_m is bounded above by

    t_m r_m/(1−r_m).

The verifier uses rational arithmetic for the summands, partial sum, ratio, tail, endpoints, and comparisons. It checks that the independently computed finite polynomial A_n(u) lies inside [partial, partial+tail], and that tail/A_n(u) <= 10^-70. The exact value is used to set the relative stopping scale and check the enclosure; the positive summation and tail calculation themselves are independent of the difference or product count algorithms. Every numerator and denominator needed to audit the result is saved.

For the small independent recursion, the state is the vector of remaining row sums. Every admissible nonzero next column is enumerated, and the child's column-count distribution is shifted by one. Binary entries use 0 or 1; nonnegative entries use 0 through the remaining row sum. The base state has one empty alignment. This verifies the full distributions, not only their totals.

## A316677 and exact moments

Let Atilde_n count nonnegative-entry matrices with no zero column. Its independently evaluated difference table uses binom(m+n−1,n)^n. The verifier checks the coefficientwise marked identity

    Atilde_n(u) = u^(-(n−1)) (1+u)^(n−1) A_n(u).

Binary support begins at degree n, so the right side is a polynomial. At u=1 this gives the previously recorded A316677 relation 2^(n−1) A262810. More generally, after normalization at fixed u,

    Ltilde =_d L − (n−1) + Bin(n−1, u/(1+u)),

with an independent binomial. Consequently its mean is mean(L)−(n−1)/(1+u), and its variance is var(L)+(n−1)u/(1+u)². Direct rational moments of the independently checked finite distributions verify both.

For the auxiliary positive-series M distribution, separate difference tables are constructed from m^k binom(m,n)^n, k=0,1,2, through their exact degrees n²+k. Summing their Newton-basis series evaluates the inserted moments exactly. The verifier checks

    E[L] = (E[M]−u)/(1+u),
    Var(L) = (Var(M)−u E[M]−u)/(1+u)².

At u=1 these reduce to the two identities used in the report. These finite rational identities require neither logarithms nor asymptotic approximations.

## Boundaries

The package does not verify source priority, evaluate the transcendental asymptotic constants numerically, certify a Berry–Esseen rate, or claim convergence of an infinite asymptotic series. It verifies the finite algebra and arithmetic supporting the separately written proofs. The earlier research/audit scripts were consulted for formulas and independent-method design, but the verifier does not import them or require their third-party libraries.

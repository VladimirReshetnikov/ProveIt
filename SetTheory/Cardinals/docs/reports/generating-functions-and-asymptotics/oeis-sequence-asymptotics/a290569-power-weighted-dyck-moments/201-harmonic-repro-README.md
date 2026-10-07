# Report201 reproducibility companion

This is a self-contained scientific reproduction of finite identities and numerical diagnostics for harmonic perturbations of weighted Dyck moments and the pure-power Freud comparison. It is not a source-audit archive. No private path, credentials, network call, or external source checkout is needed.

## Requirements and commands

- Exact checks: Python 3.9 or later, standard library only
- Optional numerical diagnostics: `mpmath` (the supplied data were generated with version 1.3.0)
- No NumPy, SymPy, compiler, TeX installation, or OEIS connection is required

From the `Report201/repro` directory, use these output paths outside the complete immutable package:

```sh
python check.py --out ../../exact-data
python check.py --diagnostics --out ../../all-data
python -O check.py --diagnostics --out ../../all-data-optimized
cmp ../../all-data/exact_checks.json ../../all-data-optimized/exact_checks.json
cmp ../../all-data/moments.json ../../all-data-optimized/moments.json
cmp ../../all-data/numerical_diagnostics.json ../../all-data-optimized/numerical_diagnostics.json
```

The default moment depth is 256, including n=0. Set `--max-n` in 48..512 if desired; increasing the depth makes the free-cumulant series inversion more expensive. Numerical precision defaults to 65 decimal digits; `--dps` changes it. Displayed diagnostics retain 30 significant digits and are not certified enclosures. The exact JSON is independent of `--dps`.

`check.py` sets `sys.dont_write_bytecode = True` before imports and does not import any local module. It creates no `__pycache__` in this package, even when the environment variable `PYTHONDONTWRITEBYTECODE` is unset. All tests raise explicit exceptions, rather than using removable Python `assert` statements. The program uses deterministic ordering, exact decimal strings for large sequence values, and no timestamp or local path in generated JSON. `generated/manifest.json` contains SHA-256 hashes of the generated products.

## Mathematical convention and actual sequence laws

M_n is the sum over Dyck paths of length 2n of the product of lambda_h for each downstep from height h. Thus M_0=1 and the ordinary generating function is

    M(z) = 1/(1 - lambda_1 z/(1 - lambda_2 z/(1 - ...))).

Scaling every weight by k multiplies M_n by k^n. Indices in `moments.json` always start at semilength n=0, regardless of a source's offset or sign convention.

| Entry | Downstep weight / interpretation |
|---|---|
| A216966 | h^3 |
| A218221 | h(h+1)(h+2)/6 = binomial(h+2,3) |
| A227887 | h^4 |
| A144849 | h(h+1)(2h+1)^2/3 |
| A144853 | h^2(4h^2-1)/3 |
| A261000 | h^2(4h^2-1), exactly 3^n A144853(n) |
| A104133 | positive moments are (-1)^n A104133(n), with the alternating Dixon weights below |
| A338634 | even free cumulants of the symmetric h^4 moment sequence, with constant term 1 added |

In particular, A218221 is not h^2(h+1), A144849 is not the cubic binomial-weight sequence, and neither A144853 nor A261000 has weight h(h+1)(h+2)(h+3)/24.

The auxiliary classical families are also generated through n=256:

- A000182(n+1): h(h+1)
- A002105(n+1): h(h+1)/2
- (-1)^n A326328(n): h(h+2)
- A395382(n), A395383(n): h(h+3), h(h+4)
- A000698(n+1), A167872(n), A321963(n): h+1, h+2, h+3

A187756(h)=h^2(4h^2-1)/3 is an auxiliary *weight* sequence, not the corresponding moment sequence.

### A338634 is a transform, not the quartic moment baseline

Let M(t)=sum A227887(n)t^n and A(x)=sum A338634(n)x^n. Factoring A from every denominator of the defining continued fraction gives

    A(x) = M(x/A(x)^2), equivalently M(t)=A(t M(t)^2).

The latter is the symmetric moment/even-free-cumulant relation. A_0=1 is a generating-function convention, not a zeroth free cumulant. The package generates A338634 by exact triangular composition inversion through 256, checks the composition coefficientwise, and independently solves its own defining nested continued fraction through 20. It does not invent a polynomial Dyck weight for A338634. Its displayed prefix is different from A227887 beginning at n=2: 15 versus 17.

## Exact validation scope

`data/oeis_displayed_terms.json` preserves the entire displayed term field for 17 inspected entries, with public URLs, revision/date metadata, and explicit offset/sign maps. No b-file terms, inferred tail terms, or HTTP data are used by the checker. At the default depth:

- 252 normalized moment/source term equalities across 16 entries, plus 36 displayed A187756 weight values
- All generated moments through n=256 for the principal and auxiliary laws, plus A338634 through 256
- Independent first-return recursion, formal nested S-fraction expansion, and time/height walk DP agree through n=24 for every moment weight law
- Exact scaling A261000(n)=3^n A144853(n) through n=256
- Occupation sums, primitive negative-excursion deletion identities, finite spectral chord inequalities, and primitive-path/shift identities for 11 different positive laws through n=9
- 27,448 condition-on-the-middle-vertex pair checks through n=7, for four laws and two cutoffs, including UU, DD, UD at height zero, and the UD/DU two-choice case
- Positive signed-Dixon ODE versus weighted Dyck coefficients through n=48, with coefficient sparsity checked through Taylor degree 145
- Gaussian moments and seven rational secant-power parameters through n=24
- Exact rational finite rising-factorial product identities, conjugate complex product identities, half-integer Gamma reductions, and the cubic amplitude/exponential monomial algebra

For the occupation identity, N_h counts descents across edge h. If T_n(h) is its weighted total and M_n^{<h} is the moment restricted to maximum height below h, the tested identity is

    T_n(h)-M_n+M_n^{<h}
      = sum_{k=1}^{n-h} e_{h,k}(T_{n-k}(h)+T_{n-k}(h+1)),

where e_{h,k} is computed independently by a confined walk beginning with a descent from h and returning to h only on its final ascent. The first-return implementation differentiates with respect to log weights; it does not enumerate the same identity on both sides.

The exact two-step identity is checked by exhaustive path grouping. For an even starting height k>0 and equal endpoints, its mean is

    [lambda_k w_k-lambda_(k+1) w_(k+1)]/[lambda_k+lambda_(k+1)].

No independence between step pairs is assumed.

### Dixon normalization

The positive system used is s'=c^2, c'=s^2, s(0)=0, c(0)=1. The generated moments obey

    M_n(d) = (3n+1)! [z^(3n+1)] s(z),
    d_(2j-1)=(3j-2)(3j-1)^2,
    d_(2j)=(3j)^2(3j+1).

These alternating weights are distinct from the A218221 polynomial weights. The primary continued-fraction and signed-function sources are Conrad–Flajolet, [The Fermat cubic, elliptic functions, continued fractions, and a combinatorial excursion](https://arxiv.org/abs/math/0507268), and Flajolet–Gabarro–Pekari, [Analytic Urns](https://arxiv.org/abs/math/0407098). The optional pole diagnostic uses all three nearest poles through 3(3n+1)!/rho^(3n+2), where rho=B(1/3,1/3)/3. Finite agreement does not itself prove that pole theorem.

## Numerical diagnostics, kept separate

`numerical_diagnostics.json` is optional and always labeled `DIAGNOSTICS_ONLY`. It contains:

- Relative-amplitude ratios for the principal cubic and quartic applications
- General-power one-shift tests at p=1/2,1,2,3,4 and alpha=-1/2,1,2, including harmonic-statistic errors
- Ratios to the posted pure-power absolute prefactor formula at p=1,2,3,4
- Mean/standard-deviation profiles at three macroscopic times versus the implicit limiting arch; the discrete bridge marginals are exact integers/rationals before numerical conversion
- Positive real polynomials with complex roots, a repeated negative nonintegral shift, and two distinct negative nonintegral shifts
- Finite Gamma-product and Dixon-product convergence diagnostics
- Dixon three-pole ratios and special-function normalization identities
- Lambert-W inverse centers, compared with exact first inclusive crossings for equality, just-above, and interior thresholds
- A338634/A227887 ratio diagnostics

The polynomial examples are h^2+1, h^2(h-3/2)^2, and (h-6/5)(h-9/5). All are positive at every positive integer: the complex pair gives h^2+1>0; the square has no integer root; and the last two factors are both negative at h=1 and both positive for h>=2. Their Gamma products must be treated as products; individual Gamma factors may be negative. No positivity condition on each individual linear factor is imposed.

The general-power *absolute* formula was posted by Vaclav Kotesovec in the comments of [A216966](https://oeis.org/A216966) on September 24, 2020. The article derives that formula for every fixed p>0 using its endpoint-occupation estimate and the published Freud leading-coefficient theorem. A separate standalone `freud_check.py` companion covers the finite comparison identities and diagnostics described below. The finite computations are consistency checks, not the article's proof or evidence of novelty.

The original checker's generic inverse diagnostic does not promote ceil(xi) to an unconditional answer. The generic theorem's radius is an unspecified o(1/log t); it provides no computable finite cutoff or radius from a leading equivalent alone. The separate pure-power Freud result gives an O_p((log t)^(-3)) radius only for unscaled h^p weights, still with unspecified p-dependent constants and onset; its companion likewise supplies no finite asymptotic certificate. Here the first crossing is certified separately by exact comparison against all earlier generated integers. At a threshold M_n+1, finite-precision log interpolation can round to the integer n; the exact crossing remains n+1. This is deliberately recorded rather than hidden.

## Output inventory

- `check.py`: self-contained implementation and CLI
- `data/oeis_displayed_terms.json`: displayed source-term fixtures
- `generated/exact_checks.json`: exact check scope, counts, and Dixon coefficients
- `generated/moments.json`: all 16 normalized arrays n=0..256; 15 moment laws plus the A338634 transform
- `generated/numerical_diagnostics.json`: optional, separately labeled diagnostics
- `generated/manifest.json`: hashes for this generation
- `REPRODUCTION_RECEIPT.json`: normal/optimized deterministic replay and clean-package results

All these files may be moved together to a different directory. Source metadata is provenance for the inspected term fields, not a claim that OEIS will never revise those entries.

## Standalone Freud comparison companion

`freud_check.py` is a separate portable program for the article's absolute pure-power result. It does not import the original checker, use its OEIS fixture, or download a paper. Its default exact arithmetic needs only Python's standard library; `--diagnostics` additionally uses mpmath 1.3.0. From this directory, choose outside output directories when replaying an immutable release:

```sh
python -S freud_check.py --out ../../freud-exact
python freud_check.py --diagnostics --out ../../freud-normal
python -O freud_check.py --diagnostics --out ../../freud-optimized
cmp ../../freud-normal/exact_checks.json ../../freud-optimized/exact_checks.json
cmp ../../freud-normal/numerical_diagnostics.json ../../freud-optimized/numerical_diagnostics.json
cmp ../../freud-normal/manifest.json ../../freud-optimized/manifest.json
```

Defaults are `--max-n 256`, `--norm-degree 16`, and `--dps 65`. Valid ranges are max-n 48..512, norm-degree 8..24, and dps at least 45. The exact output is independent of dps. The script disables local bytecode generation before imports, uses explicit exceptions, contains no removable assertions, and stores no timestamp, local filesystem path, or machine-specific Python executable in its output. Normal, optimized, relocated, and no-site-packages exact runs are recorded separately in `FREUD_REPRODUCTION_RECEIPT.json`.

### Exact convention and finite scope

For each integer p=1,...,6, start with the probability density

    exp(-|x|^(2/p)) / [p Gamma(p/2)].

Its odd moments vanish; its even moments are exactly Gamma(pn+p/2)/Gamma(p/2). If this unscaled variable is U, the article's comparison variable is Y=2U/A, which multiplies the even moments by (4/A^2)^n. For these integer p, the ratio is a rational rising product, including the half-integer cases. Rational LDL^T factorization of the Hankel moment matrix supplies the monic squared norms q_h and positive recurrence weights q_h/q_(h-1). A separately constructed formal S-fraction recovers the same Gamma moments. These are finite algebraic checks on a specified measure; they do not assume determinacy of its moment problem.

At the default depth, `freud_generated/exact_checks.json` records 760 finite instances:

- 102 Gamma-moment/S-fraction equalities through degree 16 for p=1,...,6
- 96 norm telescoping and 96 factorial-normalized telescoping identities
- 16 Gaussian comparison-recurrence coefficients
- 54 rescaled norm and 54 rescaled moment identities for p=1,3,6, using rational squared-coordinate scales 4/9 and 9/4 through degree 8
- 156 positive Hankel pivots across the original and rescaled matrices
- 85 pure-power walk/S-fraction values and 34 Gaussian/secant coefficient benchmarks through n=16
- 60 exact inclusive thresholds, for p=1,2,3,4,6 at base indices 16,32,64,128 and equality, just-above, and midpoint thresholds
- Seven exact symbolic constant/correction-algebra checks

The positive pure-power integer moment sequences used for crossings are generated through n=256; the output records each array's SHA-256 and every tested threshold. The constant algebra uses rational affine-in-p exponent vectors for 2, pi, p, I_p, and Gamma(p/2). It verifies C_nu/P=c_p and 4p^p/A^2=d_p, the signed telescoping 1/N coefficient (p−1)/12, and four smooth recurrence-series coefficients. It does not turn the unknown remainder into a differentiable function.

### Mathematical scope of the added result

For the article's comparison measure, A=(p I_p)^(p/2), H0=p Gamma(p/2)/A, and Y=2X after probability normalization. Thus

    nu_n=(4/A^2)^n Gamma(pn+p/2)/Gamma(p/2),
    P=pi/[H0(2pi)^(p/2)],
    c_p=sqrt(2p/pi) I_p^(-p/2),   d_p=4/I_p^p.

The article's proof uses the published Freud leading-coefficient theorem, explicitly restated in Claeys–Krasovsky–Minakov, section 2, equation (2.3), together with the endpoint-occupation estimate. Its attribution to Kriecherbauer–McLaughlin Theorem 1.5 is through that inspected restatement; direct access to the original 1999 full text is not claimed. See the article's bibliography for the source/version details.

For every fixed p>0, this gives the absolute formula and a relative O_p((log n)^(-2)) remainder. The constants and onset may depend on p and are not made effective. It gives no uniformity as p varies and no polynomial-rate bound. The improved O_p((log t)^(-3)) inverse radius applies here to unscaled pure h^p weights only. Broader perturbed and polynomial families retain the article's generic finite-prefix safeguard and qualitative o(1/log t) inverse statement. Neither result authorizes an unconditional single ceiling.

### Optional numerical scope

`freud_generated/numerical_diagnostics.json` is marked `DIAGNOSTICS_ONLY`. At the defaults it contains:

- 40 pure-power ratios for p=1/4,1/2,1,3/2,2,3,4,6 at n=16,32,64,128,256, with log²n-scaled relative and logarithmic errors
- Eight numerical constant-normalization records and eight explicit Gamma-moment Stirling ratios at n=1000
- 18 exact-norm-product evaluations, converted numerically at degrees 4,8,16, including the signed 1/N correction
- 25 two-step numerical walk comparisons with independently computed exact integer walks
- 60 pure integer-power inverse centers and log³t-scaled interpolation errors, paired with the exact inclusive first crossings stored by the exact suite

The noninteger-power moments are high-precision numerical values. Integer-power inverse crossings use exact integer comparisons against every earlier value. Finite-precision logarithms can still round adjacent enormous integer thresholds to the same display; that does not change the separately computed exact crossing. No displayed error is an interval enclosure, proof of convergence, certified finite onset, fitted bound constant, or computable asymptotic radius.

Additional output files are `freud_generated/exact_checks.json`, `freud_generated/numerical_diagnostics.json`, `freud_generated/manifest.json`, and `FREUD_REPRODUCTION_RECEIPT.json`.

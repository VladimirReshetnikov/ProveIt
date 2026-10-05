# Reader-facing exact validation for report 116

## What this directory does

`validate.py` uses Python 3.10 or later and the standard library only. All arithmetic in the mathematical checks is integer or `fractions.Fraction` arithmetic. It uses no floating-point arithmetic, numerical quadrature, symbolic-algebra package, network connection, or files outside this package. All guards raise explicit exceptions and remain active under `python -O`.

The checker's scope is finite enumeration, exact coefficient and exponent algebra, and rigorous rational numerical enclosures with an explicitly imported tail theorem. The proofs of the leading equivalents and the inverse conclusions are in the article. A passing finite test does not prove the survival theorem, conditional weak convergence, local central limit theorem, successive smoothing limits, asymptotic convolution, or eventual threshold claims.

The amplitude A is not numerically evaluated. In particular, evaluating the universal marginal factor alone would not evaluate the discrete harmonic value in A. No convergence rate or higher-order counting correction is certified.

## Files and commands

- `fixtures.json`: strict, versioned finite sequences, rational constants, fixed ranges, source URLs, and limitations
- `validate.py`: independent exact arithmetic and enumeration checks
- `results.json`: deterministic, complete recorded output of the checker
- `mutation_campaign.py`: named source/schema mutations plus clean fresh-directory replay
- `mutation_results.json`: actual rejection diagnostics, normal/optimized runs, and before/after SHA-256 hashes
- `reader_validation.md`: this explanation

From the package root:

```text
python3 checks/validate.py
python3 -O checks/validate.py
python3 checks/mutation_campaign.py
python3 -O checks/mutation_campaign.py
python3 replay.py
```

The two mathematical commands emit JSON to standard output. Their optional `--output PATH` writes the same bytes to a selected path; do not use it on archived outputs if preserving the sealed package. The validator also accepts `--only schema`, `counts`, `algebra`, or `certificates`, and `--fixtures PATH`. Full package replay compares regenerated outputs byte for byte with the archived files. The outer package's manifest and rebuild checks are separate from this directory's mathematical tests.

## Exact count and formal-series checks

The C and D reference vectors, for 0 through 38, are copied from report 114's exact enumeration output. The prior output's SHA-256 is recorded in the fixture as provenance; replay does not require or fetch that earlier report. The current validator independently recomputes every entry using two separate implementations:

1. A nondecreasing half-score dynamic program testing Landau excesses
2. An integrated velocity/area dynamic program with the correct parity-dependent terminal velocity and the untested final slack step

These calculations agree with each other and with both frozen vectors. C_0=D_0=1 are formal empty terms; D_1=1 and D_2=0 are retained exactly.

Ordinary S and T counts are independently enumerated for 0 through 19 by a full-score Landau dynamic program, with weak or strict proper-prefix inequalities respectively. The code computes N by the totient/binomial divisor formula, and compares all five vectors with their fixtures. It verifies coefficient by coefficient, over the available ranges:

- S=1/(1-T), with S_0=1 and T_0=0
- n S_n=sum_{j=1}^n N_j S_{n-j}
- C(z)=D(z)S(z^2)
- D(z)=C(z)(1-T(z^2))

For N_1 through N_8 an additional independent enumeration counts n-element subsets of {1,...,2n-1} whose sum is divisible by n, checking the EGZ interpretation. Finite inverse tests cover thresholds immediately below, at, and immediately above available count values. These verify the minimum-index definition and strong/all order on this finite data, not an asymptotic threshold formula.

## Gaussian, smoothing, and amplitude algebra

An exact multivariate Laurent-polynomial engine checks the completed square for both signs of the terminal velocity in the Gaussian kernel. In particular, integration over the starting area has marginal factor `(2*pi*t)^(-1/2)`, and the log density ratio is `12*x*w/t^2-4*y*w/t`.

The following powers and factors are checked independently as rational identities:

- The dominating s power is 3/4; both endpoint singularities of the dominating beta integral have powers greater than -1
- The geometric-minus-one increment has mean zero and variance 2, with lattice span one
- Gaussian smoothing contributes alpha^(-3/4)
- The bad-event bound has powers epsilon^(5/2) delta^(-2) n^(-1/2)
- Multiplication by survival and the n^(3/4) normalization cancels the n power exactly
- The half-length conversion contributes 2^(3/4); dividing by sigma=sqrt(2) leaves 2^(1/4)
- The far convolution tail has power n^(-3/2)
- Every finite geometric slack partial sum plus its exact tail equals one

Bridge split inequalities are checked for lengths 3 through 1000. Twelve exact rational parameter cases exercise the area-protection and endpoint-window bookkeeping. These are finite implementation checks; the article proves the uniform inequalities and limiting arguments, with n tending to infinity before epsilon tends to zero and then delta tends to zero.

## Universal marginal-factor expression

The article's expression

```text
f_Y(0) = 5 Gamma(7/4)^2 / (96 sqrt(2 pi))
         * 3F2(1,7/4,9/4;3/2,4;3/4)
```

is supported by exact prefactor, Pfaff-argument, gamma-recurrence, and coefficient checks. The code checks coefficients 0 through 64 against both a direct rising-factorial formula and the beta-integrated 2F1 recurrence. It also checks the polynomial identity

```text
(j+3/2)(j+4) - (j+7/4)(j+9/4) = (3/2)j + 33/16
```

which gives a positive consecutive-term ratio less than 3/4 for every nonnegative j. The integral transformations, interchange, and convergence justification are supplied analytically in the article. No exploratory decimal quadrature is included and no numerical value of A is claimed.

## Rigorous lambda and ratio certificate

The code computes all N_k through M=1669 exactly and forms the exact rational sum

```text
P_M = sum_{k=1}^M N_k / (k 4^k).
```

Its full numerator and denominator are recorded in `results.json`. A hash of the full N_0,...,N_1669 integer vector is also recorded with an explicit serialization rule. N_0=0 is only the vector's indexing placeholder.

The imported analytic input is Kolesnik, *The Asymptotic Number of Score Sequences*, Lemma 11, equation (17), applied at M=1669:

```text
(1-2/M)/(3 sqrt(pi) M^(3/2))
 <= sum_{k>M} N_k/(k 4^k)
 <= 1/(3 sqrt(pi) M^(3/2)).
```

Source: https://link.springer.com/article/10.1007/s00493-023-00037-4

That inequality is a cited theorem, not something finite enumeration establishes. Conditional on it, the remaining numerical certificate is exact and self-contained:

1. Alternating arctangent series at 1/5 and 1/239 bound pi using Machin's identity. The rational tangent identity is checked explicitly. The angle lies on the relevant branch, as described by the usual elementary identity `pi/4=4 atan(1/5)-atan(1/239)`
2. Integer-square-root calculations give rational bounds for sqrt(pi M^3), with their squares checked against the rational radicands
3. Positive arithmetic combines these bounds with P_M and the imported tail inequality
4. Alternating exponential series bound exp(-lambda) at the two lambda endpoints; monotonicity gives the interval for r
5. The positive atanh(1/3) series, with a geometric upper bound on its remaining tail, encloses log(2) and hence lambda/log(2)

All displayed decimal endpoints are rounded outward using integer division. No floating-point output is labeled certified. The resulting enclosures are:

```text
0.330237542043740119883454560545 <= lambda
                                     <= 0.330237545348903732852922336286

0.718752976724866638483058641951 <= exp(-lambda)
                                     <= 0.718752979100462827793445680518

0.476432064221864424618234874532 <= lambda/log(2)
                                     <= 0.476432068990207578375935213302
```

These imply Kolesnik's published `0.330237542 <= lambda <= 0.330237546` and the article's `0.7187529762 < exp(-lambda) < 0.7187529792`. They also certify `1/2<r<1` and `0<lambda/log(2)<1`, the numerical inequalities used in the analytic eventual-gap argument.

## Inverse and eventual-gap checks

The code checks the sign and scaling in the Lambert substitution `w=-(gamma/a)t`, where a=3/4 and gamma=log(2). It checks the formal cancellation for both the natural-log and base-two smooth-inverse expansions. It exercises the exact ceiling implications arising from

```text
m-1+e_(m-1) < q_E(X) <= m+e_m,
eta_E(X) = max(|e_(m-1)|, |e_m|).
```

This is consistent with the vanishing-width ceiling brackets in the article. It does not assert the false global statement `N_E(X)=q_E(X)+o(1)`.

The eventual integer gap is an analytic consequence of D_n<=C_n, the leading equivalents, and `D_(n+1)/C_n -> 2r>1`. At X=D_n the gap is eventually zero; at X=C_n it is eventually one. The finite tests certify the rational conditions on r and algebraic bookkeeping, not a computable index beyond which those asymptotic comparisons hold.

## Mutation tests, schema guards, and replay

The mutation campaign first parses the validator's Python syntax tree to exclude optimization-disabled `assert` guards. It copies clean inputs into a fresh temporary directory and reproduces `results.json` byte for byte in normal and optimized Python. Each named mutation then gets a separate fresh directory and must be rejected in both modes with exit code 2, empty standard output, and the specific expected `VALIDATION_FAILURE` diagnostic. A syntax error or unrelated crash does not count as success.

The 49 named mutations include terminal parity, an extra slack area test, the wrong integration velocity, strictness, divisor sign, formal convolution indices and signs, Gaussian completion and factors, bridge and area guards, smoothing/error/amplitude exponents, inverse signs and ceilings, hypergeometric coefficients, Machin and tail formulas, lambda normalization, exponential sign, reference counts, duplicate JSON keys, unknown keys, booleans masquerading as integers, floats, zero denominators, unreduced fractions, changed ranges or provenance, and deleted limitations. There are 98 required rejection runs.

`mutation_results.json` records the actual original and mutated validator/fixture hashes for every case, the expected and observed diagnostic, the optimization setting, and exit status. It also records actual clean input hashes before and after the full campaign, checks that they are unchanged, and records the fresh replay's output hash. Hashes establish reproducibility and integrity, not mathematical truth or authorship.

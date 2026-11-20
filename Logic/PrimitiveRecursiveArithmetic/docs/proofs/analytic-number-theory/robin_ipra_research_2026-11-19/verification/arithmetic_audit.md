# Independent arithmetic and finite-bridge audit

## Scope and result

The production file `code/robin_certificates.py` was independently read, its interval formulas were checked mathematically, and a separate exact-rational reference computation was executed. **No mathematical error was found in the interval enclosures or the finite least-common-multiple bridge.** This is a mathematical/code audit, not a Lean proof, an iPRA derivation, or a proof of Robin's equivalence.

The independent executable is `verification/independent_arithmetic_audit.py`; its saved results are `verification/independent_arithmetic_audit.json`. It uses only Python integers and `fractions.Fraction`. The production recurrence is dyadic and rounds every step, while the reference evaluates exact rational polynomials before applying smaller rational tail bounds. The checks therefore do not simply repeat the production interval recurrence.

Executed checks, all passing:

- 141 logarithm cases, with 80-term exact rational reference polynomials, including reciprocal arguments, values near 1, powers of two, 5041, and a large integer.
- Euler constant enclosure checked against an independent harmonic-sum reference at `m=8192` (production uses `m=2048`).
- 7 exponential interval cases, including point intervals at 0 and 1 and the full input interval `[0,1]`.
- 49 signed interval product cases, covering all sign configurations and zero endpoints.
- 19 composed Robin-bound cases, including `n=2`, both sides of 5040, 10080, 55440, 100000, and `10^30+1`.
- All 99,999 CSV divisor sums independently recomputed by prime factorization and multiplication of geometric sums, rather than the production divisor-addition sieve.
- All 99,999 CSV signs checked by exact integer comparison; the row count checked against both advertised count and final limit; the 27 recorded exceptional integers reproduced.

The independent comparison in the approximation cases is stronger than a decimal agreement check: each production interval contains the complete narrower rational reference enclosure.

## Mathematical enclosure review

### Directed rounding

For positive integer `b`, Python integer division `a//b` is floor even when `a` is negative. The implementation `-((-a)//b)` is ceiling. Thus the code's signed lower and upper rounding are correct.

### Logarithm series and tail

For `1 <= a/b <= 2`, set `z=(a-b)/(a+b)`, so `0 <= z <= 1/3`. The identity

    log(a/b) = 2 sum_{j>=0} z^(2j+1)/(2j+1)

has positive terms. With K terms, its tail is bounded by

    2 z^(2K+1)/((2K+1)(1-z^2))
    <= 9/(4(2K+1)3^(2K+1)).

Both the exponent `2K+1` and the constant `9/4` in the code are correct. The lower and upper dyadic power recurrences preserve their inequalities because all factors are nonnegative. The rounded power used for the finite upper sum can exceed the true power; this does not invalidate the separately added tail bound, which bounds the omitted terms for the true `z`.

Range reduction finds an integer e such that `1 <= a/(2^e b) < 2`, and adds `e log 2`. The bit-length difference with at most one downward adjustment has exactly that property. For `a<b`, the reciprocal identity reverses both interval endpoints, as required. No comparison of unknown real values is used.

### Euler constant enclosure

The enclosure direction is correct:

    A_m = H_m - log m - 1/(2m),
    A_m <= gamma <= A_m + 1/(12m^2).

Here is a direct justification that also exposes finite rational bounds. Put `z=1/(2m+1)`. Then

    A_(m+1)-A_m
      = 2z/(1-z^2) - 2 atanh(z)
      = 4 sum_{j>=0} (j+1)/(2j+3) z^(2j+3).

Every term is nonnegative. Since `2j+3>=3`, this difference is at most

    (4/3) z^3/(1-z^2)^2
      = 1/(12m^2) - 1/(12(m+1)^2).

Consequently `A_m` increases, while `A_m+1/(12m^2)` decreases. Their gap tends to zero with the explicit bound `1/(12m^2)`. For any finite `r>=m`, telescoping gives the corresponding finite bracket relation; positive series tails can be replaced throughout by their displayed rational remainder bounds. The common limit is gamma because `1/(2m)` tends to zero. This proof does not need a numerical value for gamma.

In the implementation, the harmonic lower sum rounds down and its upper sum rounds up; subtracting log reverses its endpoints; subtracting `1/(2m)` uses ceiling for the lower bound and floor for the upper bound. The positive correction `1/(12m^2)` is rounded upward. Each direction is correct.

### Exponential

For `0<=x<=1`, the omitted tail after terms 0 through K is at most `2/(K+1)!`: the first omitted term is at most `1/(K+1)!`, and every later ratio is at most `1/(K+2)<=1/2`. The production lower and upper recurrences respectively round down and up the positive Taylor terms. The advertised tail constant is therefore safe. `math.factorial` here is exact integer arithmetic.

### Signed multiplication and the case n=2

The extrema of the product over two closed real intervals occur among the four endpoint products. The code takes the minimum and maximum of all four products and rounds outward; it does not incorrectly assume that both factors are positive.

This is essential for `n=2`, where `log n` is positive but less than 1, hence `log log n` is negative. The logarithm-of-interval step is correct by monotonicity: apply the logarithm routine to the positive lower and upper bounds for `log n`, then keep respectively its lower and upper outputs. Negative values are handled by reciprocal logarithm and by signed four-corner multiplication. The independent exact reference check includes this case and passed.

### Acceptance comparisons

`robin_bound(n)` encloses `B(n)=exp(gamma) log log n`. The success test

    n*bound.lo > sigma[n]*S

implies `sigma(n)<n B(n)`. The failure test

    sigma[n]*S > n*bound.hi

implies the stronger strict reverse inequality, so it is valid evidence of failure of Robin's strict bound. A possible exact equality or inadequate interval precision yields `undetermined`, not a silently assigned sign.

The minimum recorded margin comparison uses cross multiplication of positive denominators and is correct. The independent arithmetic audit reproduced all divisor sums and signs in the advertised finite interval. No finite interval check proves the unbounded criterion.

## Replay robustness observation

The initially inspected production verifier compared its row count to `summary['integers_checked']`. I recommended also requiring this count to equal `summary['limit_inclusive']-1`, so an abbreviated CSV with an edited count cannot still advertise the original limit. The primary author added the assertion, and a final source check confirmed it is present. The current generated data satisfy both equations, and the independent verifier checks both. This was a completeness-hardening improvement, not a numerical defect in the delivered computation. No production code was changed by this auditor.

Final reviewed production SHA-256:
`76ea16e10cd3a72bc8ddb59e67caa1056d390702cda2dc49e27813bb40d21762`.

## Finite least-common-multiple bridge review

The separately prepared `lcm_bridge.tex` was read in full. The following points were checked:

1. The identity for `M(L_P)` has the correct signs: the prime-power truncation contributes `-T(P)`, while replacing `theta(P)` by `psi(P)` contributes `-D(P)`.
2. At `P=m^2`, only primes at most m contribute to `psi-theta`; the bound `m log P` is valid.
3. Under `theta(P)>=P/4`, the two elementary logarithm bounds give `D(P)<=8/m` for `m>=4`.
4. Splitting the prime-power truncation at m gives `T(P)<=2/m+2/m`. The second estimate uses the finite telescoping sum of `1/(j(j-1))`; no prime density estimate is hidden there.
5. The elementary Chebyshev lower bound is valid. Legendre's formula gives `binom(2h,h) | lcm(1,...,2h)`. The central binomial coefficient bound and `2/3<=log 2<=3/4` yield the stated constants. The polynomial identity `(m-16)(m+7)+78=m^2-9m-34` is correct and proves the final nonnegativity.
6. `lcm(1,...,16)=720720`, so the constructed integer exceeds 5040.
7. Passing from Q to `P=floor(sqrt(Q))^2` loses at most `4/m` in `log F`, with the correct inequality direction.
8. If the oscillation input is `-log F(Q)>=c Q^(-b)` and `delta=1/2-b>0`, the condition `c Q^delta>32` is sufficient. The proposed rational-code cutoff using `B>=max(2,64/c)` and integer `k>=1/delta` indeed implies it.

No defect was found in these finite arguments. Their conclusion is a conditional finite witness transformation. The bridge does not establish Nicolas/Landau oscillation in iPRA and correctly records that remaining obligation.

One wording qualification was communicated: a *supplied positive rational gap* lets a uniform primitive-recursive approximation schedule certify a strict input inequality. Mere strictness implies existence of some certificate under the usual constructive strict-order interpretation, but does not by itself provide a uniform primitive-recursive bound for finding its precision. These distinctions should remain explicit.

## Reproduction

From the package root:

```sh
python3 verification/independent_arithmetic_audit.py
```

This regenerates the small JSON audit record and reads the existing finite CSV. It does not modify the production code or the CSV.

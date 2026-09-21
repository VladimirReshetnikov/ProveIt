# Wolfram Language verification record

Date: September 21, 2026.
Execution service: the connected Wolfram Language evaluator.
Reported kernel: **15.0.1 for Linux x86 (64-bit) (July 2, 2026)**.

## What was executed

The arithmetic definitions corresponding to `code/RationalHahn.wl` and the
checks corresponding to `code/Checks.wl` were submitted as code to the
stateless Wolfram Language evaluator. The local package path itself was not
loaded into a separately installed kernel. The package distribution adds
normal context/usage-message wrapping and comments around the definitions.

These are exact finite algebra and formal-series checks. They are not a
formal verification of Hahn summability, surreal foundations, the effective
real-closure construction, global analytic structures, or infinite recursions.

## First evaluation

The initial suite reported **34 checks, 31 passed**.

All 22 rational-kernel checks passed:

1. Cancellation to exact one.
2. Multiplication by an inverse.
3. Addition followed by subtraction.
4. Sign with a negative denominator.
5. Comparison of the second scale against the 10000th power of the first.
6. Leading positive sign across those scales.
7. Quotient valuation.
8. Valuation after cancellation.
9. Distinguished valuation marker for zero.
10. Zero sign.
11. Zero standard part.
12. Rational finite standard part.
13. Standard part of a higher-rank infinitesimal quotient.
14. Rejection of standard part for an infinite element.
15. Rejection of the inverse of zero.
16. Rejection of a zero denominator.
17. Rejection of an inexact coefficient.
18. Rejection of a transcendental coefficient outside the declared Q-domain.
19. Rejection of a nonpolynomial numerator.
20. Rejection of mismatched monomial domains.
21. Rejection of duplicate variables.
22. Rejection of an empty variable list.

Nine additional checks passed on this first evaluation:

- Geometric reciprocal coefficients.
- Positive square-root coefficients.
- Finite-center sine coefficients.
- Inverse-tangent coefficients.
- Each of the two ramified quadratic roots.
- Infinite-residue cancellation coefficients.
- Implicit inverse-sine coefficients.
- The two different formal derivative conventions.

Three initial checks did not simplify to True:

- The inverse-cosine endpoint expansion used `ArcCos[1-u^2]` without first
  making the positive square-root uniformizer explicit.
- The Cayley identity used `Cancel` alone on a sum of rational terms.
- The trigonometric algebraization identity likewise used `Cancel` alone.

The initial connector evaluation also emitted warnings about global-symbol
preprocessing and messages generated during the inverse-cosine series request.
No claim of a warning-free initial evaluation is made.

## Corrective evaluation

The corrected endpoint coefficient calculation uses

    2 ArcSin[u/Sqrt[2]]/(Sqrt[2] u)

as the analytic factor in the positive uniformizer u. The other two checks
use `Together` to combine denominators. A subsequent evaluator call reported:

    InverseCosineUniformizer -> True
    CayleyUnitCircle -> True
    TrigAlgebraization -> True

Thus every check in the distributed suite has an individually successful
corresponding evaluation after these test-expression corrections. This is not
reported as one original 34/34 run.

An additional request to simplify

    ArcCos[1-u^2] == 2 ArcSin[u/Sqrt[2]],  0 < u < 1

remained unevaluated. It is not counted as a passed computer check. The
positive-branch identity is justified by the ordinary half-angle identity and
inverse-function ranges, as in the supplied trigonometry manuscript and the
article's discussion. A failure to simplify it is not evidence against that
mathematical proof.

## Reproducing the corrected suite

From the extracted archive, evaluate:

    Get["code/RunChecks.wl"]

or run:

    wolframscript -file code/RunChecks.wl

A successful corrected run should produce `Checks -> 34`, `Passed -> 34`,
and an empty `Failures` list. This is an expected reproducibility result,
not a claim that a local installation was exercised in this environment.

The `Checks.wl` file uses named global variables for readability. Run it in a
fresh kernel or a disposable context. The package rejects variables that have
already evaluated to nonsymbolic values.

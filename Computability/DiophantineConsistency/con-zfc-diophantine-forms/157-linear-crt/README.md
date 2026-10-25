# Linear CRT radii and semantic radix recovery

An explicit Diophantine consistency construction prepared for Vladimir
Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Start with **report/report.pdf**. **report/report.tex** is a standalone
LaTeX source, including all 174 quadratic residuals of the principal equation.

## Result

Every displayed variable ranges over the unrestricted integers. The main
polynomial is exactly the sum of the squares of the residuals in
equations/P238/equation.json:

    P238(x0,...,x237) = R0^2 + ... + R173^2.

The new ordinary mathematical proof, composed with the identified inherited
numerical-calculus calibration, establishes

    ZFC proves:
    [there is no x in Z^238 such that P238(x)=0] iff Con(ZFC).

The two companions have the same consistency interpretation.

| Profile | Integer variables | Quadratic rows | Degree | Collected monomials | Height |
|---|---:|---:|---:|---:|---:|
| P238 | 238 | 174 | 4 | 13,149 | 6,144 |
| P239_sparse | 239 | 175 | 4 | 4,963 | 7,968 |
| P239_low_height | 239 | 175 | 4 | 6,723 | 4,432 |

Every residual coefficient has absolute value at most 64. All coordinates
occur in the collected polynomial. Each directory supplies every collected
coefficient, the exact metrics, and a polynomial restoration certificate.
There are no variable-exponent operations, unspecified coefficients, or
universal-polynomial parameters in the literal final data.

P238 improves the inspected incoming Shared Factorial Error 240-variable
direct quartic by two variables, three rows and 8,333 monomials, preserving
height 6,144. P239_low_height improves all four corresponding size measures.
These comparisons concern the direct small-coefficient quartic lineage.
Other repository constructions have fewer variables with different degree
or coefficient architectures; no global minimum is claimed.

## New arithmetic

The semantic choices are

    t = 16 + 4h^2,  F = t^t,  R = F,  C = 2c,
    H = 2 + 4(C + A1 + ... + A8),  y = F(2v+1).

The existing power graphs certify all displayed powers. The final equation
itself uses only addition, subtraction, multiplication and fixed integers.

Three coordinated simplifications remove the squared CRT radius, the
private square restriction on the radix, and the square wire for the beta
multiplier. The essential proofs are:

1. Positive coefficient lists distinguish bounded label multisets already
   at F=t^t, including the boundary case with t nonunit factors.
2. lcm(1,...,t) <= 4^(t-1) makes F itself a sufficient binomial CRT radius.
3. The even C chart forces B nonzero before signs. H is 2 modulo 4 for
   every signed tuple, so its product with B cannot be a unit. This recovers
   the exponent and radix, then the existing q^(y+1) request forces y positive.
   Representative signs and the signed binomial digit are recovered afterward.

The report and proofs/MAIN_PROOF.md give the soundness and constructive
completeness arguments. The exceptional boundary y=F is excluded explicitly
after row decoding.

## Reproduce

Python 3.10 or newer, standard library only:

    python3 -B verify.py
    python3 -B verify.py --rebuild
    python3 -B -O verify.py

The independent checker imports no producer or optimizer. It verifies the
source delta, all 18 power requests, frame coverage, Horn factoring, 202
monic eliminations, 117 unused-slot deletions, 69 translations, every final
affine and row transformation, full coefficient expansions, liveness, and
the measured comparison polynomials. It also rejects targeted corruptions.
The rebuild reconstructs 19 mathematical files byte for byte in a temporary
directory. No root search or consistency decision is performed.

To save a new receipt outside this sealed release:

    python3 -B verify.py --rebuild --receipt ../my_check.json

To evaluate a supplied JSON list of exactly 238 integers:

    python3 -B evaluate.py point.json

Use --profile P239_sparse or --profile P239_low_height with a 239-integer
tuple for a companion.

To rebuild the article with a standard pdfLaTeX installation:

    python3 -B build_report.py

The builder parses the printed residuals back into polynomials and rejects
unresolved references or overfull boxes. Different TeX installations can
change PDF bytes. After an intentional rebuild or edit, use
verify.py --skip-manifest to check mathematical content without requiring
the original file hashes.

## Scope

The proof uses the named inherited interfaces
KEndpoint.c222_iff_zf_refutation and
ConstructibleChoice.zf_refutation_iff_zfc_refutation, together with the
retained signed Pell/frame compiler. This is an ordinary proof formalizable
in ZFC, with exact finite algebra audits. It is not a newly compiled
end-to-end Lean/Rocq development, an encoded object-ZFC proof string, or
a proof of Con(ZFC).

The direct construction does not simulate K215 or instantiate Jones's
universal polynomial. The source calibration is inherited and identified,
not asserted to have been independently rebuilt here.

## Provenance

Comparison commit:

    7a8da414376a80b90ecf799f37ceb26fb9ac674e

SOURCE_LEDGER.json pins all seven incoming ZIPs inspected at that snapshot.
The immediate factorial-free source is retained with its original notices.
NOTICE.md records attribution, and INTEGRATION.md describes placement.
Independent reviews here mean separately conducted checks within the
AI-assisted workflow, not outside human refereeing.

# Derivative Supports of x^(x^a)

For every fixed positive integer a, the number A_a(N) of nonzero monomials in the Nth derivative of x^(x^a) satisfies

A_a(N) = N^2/2 + o_a(N^2).

The ten-page report gives a self-contained proof. It includes the exact coefficient and tanh transformations, strict positivity of the nonnegative power columns, global angular selection for every integer exponent, complete contour coverage by joined convex envelopes, the real/complex parameter regions, an elementary nonzero-curvature anchor, the integer-triangle estimate, and full tail exhaustion.

It also proves two exact results:

- All negative-column coefficients at depths one and two vanish only at the specified reflection cells, with explicit signs elsewhere
- For every transcendental real exponent, and more generally outside a countable algebraic exceptional set, the exact derivative count is N(N+3)/2 for every N>=1

The asymptotic constants and thresholds may depend on the fixed integer exponent. The result does not address exponents growing with N or classify every deeper cancellation at an exceptional algebraic parameter.

## Contents

- `article.pdf`: complete report
- `article.tex`: complete LaTeX source
- `build_local.sh`: build helper for the supplied execution environment
- `verify_general_coefficients.py`: exact, standard-library verification script
- `general_coefficient_checks.json`: recorded results

## Verification

Run `python verify_general_coefficients.py`. It checks 631 exact coefficient identities for exponents 1 through 8, including 104 zero cases, 187 positive-bulk cases and 252 depth-one/two sign cases. These finite checks supplement the proof and do not establish an all-depth exact zero classification.

Compile `article.tex` twice using a normal LaTeX installation, or use `bash build_local.sh` in the supplied environment.

The proof received independent mathematical and final-transcription review; all rendered pages were inspected. It is a conventional analytic proof, not a proof-assistant formalization or an externally refereed publication.

## Source comparison

Question 8 of ProveIt's `power-tower-derivative-term-counts/article.tex` explicitly asks for the x^(x^r), r>=3 extension and for rederivation of its depth generating function and symmetry center. The current source was rechecked on 1 October 2026 at 09:14 UTC: default-branch head 7421a4ca60fdf125411edf412f825aac54278b37; latest commit touching that article ca81647a9f679e96d49ffdbc54b0c0ab13d10a36. The question remained present. The paper retains this pinned, source-relative comparison and makes no exhaustive worldwide priority claim.

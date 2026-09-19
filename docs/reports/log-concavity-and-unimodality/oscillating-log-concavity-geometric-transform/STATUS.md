# Source and claim audit

Audit date: 19 September 2026.

## Exact target

Bernhard Heim and Markus Neuhauser, *Log-Concavity of Infinite Product and
Infinite Sum Generating Functions*, arXiv:2302.13327v1, 26 February 2023.

- Abstract/history: https://arxiv.org/abs/2302.13327
- Full HTML: https://arxiv.org/html/2302.13327v1
- PDF: https://arxiv.org/pdf/2302.13327

Section 3, printed page 10, was checked in both extracted text and a PDF
page image. Challenge 2 asks for infinitely many exceptions and
non-exceptions for the geometric transform of `n^2`. Challenge 3 asks for
infinitely many exceptions for each nonnegative integer divisor exponent.
The article's challenge numbers refer to this exact version.

The abstract page inspected listed only v1. Publisher metadata identified
DOI https://doi.org/10.1142/S1793042124500192 and publication in the
International Journal of Number Theory. The publisher revised full text
could not be inspected directly; no claim is made about textual identity
between that revision and the arXiv version.

## Known sequence and parameterized framework

https://oeis.org/A033453 was inspected. It already records the INVERT
transform of squares, its colored-composition interpretation, rational
generating function `(1+z)/(1-4z+2z^2-z^3)`, and recurrence `(4,-2,1)`.
Its index zero corresponds to manuscript index one. The displayed entry
contained no sign-density or sharp four-index-block theorem.

Heim and Neuhauser, *Horizontal and vertical log-concavity* (2021),
https://doi.org/10.1007/s40993-021-00245-1, was inspected for the already
established positive-parameter geometric-transform framework.

## A recent related title checked

Alzer and Volkmer, *Inequalities for the Lambert series*, The Ramanujan
Journal 70, article 1 (2026), published 10 April 2026:
https://doi.org/10.1007/s11139-026-01365-x

Its principal log-concavity theorem concerns the function
`t -> L_0(1-exp(-t))`. This is not the coefficient sequence of
`1/(1-u L_s(z))` considered here.

## Search coverage and limitations

Targeted searches used the exact article title, arXiv identifier, author
names with geometric log-concavity, challenge wording, and A033453.
No prior resolution of the two stated questions was located. Some searches
returned irrelevant or incomplete results. Search absence is not proof of
priority, and the audit is not an exhaustive citation-network review.

## Claims made by the manuscript

The general pole criterion, divisor-family application, integer-power
classification, and square-case statements are supplied with full arguments.
The square case includes a determinant recurrence, exact nonvanishing,
the optimal four-index block bound, and half-density in every progression.
The manuscript does not claim that the underlying analytic and algebraic
tools or the recorded OEIS coefficient recurrence are new.

No result is asserted for the separate exponential/product Challenge 1.
No universal exact parity pattern is asserted for the divisor families.
No uniform-in-parameter gap bound or general half-density theorem is asserted.
The square sign theorem concerns adjacent determinants, not the positive
coefficients themselves.

## Review status

Developed in this ChatGPT session and checked by conventional mathematical
reasoning plus exact finite computation. Not independently peer reviewed
and not formally checked in Lean or another proof assistant. Numerical root
approximations are illustrative and are not premises in the proofs.

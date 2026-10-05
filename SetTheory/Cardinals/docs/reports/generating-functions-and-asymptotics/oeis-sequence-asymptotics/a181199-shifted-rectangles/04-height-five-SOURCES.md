# Source and attribution record

1. Manuel Kauers and Christoph Koutschan, *Some D-Finite and Some Possibly
   D-Finite Sequences in the OEIS*, arXiv:2303.02793v2, Section 6.4,
   Conjecture 19, printed page 34. Versioned public source:
   https://arxiv.org/pdf/2303.02793v2
2. OEIS A181199, internal entry, consulted October 5, 2026:
   https://oeis.org/A181199/internal
   The operator in `code/printed_coefficients.py` is a literal transcription of
   the displayed order-three recurrence, independently compared with the
   nested-sum factorization. Each of its four coefficients has degree 24.
3. The earlier fixed-height manuscript in repository
   `report a181199-shifted-rectangles`, pinned to
   Git blob `2b40ded9daa6549f786a52b880d5477de3b5adfc`, supplied prior fixed-height
   asymptotic context. Verified repository source:
   https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a181199-shifted-rectangles/article.tex
   Its leading asymptotics and all-order expansion results
   are credited in the article; the present work addresses the separate exact
   finite-count conjecture. That earlier manuscript is not redistributed here.

4. NIST Digital Library of Mathematical Functions, Section 5.11, especially
   equation 5.11.1 and the positive-real remainder discussion in Section 5.11(ii):
   https://dlmf.nist.gov/5.11
   https://dlmf.nist.gov/5.11.E1
   https://dlmf.nist.gov/5.11.ii
5. NIST Digital Library of Mathematical Functions, Section 4.13, definition and
   real branches of the Lambert W function:
   https://dlmf.nist.gov/4.13

The rising-factorial bars over the exponents 3 and 4 in the denominator of
Conjecture 19's u(k) are mathematically essential. They were checked against the
printed page. They must not be replaced by ordinary powers after PDF extraction.
The second printed degree-eight denominator polynomial is exactly P(k+1).

The package redistributes no third-party paper, source PDF, source screenshots,
or private review reports. Public source links above identify the mathematical
claims being proved and compared. The program uses no downloaded material at
runtime. Source consultation is bounded; no claim to a complete priority search
or historical novelty certification is made.

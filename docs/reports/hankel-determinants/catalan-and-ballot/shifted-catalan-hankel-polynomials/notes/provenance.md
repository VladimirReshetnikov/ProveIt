# Source and status audit

Checked: 19 September 2026.

## Target, with an exact version

Paul Barry, *Notes on the Hankel transform of linear combinations of
consecutive pairs of Catalan numbers*, arXiv:2011.10827v1, 21 November 2020,
29 pages.

- Record: https://arxiv.org/abs/2011.10827
- Versioned HTML: https://arxiv.org/html/2011.10827v1
- PDF: https://arxiv.org/pdf/2011.10827

Page 4 contains the denominator-exponent conjecture and the separate
Conjecture 2. Both HTML and the rendered original PDF page were inspected.
The coefficient-index discrepancy is present in the PDF, not just in its
experimental HTML representation. The target record inspected lists v1.

**Translation:** the source's determinant size is n+1; our size is N.
The source coefficient parameter s corresponds to our actual shift m=s-1.
The one-by-one case s=2 produces a+2b from the printed coefficient formula,
whereas the literally stated shift-2 determinant is 2a+5b. Appendix A proves
the corrected correspondence for all N>=1, s>=2, and 0<=k<=N.

## Known foundations deliberately not claimed as new

Christian Krattenthaler, *Hankel determinants of linear combinations of
moments of orthogonal polynomials, II*, The Ramanujan Journal 61 (2023),
597–627, online 22 November 2021.

https://doi.org/10.1007/s11139-021-00514-8

Its fixed-size Christoffel determinant, confluence discussion, and Section
8 establish a substantial existing framework. Section 8 credits Elouafi's
2015 proof of the earlier general recurrence conjecture. Our article does
not claim rationality alone, the Christoffel identity, or general
constant-coefficient recurrence theory as a discovery. It gives a direct
specialized proof of the sharp exponent, noncancellation, and exceptions
for the multiplier x^m(a+bx).

Michael Dougherty, Christopher French, Benjamin Saderholm, Wenyang Qian,
*Hankel Transforms of Linear Combinations of Catalan Numbers*, Journal of
Integer Sequences 14 (2011), Article 11.5.1.

https://cs.uwaterloo.ca/journals/JIS/VOL14/French/french2.html

NIST DLMF, Jacobi hypergeometric representation, equation 18.5.7:
https://dlmf.nist.gov/18.5.E7

The article reproves the needed orthogonality and determinant identities
so that the mathematics can be checked without trusting a normalization
in a secondary citation.

## OEIS connections

- Catalan numbers: https://oeis.org/A000108
- Odd-index Fibonacci subsequence: https://oeis.org/A001519
- Even-index Fibonacci subsequence: https://oeis.org/A001906
- Related shifted-Catalan determinant triangle, linking the target paper:
  https://oeis.org/A123352

The package does not claim a new OEIS entry or an exhaustive identification
of all specialization rows.

## Search scope and limitations

Searches included the exact arXiv identifier and paper title, the phrase
"central polygonal numbers" with Catalan/Hankel, and combinations of Barry,
Hankel determinants, denominator exponents, proof, and recurrence. The
search surfaced the target itself, its OEIS links, and the established
general theory above. The retrieved material did not give an explicit
statement of the full sharp classification proved here.

Related search hits were distinguished rather than assumed to address the
same problem. For example, Allouche–Han–Shallit's *On some conjectures of
P. Barry* concerns a different 2020 source and the Rueppel sequence. The
2026 paper by Chern and Shi on Catalan-like determinants concerns a
different family of Motzkin-meander moment sequences. Neither was used as
support for novelty of the present theorem.

This bounded search is not a proof of global open status. An equivalent
formula may occur elsewhere under Jacobi-polynomial, Christoffel-transform,
or determinant terminology. The mathematical results should be described
as a proof and strengthening of the conjecture in the specified source,
with an explicit correction to its separate coefficient statement, not
as a certified first-ever solution of a globally unresolved problem.

No authors were contacted, no result was submitted to OEIS or a journal,
and no external peer review or Lean formalization was performed.

# Source references and access record

Consulted 3 October 2026. The source paper PDFs are not redistributed in this package. All mathematical proofs in Report172 are self-contained except for explicitly credited standard algebraic and zeta-function facts; the classical theorem discussion is an attribution and applicability check.

1. OEIS A397045, https://oeis.org/A397045
   Shell definition, index origin 1, 35 displayed positive-index terms, and conjecture dated 15 June 2026. The current page was opened again during report preparation. Its cached metadata does not certify the latest uncached revision. The linked n=1..75 b-file was not successfully retrieved during source gathering; no claim is made about exact data beyond n=35. The cumulative comment's wording with all integer radicands k>1 is incorrect because sqrt(4)=2; the correct alternatives are nonsquare integers or squarefree d>=2, retaining the empty sum.

2. E. E. Kohlbecker, Weak asymptotic properties of partitions, Transactions of the American Mathematical Society 88 (1958), 346–365.
   https://doi.org/10.1090/S0002-9947-1958-0095808-9
   Main Theorem and Corollary 1, pp. 362–363; introduction and relevant surrounding theorem material. Consulted through the scan transcription at https://studylib.net/doc/18218928/p--i--e-ii---- . Publisher PDF retrieval failed. Arbitrary positive real part sizes are explicitly permitted. The logarithmic theorem here is a specialization of this classical theory, not a new general result.

3. A. E. Ingham, A Tauberian theorem for partitions, Annals of Mathematics (2) 42 (1941), 1075–1090.
   https://doi.org/10.2307/1970462
   Original scan not retrieved. The general Laplace–Stieltjes theorem was consulted through the exact restatement in item 4. Report172 verifies the radial complex bound needed for its application.

4. K. Bringmann, C. Jennings-Shaffer and K. Mahlburg, On a Tauberian theorem of Ingham and Euler–Maclaurin summation.
   https://arxiv.org/abs/1910.03036v3
   https://doi.org/10.1007/s11139-020-00377-5
   Full PDF/text available; Section 4 and Theorem 4.1 consulted. Version 3 dated 24 November 2020. The abstract page was opened again during report preparation.

5. B. K. Agarwala and F. C. Auluck, Statistical mechanics and partitions into non-integral powers of integers, Proceedings of the Cambridge Philosophical Society 47 (1951), 207–216.
   https://doi.org/10.1017/S0305004100026505
   Scan accessed through https://oeis.org/A000093/a000093.pdf . Setup and formulas (26)–(28) consulted. The paper counts representations using integer radicands, not distinct represented real values. Its discussion does not establish the multiplying factor for nonintegral powers. Related representation sequence: https://oeis.org/A000333 .

6. A. Dong, N. Robles, A. Zaharescu and D. Zeindler, Exponential sums twisted by general arithmetic functions, arXiv:2412.20101v1, 28 December 2024.
   https://arxiv.org/abs/2412.20101v1
   Full PDF/text available; Section 6, especially Lemmas 6.2 and 6.8, consulted. The abstract page was opened again during report preparation. The integer-squarefree-part Mellin factor is Gamma(s) zeta(s+1) zeta(s)/zeta(2s). It is prior conceptual precedent for zeta-zero contributions in partition refinements, but the spectrum differs from the real squarefree-root spectrum in this report.

7. NIST Digital Library of Mathematical Functions, Section 25.10, Zeros of the Riemann zeta function.
   https://dlmf.nist.gov/25.10
   Opened during report preparation for standard zero existence and zero-free-boundary facts. The argument uses no numerical location or simplicity assumption.

## Exact fixture provenance

The 35 displayed OEIS terms were independently matched in a prior completed rational-enclosure run with denominator 2^48. It enumerated 428,363,342 vectors through n=35 and reported zero ambiguous boundaries. The package retains the resulting historical fixture. Default builds freshly verify n=0..20 with a separate arbitrary-integer Python implementation, direct shell enumeration through n=12, atomic endpoints, and a bounded C++ cross-check when the compiler is available. The optional n=35 compiled run is never executed implicitly.

## Limitations and priority

A bounded search did not identify an earlier treatment of the precise squarefree-root real spectrum with these quantitative statements. This is not an exhaustive novelty claim. The leading law and qualitative exact-saddle framework are classical. Neither external edits nor publication, repository changes, or author contact were made for this report.

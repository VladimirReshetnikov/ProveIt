# Sources and computational provenance

Report 175, 3 October 2026. This archive contains original report text and local verification code. It does not redistribute third-party papers, books, source code, or research working notes.

## Primary mathematical sources

- Donald E. Knuth, *Non-attacking Kings on a Chessboard*, February 1994 rough notes: https://www-cs-faculty.stanford.edu/~knuth/papers/nkc.tex . Subset/height states and monotone subset transitions are prior.
- Herbert S. Wilf, *The Problem of the Kings*, Electronic Journal of Combinatorics 2 (1995), R3: https://doi.org/10.37236/1197 . The binary-word triangular transfer and positive linear dominant asymptotic are prior.
- Václav Kotěšovec, *Non-attacking Chess Pieces*, sixth edition (2013), pp.82–90 and 178: http://www.kotesovec.cz/books/kotesovec_non_attacking_chess_pieces_2013_6ed.pdf . Page 83 records Conjectures 2–4; the report proves the upper-bound part of Conjecture 2 and the even-height assertion of Conjecture 4. It neither proves all-height degree attainment nor claims a historical first proof.
- Tricia Muldoon Brown, *Maximum arrangements of nonattacking kings on the 2n × 2n chessboard*, Recreational Mathematics Magazine 12(20) (2025), 41–52: https://doi.org/10.2478/rmm-2025-0003 . Preprint: https://arxiv.org/abs/2111.10331 . Its Corollary 1 covers rectangles.
- OEIS A061593: https://oeis.org/A061593 . Small-height scalar generating function for h=2.
- OEIS A061594: https://oeis.org/A061594 . Small-height scalar generating function for h=3.

The component-incidence Gram machinery is reused from companion cylindrical research. The full Alekseyev 2011 factor-generation derivation remains unrecovered, preventing any justified historical first-proof claim. A bounded literature screen is not an exhaustive priority certificate.

## Exact evidence

The coefficient data derive from an original Python exact producer (3 October 2026) with SHA-256 9a21f0446e96c8c7b7f675b012e58fbf76a1d305e112f717c67d59b2d437be23. The frozen producer output had SHA-256 1de4f15bbe1eb3141500569f0bba91933b7335f279d8132fccc9ec6ec83a8575. Its checks covered all 245152 transfer state pairs and all 36 boards through h,w=6. These provenance hashes identify computation inputs; the archived certificate is independently verified rather than trusted merely because it has a hash.

A separately written exact audit checked 7584 state pairs, 30 Gram blocks, and 16 boards through height four, reconstructing scalar generating functions from the full characteristic polynomial. A supplementary audit checked all 1184 resolvent entries through height three and the h=3 cancellation at eigenvalue one. The report's proof does not depend on finite extrapolation or these bounded numerical checks.

The archive's standard-library verifier supplies the all-width rational-GF certificate by checking N consecutive exact recurrence residuals and invoking the Cayley–Hamilton argument proved in the report. Normal and optimized runs must agree; intentional data corruption must fail. Optional SymPy regeneration is separate from default offline verification.

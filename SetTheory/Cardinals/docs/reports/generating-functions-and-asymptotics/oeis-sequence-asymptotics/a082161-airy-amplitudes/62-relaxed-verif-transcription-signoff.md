# Final integrated article verification

Date: 2 October 2026

Final TeX SHA-256: 4b24b3201e96fe662162cd189e325b1e5376a4a208d304f974da7fcbdf991af4

Final PDF SHA-256: f8e841c698413f4addb301134237c84b7a7f7367af8b9135ee9ace1c39e8c2c4

The integrated article passed the final mathematical transcription comparison. All 120 displayed equations were compared against their reviewed derivations: 72 forward-proof displays, 13 coefficient-grading displays, and 35 inverse displays. Normalization factors, scalar and profile coefficients, grading exponents, inverse coefficients, and error exponents were preserved. The only equivalent display changes were Catalan binomial notation and alignment of the inverse numerical constants.

The five equations in (I12) were also checked directly from the displayed formulas (I10), using fresh SymPy expressions with independent symbolic A, B, D, E, p, q, s. Every residual vanishes identically.

The finite-support restriction, final zero interpolation node, and explicit remainder choice p >= 1+(M+1)/3 were checked in the integrated proof. The grading lemma retains its hypotheses and uniqueness normalization.

Before the final signoff, three notation discrepancies were corrected: the profile polynomial Q in Q(0)=0 was restored to ordinary mathematical italic, the inverse's Airy-zero notation gained its distinguishing superscript, and the interpolation error used one consistent epsilon glyph. The final source was checked to differ from the reviewed version by exactly those three edits.

Outcome: no unresolved normalization, grading, coefficient, inverse-algebra, or transcription finding. Every page of the final 23-page PDF was visually inspected. The clean PDF rebuild has identical extracted text and identical rendered pixels on all 23 pages; the relevant receipt is `output/final-clean-replay.json`.

This report is technical verification of the supplied manuscript. It is not a claim of external peer review, formal proof-assistant certification, or a rigorous numerical enclosure of the amplitude.

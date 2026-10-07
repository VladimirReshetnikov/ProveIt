# Sources and provenance for Report 289

## Public mathematical inputs

1. Shabnam Akhtari and Jeffrey D. Vaaler, *Lower bounds for Mahler measure that depend on the number of monomials*, arXiv:1810.12413, submitted 29 October 2018. Theorem 1.1 and Corollary 1.1 (printed page 2), Theorem 1.2 (printed page 3).
   - Record: https://arxiv.org/abs/1810.12413
   - Primary paper: https://arxiv.org/pdf/1810.12413
   - Related journal DOI: https://doi.org/10.1142/S1793042119500805
   - The input is the coefficient bound indexed by ordered exponents. It permits complex coefficients and a finite exponent set containing the actual support. The paper's proof is not reproduced or bundled. This is established prior work, not a theorem first proved by this report.

2. *Sharp Hereditary Energy Rigidity on Arbitrary Abelian Groups*, ProveIt Report288, prepared for Vladimir Reshetnikov, 7 October 2026.
   - Frozen source SHA-256: 9e2d258dfa94b20b74846b7fc870c4a8b7213b203e63508c1268112a837c9840
   - The division-free index-two form and sum of squares are rederived in full here.
   - Its general nonaffine-map weighted upper theorem and its cyclic-or-six-point reduction are used for universal worst-case corollaries. The full cyclic/Jensen reduction is not repeated here.
   - The predecessor is not bundled, edited, or required to run the exact companion.

3. David W. Boyd, *Sharp inequalities for the product of polynomials*, Bulletin of the London Mathematical Society 26 (1994), 449–454, Theorem 1, p. 452.
   - DOI: https://doi.org/10.1112/blms/26.5.449
   - The finite-degree factor-norm inequality is the external input for the interval-constrained lower bound, with C2=exp(2 Catalan/pi). It holds for all total degrees; its proof is not reproduced.
   - The primary paper recalls the corresponding sharp two-factor constant from Boyd’s 1992 work. Full 1992 text was not inspected and is not a direct input here.

4. Peter B. Borwein, *Exact inequalities for the norms of factors of polynomials*, Canadian Journal of Mathematics 46 (1994), 687–698, Theorem 6, p. 696.
   - DOI: https://doi.org/10.4153/CJM-1994-038-8
   - Primary publisher PDF: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/7BAD7C4130762D2E6C639532BC4D4598/S0008414X00048422a.pdf/div-class-title-exact-inequalities-for-the-norms-of-factors-of-polynomials-div.pdf
   - Cited for the classical extremal factor family and historical context. Its numerical asymptotic line is not used as an exact finite-degree constant. Boyd’s theorem supplies the finite-degree bound above.

Primary source statements were checked directly on 7 October 2026. The present article contains an independently written application of the sparse theorem and new proofs of the stated energy, spectral, and finite-support consequences. No claim is made that these consequences have publication priority; no exhaustive literature search establishes such priority.

## Authored source inventory

There are exactly ten authored source files:

1. `README.md`
2. `REPRODUCING.md`
3. `SOURCES.md`
4. `Report289.tex`
5. `build.py`
6. `companion/__init__.py`
7. `companion/README.md`
8. `companion/exact_checks.py`
9. `tests/test_build.py`
10. `tests/test_companion.py`

The prepared PDF and `MANIFEST.sha256` are generated artifacts. The ZIP SHA-256 pin is generated outside the archive. Logs, review images, receipts, scratch calculations, and third-party papers are excluded from the public package.

The guarded build design and build regression suite were adapted from the frozen Report288 reproducibility template, with new report identifiers and a duplicate-destination quality gate. The companion, examples, checks, and manuscript target the present results. The prior package remains untouched.

## Proof and verification boundaries

The general sparse lower bound is proved using the cited external coefficient theorem. The interval-span lower bound uses Boyd’s theorem. The cyclotomic parity identities and L4 asymptotic applications are proved here, without a priority claim. Exact examples and bounded test families do not prove an assertion for all real weights or all abelian groups. The spectral criterion is proved after passing to a finitely generated support-difference group; the companion may only compute with explicitly supplied finite coordinate models. Local torsion must not be replaced by ambient torsion. “Some weight attains” must not be replaced by “this weight attains.”

The report does not assert that every map with infimum 3/4 is in the index-two family. It does not solve the optimal unrestricted sparse-support leading constant or the general exact support function. The containing-interval leading constant is settled, and is a different complexity measure. It makes no nonabelian, global Ramsey, or machine-kernel certification claim.

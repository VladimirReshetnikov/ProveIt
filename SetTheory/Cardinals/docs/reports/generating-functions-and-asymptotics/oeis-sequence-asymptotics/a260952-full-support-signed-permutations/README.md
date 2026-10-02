# Full support signed permutations and their asymptotic coefficients

This package contains a nine-page mathematical report, its editable LaTeX source, and an offline replay of the exact and numerical checks.

## Main results

- A proof of the explicit large-order conjecture in OEIS A260952, with every fixed correction order
- The exact scaling A260952(m) = 2^m p_m(2), where p_m multiplies n^(-m)
- Separate all-order expansions of two exact finite endpoint sums for weighted full-support signed permutations
- The sparse-sign regime with negative-sign weight lambda/n, including a Poisson law conditioned to be positive and all fixed corrections
- Growth-index inverses with a stated integer-threshold rounding ambiguity

The report credits the established generating functions, known factorial-count asymptotics, and classical Stirling-transform methods. No convergence of an infinite expansion, optimal-truncation result, or exhaustive historical priority is claimed.

## Files

- Coxeter_Full_Support_Asymptotics.pdf: complete report
- Coxeter_Full_Support_Asymptotics.tex: editable mathematical source
- code/derive.py: symbolic coefficient generator
- code/verify.py: exact recurrence and weighted signed-permutation enumeration, with numerical consistency checks
- data/coefficients.txt: five sparse-sign and six late correction orders
- data/verification.json: detailed numerical output through index 600
- data/verify_summary.json: compact replay summary
- SOURCES.md: primary source links and attribution
- build.sh: builds the PDF using pdfLaTeX
- replay.sh: regenerates the supplied mathematical data
- SHA256SUMS: checksums of the supplied files

## Replay

Python 3 with SymPy 1.14.0 and mpmath 1.3.0 is required. The replay does not use the network or install packages.

    bash replay.sh

The checks include the first displayed OEIS values, exhaustive weighted full-support signed permutations through size 6, late coefficients through 600, exact endpoint identities and q=1 cancellation, and real/complex sparse-sign tests. A successful run reports all_exact_assertions_passed. Numerical agreement is a consistency check; the report contains the mathematical proofs and uniform error estimates.

To rebuild the PDF with an installed TeX Live distribution and the standard article, Latin Modern, AMS, geometry, microtype, hyperref, and enumitem packages:

    bash build.sh

The build script keeps generated TeX caches under .build. The separate smaller endpoint is retained exactly; a fixed algebraic truncation of the leading endpoint does not resolve an exponentially small remainder.

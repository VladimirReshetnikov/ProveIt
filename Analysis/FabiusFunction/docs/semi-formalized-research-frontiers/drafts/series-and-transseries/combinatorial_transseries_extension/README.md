# Combinatorial Transseries and Their Inverses

Gamma quotients, multiple saddles, arithmetic sectors, and discrete thresholds
September 4, 2026

## Main deliverables

- combinatorial_transseries_and_inverses.pdf — the 42-page article.
- combinatorial_transseries_and_inverses.tex — self-contained LaTeX source,
  including bibliography and Wolfram Language listings. No external images,
  bibliography database, or custom font files are needed.

## Coverage

Catalan and Fuss–Catalan numbers, central multinomial coefficients, rectangular
standard Young tableaux, fixed-column Stirling numbers of both kinds, Motzkin,
central Delannoy and large Schröder numbers, involutions, alternating permutations,
connected labeled graphs, necklaces and Lyndon words, harmonic functions and
generalized harmonic functions. General finite coefficient formulas, inverse
transport, interpolation caveats, remainder proofs, and numerical checks are
included.

The article extends the linked ProveIt Transseries_And_Inversion volume. It is
not a replacement copy of that volume and does not claim Lean formalization or
priority for all formulas. References and source conventions are in the article.

## Rebuild the PDF

Use a standard TeX Live installation with pdflatex. Run:

    sh build.sh

or run the following command three times so that the contents, references, and
PDF bookmarks settle:

    pdflatex -interaction=nonstopmode -halt-on-error combinatorial_transseries_and_inverses.tex

The delivered PDF was compiled successfully with no overfull/underfull box
warnings and no undefined references or citations in its final LaTeX log.
All pages were rendered for visual layout review; selected mathematical and code
pages were also inspected at full size.

## Reproduce the computations

Tested with Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.
Install the packages in requirements.txt, then run in this directory:

    python verify.py
    python audit_symbolic.py

verify.py computes exact rational coefficient checks and 100-decimal-digit
forward/inverse comparisons. audit_symbolic.py additionally checks formal
residual cancellation, exact small-integer identities, high-precision moment
integrals, and exact rational connected-graph remainders.

Their actual outputs are included:

- verification_results.json
- verification_report.txt
- symbolic_audit_report.txt

Both scripts completed and all assertions passed. These finite computations
are checks, not substitutes for the article's all-orders proofs.

coefficient_tools.wl is the standalone Wolfram Language translation of the
listing in Appendix C. A Wolfram kernel was not used or claimed for verification.

## Interpretive boundaries

Convergent formulas, all-orders asymptotic expansions, exactly normalized
exponential sectors, and formal range inverses are identified separately.
Continuous interpolation is explicitly specified where used. The article does
not assert a unique interpolation of every integer sequence, global convergence
of Bernoulli/saddle expansions, uncomputed Stokes multipliers, or an infinite
noninteger divisor interpolation for necklaces. Section 11 summarizes precisely
which statements are proved and which extensions remain research directions.

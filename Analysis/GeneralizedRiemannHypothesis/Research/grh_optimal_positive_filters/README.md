# Optimal logarithmic support for positive Dirichlet zero filters

Research extension of the ProveIt GeneralizedRiemannHypothesis article, dated 27 November 2026.

**Main result.** For a fixed conjugation-closed family of d primitive Dirichlet L-functions, let H(B,L) be the minimum half-width of a probability filter canceling all nonzero ordinates up to B with aggregate multiplicity and satisfying |F(x)| <= exp(-L) for all |x| >= B. Then uniformly for L >= 0,

    H(B,L) = L/B + (d/2) log B + O_F(1+log log B).

Thus for the attenuation exp(-c B log B), the sharp leading half-width constant is d/2+c. This answers the leading-constant question in the merged article. A stronger weighted slit-plane lower bound and a sub-Gaussian construction lead to an improved simultaneous averaging theorem for smoothed prime errors using the vendored GRH input.

## Contents

- `paper.tex`: self-contained LaTeX source with full analytic proofs, references and further research questions.
- `paper.pdf`: compiled paper.
- `SOURCE_AUDIT.md`: repository provenance and exact dependency/novelty boundaries.
- `check_filters.py`: reproducible finite numerical sanity checks, including multiple occurrences, positive interpolation, stopband and approximate zeta ordinates.
- `numerical_checks.json`: output from the checks.
- `SHA256SUMS`: checksums of the deliverables.

## Rebuild

    pdflatex -interaction=nonstopmode -halt-on-error paper.tex
    pdflatex -interaction=nonstopmode -halt-on-error paper.tex
    pdflatex -interaction=nonstopmode -halt-on-error paper.tex

The TeX source uses standard packages (amsmath, amsthm, geometry, lmodern, booktabs, microtype, fancyhdr, hyperref).

Run the numerical checks with Python 3 and `mpmath` (tested at 65 decimal digits):

    python check_filters.py

Use `--no-zeta` to omit approximate zeta-zero computations. Numerical results are not proof certificates; the mathematical argument is independent of them. Only the upstream Dirichlet GRH input has reported machine verification; this new result was not formalized in Lean. Its priority beyond the inspected literature is not established.

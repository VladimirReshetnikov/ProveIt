# Positive filters for Dirichlet zeros

Research note: joint support–attenuation inequality, improved logarithmic support coefficient, exact no-prescribed-zero stopband minimax, and a GRH-dependent application to prime races.

- `paper.tex` / `paper.pdf`: complete mathematical argument.
- `SOURCE_AUDIT.md`: source locations and verification boundaries.
- `check.py` / `checks.json`: reproducible numerical checks. Requires Python 3 and `mpmath`; run `python check.py > checks.json`. Zeta ordinates are illustrative, not independently certified.
- `SHA256SUMS`: file checksums (`sha256sum -c SHA256SUMS`).

Rebuild the PDF with `pdflatex -halt-on-error paper.tex` twice. No external assets are required. The proofs use classical analytic facts and the standard Dirichlet zero count. The prime-race corollary assumes the Dirichlet GRH input of the ProveIt project. No new Lean formalization or exhaustive novelty verification is claimed. The support bounds concern exact cancellation with aggregate multiplicities and uniform attenuation beyond a cutoff; they do not constrain every possible prime-race averaging method.

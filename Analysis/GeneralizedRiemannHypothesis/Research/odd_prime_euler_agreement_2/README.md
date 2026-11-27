# Sharp Euler-factor agreement for odd-prime-order Dirichlet characters

Research note, 27 November 2026. This is a proposed extension of the merged
ProveIt article, not a modification of the GitHub repository.

## Contents

- `paper.tex`: standalone LaTeX source, complete proofs and references.
- `paper.pdf`: compiled paper.
- `verify.py`: standard-library Python 3 exact finite checks, including all
  multisets in rank two for exponent 2, 3, or 5 and k < exponent; exact
  cyclotomic division, conic constructions, and higher-rank tests.
- `verification.txt`: actual output from running the verification program.
- `sources.md`: provenance and scope of repository inspection.

## Reproduce

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
python3 verify.py
```

The paper proves the minimum disagreement density exactly for cubic and quintic
character packets for every rank and packet size, and bounds it for all prime
exponents. The density results are unconditional; the finite-prime and
error-correction results use the stated Dirichlet GRH theorem. The proof uses
the classical projective Reed–Muller minimum-distance theorem. No assumption
about zero simplicity or linear independence is required. The full
high-agreement spectrum, uncovered leading digits for larger primes, and
formal Lean verification of these new results remain open in this note.

The finite tests are supplementary, not a substitute for the proofs. The
vendored GRH development was inspected at its interface, not rebuilt or
independently kernel-checked. Mathematical novelty is a candidate contribution,
not a certified priority claim.

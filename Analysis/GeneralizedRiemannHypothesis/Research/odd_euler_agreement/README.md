# Sharp Euler-factor agreement for cubic and quintic Dirichlet packets

Research note for ProveIt, 27 November 2026.

## Contents

- `paper.pdf`: compiled mathematical report, with statements, complete lower-bound and construction arguments, equality structure, GRH application, references, and further research questions.
- `paper.tex`: self-contained LaTeX source of the report.
- `verify.py`: exact finite checks, using the Python 3 standard library only.
- `verification.txt`: output of a successful run of the script.
- `sources.md`: inspected repository files, blob identifiers, and mathematical references.
- `Makefile`: reproducible build and verification commands.

## Scope

The main theorem settles the minimum Euler-factor disagreement density for all cubic and quintic equal-size Dirichlet-character packets, all ranks, and all packet sizes. It provides a general prime-order lower bound and explicit equality constructions in the divisibility cases described in the paper. The density result is unconditional; Dirichlet GRH is used for finite, quantitative prime detection and density measurement. This is an extension of the odd-prime question stated in the merged article, not a claim of global publication priority or a classification of the entire spectrum of densities. The equality characterization uses the published classification of minimum-weight projective Reed–Muller codewords. No new Lean proof or independent replay of the vendored GRH proof was performed.

## Reproduction

Run `make` (requires pdfLaTeX and Python 3), or run `pdflatex -interaction=nonstopmode -halt-on-error paper.tex` three times and `python3 verify.py`. The finite checks use integer projection histograms and exact arithmetic; they are supporting tests, not a substitute for the general mathematical proof.

No files in the original GitHub repository were changed.

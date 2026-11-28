# Rigidity at the moment barrier in even-step abelian graph towers

Research extension of ProveIt, 27 November 2026.

Read `paper.pdf` (10 pages); `paper.tex` is the complete LaTeX source. The main theorem classifies every rank-two 2s-step residue list, s>=3 and p>4s, whose first s-1 directional even moments vanish. This gives an exact previously unresolved maximum for p=1+m mod 2m at sufficiently large p, with every maximizing residue list classified. For the other congruence classes the paper determines the leading asymptotic slope, but not the exact bounded offset when m does not divide p-1. The proof uses homogeneous polynomial evaluation spaces and a smooth complete-intersection curve. The rigidity and graph results are unconditional. Only the quantitative prime-counting corollary uses Dirichlet GRH.

## Build and replay

Requires a standard LaTeX installation, Python 3, and a C++17 compiler. No network access or additional Python packages are required.

```sh
pdflatex -halt-on-error -interaction=nonstopmode paper.tex
pdflatex -halt-on-error -interaction=nonstopmode paper.tex
python3 verify.py
c++ -O3 -std=c++17 verify_six.cpp -o verify_six
./verify_six
```

- `arithmetic_checks.txt`: saved output of `verify.py`, including 212 block-construction tests, four exact independent cyclotomic-norm checks, curve examples and counting constants.
- `six_checks.txt`: saved output of the exhaustive six-step search at ten primes. Counts refer to normalized multisets, not orbit counts. The code includes a comparison to the proven M1-nonzero upper bound; its reported maxima are therefore global for the indicated residue-list model, including the simple-list submodel.
- `SHA256SUMS`: digest manifest of the delivered files other than the manifest.

## Provenance and limitations

The repository was read via GitHub, not modified. Key source files: `Article/sections/gra.tex` (blob `6a866b41da2111c5fc7f9bd10dc4315c9a283de2`), `Article/sections/src.tex` (blob `f69668b2f95261630bb1282c2cc1f9c172b7e530`), and the article and project READMEs. See paper bibliography for URLs and relevant published work. The pinned upstream Dirichlet GRH development was inspected at the level of its README and statement definitions; its build was not replayed. The novelty claim is relative to the inspected repository and a targeted literature search, not a global priority guarantee. The general proof does not depend on the finite searches. No Lean formalization is claimed, and no prominent classical conjecture is asserted resolved; the open graph-tower extremal problem is partially resolved, in an infinite family and at the leading-order level for all large primes.

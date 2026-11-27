# Sharp Euler-factor agreement at odd prime exponent

**Research packet — 27 November 2026**

This note extends `rec:thm:qmatch` in the ProveIt merged GRH article to odd-prime-order packets of Dirichlet characters. It proves the universal leading-digit lower bound, determines precisely when the bound is attainable, gives exact minima for every rank and size at orders 3 and 5, proves structural rigidity, and derives finite-prime tests from Dirichlet GRH.

## Contents

- `paper.tex` / `paper.pdf`: complete mathematical manuscript and references.
- `verify.py`: standard-library Python exact-arithmetic checker for constructions, small exhaustive cases, the order-seven obstruction, cyclotomic valuations, and actual character-group residue classes.
- `verification.json`: machine-readable output from the completed verification run.
- `verification.txt`: summary of the run.
- `source-manifest.md`: source paths, inspected blobs, and dependency boundaries.
- `formalization-notes.md`: suggested Lean decomposition, not a compiled proof.
- `Makefile`: reproducible build and verification targets.

## Reproduce

Use Python 3.8+ (standard library only) and a LaTeX distribution with `amsmath`, `amssymb`, `amsthm`, `mathtools`, `geometry`, `booktabs`, `array`, `hyperref`, `xcolor`, and `microtype`. Run:

```sh
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

Alternatively `make all`. The script is deterministic; it writes `verification.json`. Exact assertions use integer arithmetic or `Fraction`. The prime-frequency examples are illustrative observations only.

## Status and limitations

The density theorem is unconditional (ordinary PNT in progressions suffices). The finite-prime estimates use Dirichlet GRH as exported by the pinned upstream development. The packet does **not** claim to have rerun that Lean proof, or to have kernel-checked the new theorems. It relies on two published classification results for the necessity of the attainability condition, but includes its own proof of the underlying minimum-weight bound. It does not classify the full high-agreement spectrum, and the minimum for nondivisor digits at arbitrary rank remains open here. No claim of priority against all existing literature is made. No changes were made to the source repository.

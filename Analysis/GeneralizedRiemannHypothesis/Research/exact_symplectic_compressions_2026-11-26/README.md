# Exact laws and hidden dependence in arbitrary symplectic compressions

Research note prepared for Vladimir Reshetnikov, November 26, 2026.

Start with **report.pdf**. Its editable, self-contained LaTeX source is **report.tex**.

## Results

This note answers the exact-law question `spn:q:symplectic` in the supplied ProveIt article. Given two arbitrary subspaces of a finite symplectic space, it computes the probability of every cross-pairing matrix, including degenerate restricted forms and characteristic two.

The joint alternating Gram matrix determines three integers `(s,u,v)`. They determine the complete likelihood. They also give the sharp support test `s + max(u,v) <= N`, and the minimum ambient symplectic dimension `2(s + max(u,v))`.

Two quantitative extensions are proved:

- For fixed block dimensions, total variation from an independent-entry matrix has an explicit positive coefficient times `q^(-2N)`, with remainder `O(q^(-4N))`.
- At ambient dimension `a+b`, with both restricted forms nonsingular, the exact optimal test is singularity of `H + M^T F^(-1) M`. If `b -> infinity` and `a-b -> infinity`, every rank-only test has vanishing advantage, whereas full-matrix total variation tends to an explicit positive product constant. Over F_2 it is `0.1306343467085051764310563857...`.

All new theorems here are unconditional. They extend the matrix-statistics branch of the supplied GRH research program. No new Riemann hypothesis is asserted.

## Files

| File | Purpose |
|---|---|
| `report.tex`, `report.pdf` | Complete statements, proofs, source analysis, examples and references |
| `code/compression_law.py` | Exact integer/rational formula evaluator |
| `code/verify_exhaustive.py` | Independent enumeration of actual injective frames |
| `code/reproduce.py` | Certified constants, finite bounds, figure and formula checks |
| `results/exhaustive_checks.json` | Exact finite verification output |
| `results/certified_constants.json` | Rational bounds and directed decimal bounds for the limiting constants |
| `results/boundary_bounds.csv` | Certified full-matrix intervals and rank-only upper bounds |
| `results/formula_checks.json` | First-order normalization and boundary sign checks |
| `figures/boundary_bounds.pdf`, `.png` | Plot generated from analytic bounds |
| `source_audit.md` | Pinned source statements and proof architecture |
| `literature_review.md` | Classical antecedents, comparison and priority limits |
| `sources.json` | Commit IDs, relevant file blob hashes and bibliographic metadata |
| `formalization_plan.md` | Dependency-oriented formalization outline |
| `SHA256SUMS.txt` | Checksums of the delivered files |

## Reproduce

The core evaluator and exhaustive checks require only Python 3.10 or newer and its standard library. Matplotlib is needed only to regenerate the figure.

```bash
python3 code/verify_exhaustive.py
python3 code/reproduce.py
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

The report needs a standard LaTeX installation with AMS packages, Latin Modern, microtype, geometry, booktabs, enumitem, graphicx, hyperref and fancyhdr. No BibTeX run or network access is required. The supplied PDF figure is sufficient to rebuild the paper without Python.

The verifier implements true F_4 arithmetic as F_2[x]/(x^2+x+1). It checks all realizable restricted forms in the listed small configurations, including zeros of the probability formula. The last recorded run passed **329,957 frame-pair observations**, **35,230 matrix outcomes**, **130,773 joint matrix/intersection outcomes**, and **16,777 impossible matrix outcomes**.

## Scope and status

The paper contains complete human-readable proofs, supplemented by exact finite computation. It is not a completed Lean formalization or an externally peer-reviewed paper. The upstream Lean development's build/checker claims are attributed to that project; this task inspected selected source and did not rebuild the entire upstream development.

The new formulas extend the supplied article, which explicitly left the general law open. Classical form-representation and subspace-counting results are credited. An exhaustive worldwide novelty or priority claim is not established, particularly because full texts of some older papers were unavailable during comparison.

No repository was modified by this work.

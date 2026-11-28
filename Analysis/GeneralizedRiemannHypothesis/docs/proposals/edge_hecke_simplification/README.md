# Integral orbit traces and the direct exceptional-divisor bound

**Start with `report.pdf`.** Two paper-level replacements for the edge Hecke estimate in the readable Alpöge–Claude proof of RH and Dirichlet GRH. Both keep the exact existing constants. The invariant average is obtained directly by scaled tensor symmetrization and an integral orbit trace. The second argument counts exceptional Smith factors by a principal-submatrix rank test, then bounds truncated colength without constructing supplementary generators.

- `report.tex`, `report.pdf`: mathematical report and compiled PDF.
- `LEAN_PLAN.md`: exact integration plan, not compiled Lean code.
- `check_local.py`, `checks.txt`: exact finite-model regressions and actual output. Python 3 and SymPy 1.14.0 were used.
- `proposal_audit.tsv`: targeted comparison with the 14 proposal directories (24 TeX files, inspected for section headings and terms relevant to this proposal; the 14 READMEs were also reviewed).
- `source_anchors.tsv`: selected source blob hashes and declaration anchors from the GitHub connector. Key source ranges were read in the pinned revision; some overview blobs were read from main immediately before its revision was retrieved.
- `verify_sources.py`: optional local checkout hash audit. It was not run here because a full checkout was not available.

Reproduce from this directory:

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
python3 check_local.py
python3 verify_sources.py /path/to/ProveIt
```

The reference commit is `17bf37ab3b6740d5d7430065d2f2a1a2a03e8a0e`. The repository reports verification of the original proof. We did not rebuild it, run Lean on the replacement, or compare the full tree with the independently verified upstream tree. The Python regressions do not establish the universal theorems, whose paper proofs are in the report. No measured net source-line savings, full-build savings, or independent proof of RH are claimed. No GitHub files were modified.

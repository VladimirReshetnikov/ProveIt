# Direct module duality and Cayley–Hamilton in the first-order Ribet argument

Start with `report.pdf` (8 pages). It proposes two independent mathematical replacements inside the readable Lean proof of Dirichlet GRH:

- Identify the module of Selmer functions with the dual of its finite evaluation module. Add detection relations at their exact length cost, preserve the ordered triangle, and lift a single determinant from the specialization at zero. The source's bound `b + (|I| + |s|) v(C)` is preserved, with a sharper actual torsion-length cost.
- Apply Cayley–Hamilton directly to the quotient on which a central variable acts by right multiplication, removing the polynomial adjugate construction and its separate evaluation lemma.

These target a small but conceptually significant local proof layer; no measured net source-line savings or independent proof of RH/GRH is claimed. All 18 proposal directory trees were inspected and the 28 TeX files screened for relevant keywords. The most closely related proposals were checked at report level. No global literature priority claim is made.

## Contents and reproduction

- `report.tex`, `report.pdf`: complete paper-level derivations and source links.
- `LEAN_PLAN.md`: implementation plan and validation gates, not compiled Lean code.
- `checks.py`, `checks.txt`: exact finite regressions and recorded output. Requires Python 3 and SymPy.
- `source_audit.tsv`, `proposal_audit.tsv`: pinned blob/tree identities and scope of comparison.
- `verify_sources.py`: optional local Git audit (not run against a full checkout in this environment).

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
python3 checks.py
python3 verify_sources.py /path/to/ProveIt
```

Pinned ProveIt commit: `9050b04000647d588d0c78d945180abcd3b0bcf7`. The GitHub connector returned the selected source blobs at this commit. No Lean executable or full repository checkout was available, so the refactor and whole theorem replay were not performed. The baseline verification record cited by the repository is https://math.mit.edu/~drew/shortgrh/; it does not certify these proposed substitutions. No GitHub files were modified.

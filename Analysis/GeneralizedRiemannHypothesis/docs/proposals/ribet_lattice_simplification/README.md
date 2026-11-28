# Direct lattice duality in the Ribet denominator argument

Start with `report.pdf` (8 pages). This is a mathematical simplification proposal for the readable Lean proof of RH and Dirichlet GRH, not an independent proof or a compiled patch. It focuses on the polynomial relation modules used in the congruence-denominator argument, upstream of the existing flag-row proposal for the operators themselves.

- `report.tex`: complete standalone LaTeX source, with proofs, source links, limitations, and further research questions.
- `LEAN_PLAN.md`: staged source integration and verification specification; no Lean code is claimed to compile.
- `check_lattices.py` and `checks.txt`: exact finite algebra regressions and their actual output. Requires Python 3 and SymPy. These checks do not certify universal statements.
- `source_audit.tsv`: selected source paths, Git object IDs, and anchors.
- `proposal_audit.tsv`, `proposal_tex_inventory.tsv`: 18 proposal trees and 28 TeX blobs reviewed at the pin. README summaries were reviewed; the TeX screen was targeted for Fitting, triangle, Smith, Noetherian, formsMod and Ribet terminology, with the closest relevant section read directly. This is not an exhaustive audit of all ancillary files or a mathematical priority claim.
- `verify_sources.py`: optional Git object verification against a local checkout. Not run against a full checkout here; the IDs were retrieved from GitHub.
- `SHA256SUMS`: archive member checksums (excluding this manifest itself).

Pinned commit: `835c3695d07c0f77060c5cc63f92eeb52a7d21c2` of `VladimirReshetnikov/ProveIt`. No GitHub files were modified. No Lean executable or project cache was available. No whole-project line reduction, kernel replay, or runtime benchmark was measured.

Reproduce the PDF and tests:

```sh
latexmk -pdf -halt-on-error report.tex
python3 check_lattices.py
python3 verify_sources.py /path/to/ProveIt
sha256sum -c SHA256SUMS # run before regenerating PDF or output files
```

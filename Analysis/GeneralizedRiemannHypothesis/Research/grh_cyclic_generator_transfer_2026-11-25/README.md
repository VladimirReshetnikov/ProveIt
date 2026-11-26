# Beyond Dirichlet GRH: cyclic-generator prime races and linear auxiliary windows

Start with **report.pdf**. The complete editable LaTeX source is **report.tex**.

This packet contains two proved mathematical refinements: a cyclic-generator test for Dedekind RH given Dirichlet GRH, using prime-only signed Frobenius weights and no global Artin holomorphy hypothesis; and an unconditional linear-window Gamma averaging lemma. The proposed arithmetic covolume bound needed to solve a new nonabelian RH remains unproved. The paper does not claim to settle a previously open famous conjecture. Novelty is provisional.

## Reproduction

- Python 3 with SymPy: `python checks.py`. Produces `certificate.json`, `sylow_checks.csv`, `pattern_counts.csv`. All integer and rational computations are exact. 69/70 finite Sylow closures were enumerated; the remaining case exceeded the configured cap. The analytic theorems are proved in the text, not tested by the script.
- PDF: `pdflatex -interaction=nonstopmode -halt-on-error report.tex` (repeat until references stabilize).
- Source map: `source_map.tsv` lists inspected GitHub file paths and blob SHAs. Upstream commit: `72fead102f663d5c7a407964a13dc0cf9d977207`. `prior_reports.md` describes the targeted prior-report review and access limitations.
- `formalization.md` records the proposed Lean interfaces and missing prerequisites. No Lean build was performed in this session.
- `SHA256SUMS` covers all delivered files other than itself; `sha256sum -c SHA256SUMS` checks integrity.

No GitHub repository was edited. The source was accessed through the GitHub connector; external verification reports and published mathematical references are cited in the manuscript.

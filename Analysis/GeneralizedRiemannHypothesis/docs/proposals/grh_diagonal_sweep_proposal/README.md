# A deterministic diagonal sweep for the theta-lift proof

New local mathematical simplification of the auxiliary-form transfer in the readable Alpöge–Claude Dirichlet GRH development. Baseline: ProveIt commit `835c3695d07c0f77060c5cc63f92eeb52a7d21c2`.

The explicit sweep replaces arbitrary-path turn search and well-founded induction with nested ordinary induction. It uses off-diagonal transfer bound 1 and diagonal bound V, obtaining V^m instead of V^(m²), and the exact refinement h^(mr+tm²). Endpoint-sensitive counting is optional. There are still m² local exchanges. The product of special-value ratios and all final statements are preserved.

- `report.pdf`, `report.tex`: mathematical proofs, source links, and analysis.
- `LEAN_PLAN.md`: implementation specification (not compiled Lean code).
- `check_sweep.py`, `checks.txt`: executable finite regressions and actual output.
- `source_audit.tsv`, `proposal_audit.tsv`: source and proposal identifiers and audit scope.
- `verify_sources.py`: optional audit against a clone containing the pinned commit.
- `SHA256SUMS`: archive integrity checks.

Build the PDF using `pdflatex -halt-on-error report.tex` (three runs). Run `python3 check_sweep.py`, `python3 verify_sources.py /path/to/ProveIt` and `sha256sum -c SHA256SUMS` for the corresponding checks. Scripts use the Python standard library; the source audit also invokes Git.

The GitHub connector was used to inspect relevant Lean interfaces, guide excerpts, all 18 proposal README summaries and headings/targeted terms in 28 proposal TeX files. This is a targeted overlap audit, not a full semantic review of every artifact. The closest orbital-exchange proposal changes a local matching theorem rather than global traversal. No overlap with the new sweep was identified. No repository files were changed. The PDF build and finite regressions were performed; the Git verification script requires a local clone and was not run against one. No Lean rebuild or kernel replay was performed, and no measured net reduction in the full formalization is claimed.

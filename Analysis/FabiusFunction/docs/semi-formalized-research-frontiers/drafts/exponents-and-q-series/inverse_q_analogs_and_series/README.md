# Inverse q-analogs and their series expansions

This directory is the canonical consolidation of the six overlapping inverse
q-analog packages formerly stored beside it.  The deliverable is one document:
`inverse_q_analogs_and_series.tex` and its matching PDF.  Files under
`chapters/` are implementation units included by that master source; they are
not independent manuscripts.

The consolidation is editorial and mathematical rather than mechanical.  A
result shared by several source reports is stated once, with the strongest
correct hypotheses and one complete proof.  Erroneous claims are corrected or
removed.  Unproved claims survive only when they are interesting and plausible,
and then only as explicitly labelled conjectures.  `theorem_concordance.csv`
records the disposition of every source result environment, while
`PROVENANCE.md` records package- and asset-level origins.

Status terminology is deliberately strict:

- `Lean-proved` means that an exact named declaration has been compiled in the
  repository and is listed in the document's Lean crosswalk.
- `Human-proved frontier result` means that this volume contains a complete
  proof but no exact Lean counterpart has yet been validated.
- `Conjecture` means that a genuine proof obligation remains.

The six source directories were removed only after every source result and
unique reproducibility asset received a canonical disposition.  The pinned
pre-retirement revision in `audit/SOURCE_REVISION` and repository history
preserve the superseded layouts.

This volume is canonical for branch-specified inverse maps and the six-package
concordance, not for every neighboring topic that uses q-products.  The sibling
`q_pochhammer_q_binomial_monograph/` remains the broad forward-theory
reference; `Cyclotomic_q_Fabius_Rvachev_Frontier/` retains the wider
natural-boundary and cyclotomic blow-up program.  `PROVENANCE.md` records these
and the other scope boundaries explicitly.

The publication gate completed on 2026-08-31.  Three serial pdfLaTeX passes
produced the committed 85-page PDF with a clean final log: no undefined or
multiply defined references, rerun request, package warning, or underfull or
overfull box.  All 85 pages were rasterized and inspected.  `pdfinfo` confirms
A4, complete title/author/subject/keyword metadata, and no encryption;
`pdffonts` reports 27 embedded/subset Type-1 rows, five Libertinus rows, and no
Type 3 font.  The 43-entry retained-asset ledger verifies exactly, and the
revision-backed audit reproduces all 260 concordance rows across the ten
immutable source fields.

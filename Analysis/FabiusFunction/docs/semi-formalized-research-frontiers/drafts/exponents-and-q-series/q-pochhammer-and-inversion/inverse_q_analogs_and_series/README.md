# Inverse q-analogs and their series expansions

This directory is the canonical consolidation of the six overlapping inverse
q-analog packages formerly stored beside it.  The deliverable is one document:
`inverse_q_analogs_and_series.tex` and its retained publication PDF.  Files under
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

The notation-normalized publication artifact was rebuilt in three serial
pdfLaTeX passes on 2026-08-31.  Its composite source has 6,689 lines across the
driver and nine chapters.  The hierarchy move subsequently changed only the
driver's relative traversal to the shared notation file; the path-adjusted
138-line driver has SHA-256
`7a4847cc65205508a8ab999e548cc6a2f9113e28ac73ee6a19baf96774fdfebc`.
The retained 971,970-byte PDF has 85 A4 pages and SHA-256
`db5e5d4835871f8802a96ffd20ed88fe87fd6ce3ba6824ce3f3728db3a10ed1b`.
It was intentionally not rebuilt for the path-only move.  It is unencrypted
and has extractable text; all 27 Type-1 font rows are
embedded/subset, five are Libertinus rows, and none is Type 3.

The earlier publication-gate receipt records a clean final log and an all-page
visual inspection for the canonical layout.  Those two inspections were not
rerun during this metadata-only refresh, so their warning counts are not
silently projected onto the rebuilt bytes.  The 43-entry retained-asset ledger
still verifies exactly, and the revision-backed audit reproduces all 260
concordance rows across the ten immutable source fields.

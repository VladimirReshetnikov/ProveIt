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

The six source directories will be removed only after the concordance proves
that every theorem, proof, conjecture, problem, and unique reproducibility asset
has a canonical disposition.  Git history remains the archival record of the
superseded layouts.

The final publication gate is three serial pdfLaTeX passes, a clean final log,
full-page raster inspection, A4 and metadata checks, embedded/subset Libertinus
and Type-1 fonts with no Type 3 fonts, a verified checksum ledger, and a
source-to-concordance coverage audit.

# Cyclotomic q-Fabius--Rvachev frontier

The canonical manuscript pair in this directory is
`cyclotomic_q_fabius_frontier.tex` and `cyclotomic_q_fabius_frontier.pdf`.
`README.txt` preserves the arrival narrative, and `PDF_VALIDATION.txt` records
the repository-added validation.  The former `SHA256SUMS` and
`SHA256SUMS.txt` ledgers were retired repository-wide on 2026-09-01; their
historical bytes and row sets remain recoverable from Git history.

## Retained publication receipt and current source status

The publication gate completed on 2026-08-31.  The source now uses Libertinus
text and complete PDF metadata.  Its four plot inclusions use the retained PNG
companions because the submitted vector figures introduced Type 3 fonts.
Exactly three fresh serial pdfLaTeX passes from clean auxiliaries produced the
retained 28-page A4 PDF (954,089 bytes; SHA-256
`769dc1bd20dfb0d24041ef00a6d2ca452d4df324e9bf4ffbb5fe5c1cd78bdff0`).

The third-pass log has no undefined or multiply defined references, rerun
request, package warning, or TeX error.  It retains one 12.25539 pt overfull
box in the estimate at source lines 514--520 and one underfull path paragraph
at lines 1807--1811.  All 28 pages rasterized successfully, contain extractable
text, are A4 with zero rotation, and are nonblank.  `pdffonts` reports 22
embedded/subset Type-1 rows, four Libertinus rows, and no Type 3 font.

The hierarchy relocation subsequently changed only the relative shared-notation
input path.  The current source still has 1,875 lines, now with SHA-256
`edd936b78e301bd80566b9472d72d8cbb3ad888a5c3f05e1e4a924a707043270`.
Repository policy therefore requires a fresh three-pass render and receipt
refresh before this source/PDF pair is again called synchronized.

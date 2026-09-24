# Build and verification audit

Date: 23 September 2026.

## Deliverable

- Article: *Curve and Abelian Rigidity over the Omnific Integers*.
- PDF: 25 pages, US Letter (612 x 792 points).
- Source: one standalone `article.tex`, with its bibliography included.
- PDF size: 456,841 bytes.
- No external graphics, custom font files, or bibliography database required.

## Compilation

Built using `latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex`
with pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian) and
latexmk 4.86. The final build exited successfully.

The source was also copied by itself into a clean directory and compiled
successfully. That standalone rebuild produced 25 pages with identical
extracted text, page by page. The packaged PDF is the visually reviewed
build; metadata timestamps need not match the clean rebuild.

No LaTeX warnings, overfull or underfull boxes, undefined references or
citations, or missing-character diagnostics were found in the final log.

## Rendering and PDF inspection

All 25 pages were rendered using Poppler `pdftoppm` at 100 dpi. The complete
render set was inspected through contact sheets; the main differential
lemma page and final bibliography page were also inspected individually.
No clipping, overlapping text, broken glyphs, or unintended blank pages
were observed.

Programmatic inspection using PyMuPDF found:

- 25 pages, all 612 x 792 points;
- 63,082 extracted text characters;
- no text blocks outside page boundaries;
- no Unicode replacement-character pages.

`pdffonts` reports 27 font entries, all embedded, subsetted, and with
Unicode mappings. No font files are distributed separately.

This is layout and file-integrity inspection, not PDF/UA or PDF/A
certification. The PDF is not tagged for accessibility.

## Exact algebraic verification

Command: `python3 verify.py`.
Result: **PASS, 13,049 assertions**.
Arithmetic: exact rational numbers and arithmetic over F_2; no
floating-point acceptance tests. Randomized finite examples use the fixed
seed 20260923. The script requires Python 3.10+ and only the standard library.
The category counts and complete recorded result are in `verification.json`.

The checks cover the universal cubic identity, finite versions of the
superelliptic divisibility argument, finite-support Euler identities,
explicit polynomial parametrizations, the characteristic-two tail identity,
Laurent-binomial coefficients, and the dual-number elliptic example.

They do not verify arbitrary infinite Hahn supports, the proper valuative
criterion, global generation, or the new point-functor theorems. Those
claims rest on the mathematical proofs in the article, with standard
inputs cited. No proof-assistant formalization or independent mathematical
review is claimed.

# PDF visual audit

Artifact: `paper/tapir_ipra_framework.pdf`

- Rendered all 54 pages to PNG at 160 DPI with the PDF skill renderer.
- Reviewed all pages in nine six-page contact sheets.
- Inspected dense pages 36 (difficulty table) and 50 (theorem ledger) at full rendered resolution.
- Confirmed: no clipped text, overlapping objects, broken tables, accidental blank pages, missing glyphs, or inconsistent page headers/numbers.
- Confirmed the title page, six-page contents, theorem/code blocks, long tables, appendices, and bibliography are legible.
- `pdf_preflight.py` reports the file openable, unencrypted, and non-scanned.
- `pdffonts` reports every used font embedded and subsetted.
- The final LaTeX log contains no overfull-box, undefined-reference, or undefined-citation warnings.

The temporary rendered PNGs and contact sheets were used for inspection only and are intentionally omitted from the archive.

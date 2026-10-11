# Delivered PDF visual review

The final 28-page PDF was rendered with PyMuPDF 1.26.7 at 120 dpi. All 28 pages were inspected through four seven-page contact sheets. Pages 13 (root-of-unity and pure polylogarithm formulas) and 22 (the explicit six-dimensional integral and large rational coefficients) were additionally inspected at full rendered size.

The inspection found no visible clipping, overlapping formulas, missing math symbols, or page-boundary overflow. The successful LaTeX build had no warnings or overfull-box flags. An initial extractable-text check identified null mappings for large left-parenthesis glyphs; explicit Unicode mappings were added in the TeX preamble and the final check passed with no replacement/null characters. This was a PDF text-mapping issue, not a mathematical correction.

`pdf_inspection.json` records the final geometry/text checks. Visual inspection is not a proof of the mathematical content. The render files and contact sheets are intentionally excluded from the small source distribution; `code/inspect_pdf.py` regenerates the page images.

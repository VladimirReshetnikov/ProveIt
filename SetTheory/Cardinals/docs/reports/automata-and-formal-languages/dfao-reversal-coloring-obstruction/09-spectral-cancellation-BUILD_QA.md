# Build and presentation checks

Final date: 30 September 2026.

- PDF: 22 A4 pages, including the cover and one-page contents.
- Built with pdfLaTeX, with repeated passes until cross-references stabilized.
- Final build log contained no errors, undefined references, duplicate-destination
  warnings, overfull boxes, or underfull boxes.
- Every page was reviewed in rendered overview sheets during layout checking.
  The final contents page, full-spectrum theorem/table, and nineteen-output
  certificate were additionally inspected at higher resolution after revisions.
- Rendering used Poppler `pdftoppm`; no OCR was used.
- A final text-span geometry check found no spans outside the PDF page boundaries.
  Extracted text contained no unresolved `??` references.
- Shared theorem counters use alias counters so cross-references distinguish
  lemmas, theorems, corollaries, and other environments correctly.
- The inline order table was checked against the regenerated `data/orders.tex`.
- The complete arithmetic audit was rerun with Python optimization enabled
  (`python -O code/verify.py`); all explicit checks remained active and passed.

These are build/presentation and implementation checks, not external mathematical
refereeing or proof-assistant verification. No font files are distributed in the
package; the PDF contains its normal embedded fonts.

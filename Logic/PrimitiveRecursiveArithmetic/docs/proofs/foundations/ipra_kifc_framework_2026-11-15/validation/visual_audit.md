# PDF visual audit

Artifact: `paper/ipra_kifc_framework.pdf`

- Final page count: 56 letter-size pages.
- The PDF was rendered at 150 DPI and inspected in fourteen four-page contact
  sheets covering pages 1--56.
- Checked for clipped text, overlapping objects, broken code boxes, malformed
  tables, missing glyphs, blank pages, inconsistent headers/footers, and
  unreadable equations. No such defect was found.
- Long tables on pages 40, 48--49 and notation/source listings on pages 52,
  55--56 remain within the text block and are legible.
- Code displays on pages 41--45 do not cross the page boundary.
- A final rebuild changed only the PDF bookmark fallback for the subsection
  containing `y^3+y=x`. Raster spot checks of final pages 1, 15, and 56 were
  pixel-identical to the fully audited render.
- Temporary page renders and contact sheets were removed from the distributable
  archive after this audit.

Benign build notes: pdfLaTeX reports two Latin Modern small-caps-italic font
fallbacks to small-caps slanted. There are no overfull boxes, undefined
references, or PDF-string warnings in the final pass.

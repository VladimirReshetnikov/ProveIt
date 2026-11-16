# PDF visual inspection

The compiled 20-page PDF was rendered to PNG at 130 DPI using the PDF skill's
`render_pdf.py` pipeline.  A 4-column contact sheet was inspected for all pages,
and full-size renders of pages 1, 5, 8, 9, 17, and 18 were inspected separately.

Checks performed:

- title, abstract, and contents are readable;
- headers, footers, theorem blocks, formulas, and tables remain inside margins;
- the Lean code listing is not clipped;
- no black squares, missing glyphs, page overlaps, or blank pages are present;
- the long difficulty and migration tables are readable;
- bibliography and appendices render normally.

The render contact sheet is included as `render_contact_sheet.png`.

# PDF visual QA

- PDF: `paper/cifer_ipra_framework.pdf`
- Pages: 70
- Render: 120 DPI using the PDF skill renderer
- Inspection: all pages reviewed through seven 10-page contact sheets during layout development; pages 1, 38, 58, 67, and 70 were inspected at full rendered size. After the final rebuild, all 70 pages were rendered again and pages 1, 35, and 70 were re-inspected at full size.
- Result: pass

Observed qualities:

- no clipped text or equations;
- no overlapping blocks;
- no black squares or broken mathematical glyphs;
- headers and page counts stable;
- long tables remain inside the page;
- code listings remain readable;
- title and metadata display correctly;
- final bibliography page is not clipped.

The final build completed without LaTeX errors. Any nonblocking spacing warnings noted during development were checked against the rendered pages and did not create clipping.

# PDF render inspection

PDF: `paper/cbip_framework.pdf`

Renderer: `/home/oai/skills/pdfs/scripts/render_pdf.py` at 170 dpi.

Automated checks:

- 42 of 42 pages rendered successfully.
- Minimum detected content margins: left 159 px, top 87 px, right 162 px, bottom 95 px.
- No page had content within 15 px of an edge.
- Extracted text contained no replacement character and no unresolved `??` marker.
- The final LaTeX log contained no overfull boxes and no undefined references or citations.

Pages inspected visually at full resolution:

- page 1: title, repository hash, abstract, and verification-status continuation;
- pages 2-5: table of contents and page transitions;
- page 6: repository audit and close-out commit paragraph;
- pages 13-17: bounded-game and trace-reflection formulas;
- page 19: backward-viability recurrence and proof text;
- pages 29-30: two-page resolution matrix;
- page 32: Lean record and theorem-body listings;
- page 34: module-dependency diagram and completion plan;
- pages 37-38: theorem ledger and validation status;
- pages 39-41: appendices, notation table, and references;
- page 42: final reference and terminal page boundary.

Observed result: no clipped text, overlaps, broken glyphs, black squares, missing formulas, malformed tables, or illegible diagram labels.

# PDF render audit

- Artifact: `paper/ipra_pfig_framework.pdf`
- Pages: 76
- Render: all pages rasterized at 150 DPI with `render_pdf.py`
- Contact sheets inspected: pages 1–12, 13–24, 25–36, 37–48, 49–60, 61–72, and 73–76
- Individual inspection: title/abstract page and code-heavy formalization pages
- Automated image checks: no blank pages; dark-pixel bounding boxes remain at least 76 px from the top, 146 px from the bottom, and 147 px from either horizontal edge at 150 DPI
- Result: no visible clipping, overlap, missing-glyph boxes, malformed equations, or unreadable code blocks detected

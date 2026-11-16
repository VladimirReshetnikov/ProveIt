# Visual PDF QA

The final `paper/conway_criterion_ipra.pdf` was rendered at 144 DPI with the
OpenAI PDF rendering helper and all 32 pages were inspected in eight 2x2 contact
sheets.

Checks performed:

- title page, table of contents, running headers, and page count are consistent;
- theorem statements, displayed equations, tables, and proof-ending symbols are visible;
- all three source-listing blocks render as light-gray framed text, without clipping;
- both mathematical figures are legible and their captions remain on the same pages;
- appendix pseudocode, theorem ledger, reproduction commands, and references are readable;
- no blank, rotated, truncated, or anomalously dark page was found.

The first render exposed a malformed `listings` background declaration that
produced black blocks on the Lean-outline pages.  The declaration was corrected
to `backgroundcolor=\\color{black!2}`, the PDF was rebuilt, and the complete
32-page visual inspection was repeated on the final build.

The final raster metrics are in `render_metrics.json`; the largest fraction of
nearly black pixels on any page is below 0.017.

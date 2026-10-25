# Doubled85 page: independent actual-PDF visual review

2026-10-24. VISUAL PASS, no finding, for exactly `candidates/one-page-doubled85/equation.pdf`, SHA256 `20e55f8eb60ec0311c5442e20d8ed80c14cf962f11c8fae738d6ef0131bfcdc8`, 161121 bytes. `pdfinfo` independently reports one unrotated Letter page, 612 by792 points. The reviewed TeX remains SHA256 `de9c1a98cf7933ca79ae3380bd5b89e1cb14375161440bde8c16541b56370b49`, with the declared9-point body and7.7-point seed.

After the author's notification that all five explicitly released render/audit/rerender commands passed, I independently converted that exact PDF with the read-only command

```sh
pdftoppm -png -singlefile -scale-to 1800 candidates/one-page-doubled85/equation.pdf /tmp/reduce-doubled85-visual
```

I inspected the resulting whole-page image using `view_image`: `/tmp/reduce-doubled85-visual.png`, SHA256 `591ea55ebd27c2a25d68b7fa0ac1e63f5ce376f96c03dab357eaf5ecf3c98aa5` (1391 by1800 pixels before display resizing).

The title,85-operation/degree328 heading and ten-positive domain are clear. All front definitions, the two-line carrier and boxed equation are readable, with distinct subscripts, powers and signs. The two columns have a clear gutter; no displayed material collides or crosses a margin. The complete fixed-integer formulas occupy the left lower column cleanly. The943-tile table, including the last multiline index, fits the right column and its rule. The decoder, ordered alphabet, all seed rows including the final `8P`, and complete footer are visible. The footer clears the lower margin; nothing is clipped. No overlap, truncated formula, missing line or visual layout defect was found.

This is a visual review of the exact PDF, supplementing `reviews/one-page-doubled85-static-peer.md`. Mathematical equality, complete constant/glyph extraction, mutation controls and deterministic bytes belong to the separate static and released finite audits. I ran no page/source module, renderer, TeX engine, compiler or Lean program for this review, made no page/core/parent edit, and do not promote the canonical page.

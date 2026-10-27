# Final report visual and content QA

**Status: PASS / frozen for packaging.** Reviewed 27 October 2026 (UTC).

## Frozen deliverables

- `report.tex`: 82,234 bytes; SHA-256 `f3d030be97e1a2178fcece5fd17f4c80f190175e1c912879d5997baaecc4a19a`.
- `report.pdf`: 474,142 bytes; SHA-256 `7acdc69d791c90a15c3df2154e9e8fb9f626b70ed23c143e17f1bd791161a19b`.
- PDF: 26 US-letter pages, unencrypted, embedded Latin Modern fonts.
- The TeX is standalone: no external `\input` or `\include` fragments. Package this source, not obsolete authoring fragments.

## Build and visual inspection

The final source compiled twice successfully with pdfLaTeX; the final build log is `qa/latex-pass4.txt`. There are no overfull boxes, unresolved references, LaTeX warnings, or errors. Two underfull-box diagnostics arise in a long archive-filename paragraph on page 26; visual inspection confirms legibility and no clipping.

The final PDF was rendered with Poppler at 95 dpi into `qa/verified_pages/page-01.png` through `page-26.png`. Every page was visually inspected during the closing QA passes. The last layout-only change affected pages 1 and 23–26; those five final page images were re-inspected individually. Pages 2–22 are byte-identical to their already-inspected images in `qa/final_sealed_pages`. Final image SHA-256 hashes are recorded in `qa/visual_page_hashes.json`.

Inspected title/abstract and contents, all displayed mathematics, resource-frontier and benchmark tables, page breaks, proof headings, monospace paths and replay commands, headers/footers, archive appendix and final allocation derivation. No overlap, clipped content, missing glyph, blank-page accident, table collision, or unreadable line was found. The 23-row Cauchy table intentionally continues across pages 22–23 with a repeated header; the artifact map is together on page 24.

## Content checks tied to final artifacts

- Closing source cutoff is `fa6e904d109b738154db7fe41e7f2777e6d24aee` and the seven initial plus five late arrivals are distinguished.
- Polynomial-space streamed coefficient 55.33162212 (certified below 55.35), degree-sensitive coefficient 25.16376542 (below 25.2), and extra-space CRT/tree coefficients 35.07061367 time / 33.99950164 space are separately qualified.
- Late recurrence, adaptive schedules, streamed conditioning, CRT and contraction-tree precedents are explicitly credited. Historical ablations are not represented as the closing best bound.
- Practical headline comparisons use support-sparse versus dense-delta scoring and fused versus matched one-inversion, bit-mask modular quadratic Cauchy tables. The 11 packing fixtures and 23 final Cauchy records retain regressions, full preparation and all raw samples in their source artifacts.
- Benchmarks are component-only, not SAT solve timings. The report makes no global optimum, improved logarithmic order, new matrix-multiplication backend, end-to-end solver, or formal verification claim. Upstream hypotheses remain explicit.

No further source, result, or mathematical edits are pending in this report. Packaging, integrity sealing, and user-facing delivery remain with the parent task.

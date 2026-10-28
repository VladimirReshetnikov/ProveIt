# Final PDF visual review

The final PDF has 30 pages. Every page was rendered with Poppler at 100 dpi and visually inspected. After the late sparse-matching extension and degree-0.51 cached corollary, all changed pages were inspected again; pages 4 and 5 retained byte-identical PNGs from their prior individual inspection. Final page hashes are in `visual_page_hashes.json`. Stale page 31 from an intermediate build was removed.

No clipping, text overlap, missing glyphs, broken tables, displaced formulas, header/footer collision or unreadable links were found. Initial overfull numeric paragraphs were changed to displayed equations before final rendering. The final LaTeX log has no overfull boxes, undefined references or LaTeX warnings. Harmless underfull paragraph notices were visually reviewed.

The report preserves 11-point body text and original margins. A repeated prose inventory was condensed to the nine exact archive names, avoiding a near-empty extra reference page. The source is standalone ASCII LaTeX and uses no source fragment includes. `build_report.sh` provides a standard two-pass pdflatex rebuild; `qa/build_report_local.sh` records the existing local format/font-map workaround without installing anything.

Final matching and mixed-kernel source SHA-256 values match their authoritative benchmark ledgers and the successful independent component audit. The report's three-method matching table uses the final 11-fixture source-matched ledger.

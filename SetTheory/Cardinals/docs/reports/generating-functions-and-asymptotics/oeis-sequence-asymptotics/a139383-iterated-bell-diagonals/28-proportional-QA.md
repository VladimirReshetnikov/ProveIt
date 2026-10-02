# Final production and verification record

Date: 2 October 2026.

## Mathematical transcription

The independent final integrated source review passes, conditional on the stated fixed-contour foundation and seed certificate. See `review/final-source-audit.md` and its pinned source hash manifest. The authored source remains unchanged after that review.

## PDF and all-page visual inspection

- Final PDF: 11 letter-size pages, 612 by 792 points
- Three-pass pdfLaTeX build completed successfully
- No overfull or underfull boxes, undefined references, or LaTeX warnings in the final log
- All 11 pages rendered by Poppler at 115 dpi and individually inspected
- Confirmed readable mathematics, intact subscripts/superscripts, clean line breaks, consistent headers and page numbers, no clipping or overlap, and no missing glyphs
- Checked the final branching identity after correcting the superscript and adding its m >= 1 scope
- Font inspection confirms embedded fonts
- Rebuilding with the documented script produces the byte-identical PDF

The rendered PNGs and extracted text are production QA scratch and are not included in the delivery archive. `results/compile.log`, `results/pdfinfo.txt`, and `results/runtime.json` retain machine-readable build evidence.

## Exact symbolic replay

The package-relative default replay passed:

1. Regenerated the foundation's exact order-three orbit data
2. Matched the complete saved orbit JSON
3. Generated all general-beta coefficient data through order three and matched the saved JSON
4. Verified the independent first correction, degree checks, diagonal reductions, and bounded-shift translation through order two

The output is `results/exact-replay.txt`. The unchanged foundation manifest and frozen independent proportional-audit manifest both verify. The default replay does not rerun the foundation's interval certificate; its existing audited certificate and reproduction instructions are included unchanged.

## Delivery integrity and clean extraction

The delivery SHA256 manifest and structured manifest cover all archive payload files. The completed archive was extracted into a fresh temporary directory, its SHA256 manifest verified, the package-relative default exact replay passed, and a clean PDF rebuild matched the delivered PDF byte for byte. Packaging scratch and full third-party source works are excluded. The source provenance file supplies verified links and hashes for those works.

The optional numerical diagnostics are explicitly noncertified and remain separate from the symbolic and interval checks. No numerical positivity certification away from beta=1 or target-specific inverse threshold enclosure is claimed.

# Build and visual validation

The modular and standalone LaTeX sources were both compiled successfully
with pdfLaTeX/latexmk. Both outputs have 22 A4 pages and identical extracted
page text. The deliverable includes the modular build as `article.pdf`.

The final LaTeX log has no undefined references/citations, LaTeX warnings,
or overfull boxes. All 22 pages were rendered for visual inspection. The
final bibliography page and adjacent page were re-rendered after the last
layout adjustment; no clipping, overlap, or missing glyphs was observed.

`results/build_validation.json` pins the delivered PDF by SHA-256 and records
these checks. `results/verification_summary.json` records the 538 exact
assertions and 76 passing numerical comparisons. These observations do not
constitute formal verification of the analytic proofs or interval-certified
rounding analysis.

PDF binary metadata can change when rebuilt. SHA256SUMS authenticates the
supplied package contents, not a promise of bit-for-bit reproducible LaTeX
output on every installation.

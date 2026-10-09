# Delivery validation

The final article has 20 A4 pages. It was compiled three times with pdfLaTeX,
with no missing references, missing citations, or overfull boxes. One benign
underfull bibliography paragraph remains. PDF pages were rendered with pdfium
at 120 dpi; full-document contact sheets and full-size TOC/table pages were
visually inspected for clipping, overlap and broken glyphs.

The delivered core code passed all 24 test methods (zero failures, errors or
skips). The source audit reran 3,227 inputs in 19.38 seconds, with no resource
limit and no false positive against the independent small-cube oracle. The
benchmark reran all 588 measured calls plus 84 warm-ups. The sieve follow-up
reran 324 measured graph calls plus 36 warm-ups and 28 binary capacity calls.
All current data source-hash dictionaries match the delivered code exactly.
The benchmark drivers also assert that hashes do not change during execution.

The saved circle certificate was regenerated and accepted by independent source
replay. The figure-eight CLI example with the small-cube fallback returned
KNOTTED, reduced rank 5, and a checked square-zero differential.

These checks validate this standalone contribution, not the maintained native
fastunknot package. No native suite, native PD integration or native performance
comparison was performed. Mathematical proofs are not Lean-formalized.

The archive excludes transient LaTeX build files, Python caches, render previews,
and tool-environment files. Rebuild products may change file hashes; verify the
shipped manifest before rebuilding. Historical measurements have separate source
hashes and are not merged into the current tables.

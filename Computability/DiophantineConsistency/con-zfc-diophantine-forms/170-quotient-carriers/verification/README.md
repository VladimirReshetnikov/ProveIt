# Release verification receipts

`RELEASE_NORMAL.json` records the complete normal-Python mathematical and
artifact check before the top-level integrity manifest was created.
`RELEASE_OPTIMIZED.json` records the same complete checks with Python `-O`,
including verification of the then-current 559-file manifest before and after
the checks. Both runs started outside the package directory.

Only the optimized receipt itself and this explanatory file were added after
that optimized run. The final `MANIFEST.sha256` was then regenerated to cover
all 561 other package files, and every named digest and ZIP entry was checked
again during packaging. The earlier manifest digest in the optimized receipt
therefore identifies the verified package before its own receipt was inserted.

The two release receipts preserve all component diagnostics. `PDF_QA.json`
records the final PDF hash and visual/mechanical review; `PDF_BUILD.log`
retains the successful TeX build. These checks do not decide consistency or
replace the ordinary unbounded proofs in the article.

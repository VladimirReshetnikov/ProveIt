# Grouped66 actual r2 PDF: independent visual review

Verdict: **PASS**. The actual page is legible and complete, with no observed
clipping, overlap, missing display or font-rendering defect. This is visual
approval of the exact rendered artifact, not a promotion or execution release.

ROOT's separate rasterization/visual authorization is recorded in
`reviews/one-page-grouped66-fresh-replay-release.md`, commit `562fbb48e2`.
The reviewed PDF is `candidates/one-page-grouped66/equation.pdf`, 159729 bytes,
SHA-256 `c60f35c31bfbf8d386ee28f718f23c50c004f461cfa41ec58bfb44326ed13106`.
Its exact TeX is 5395 bytes, SHA-256
`b55974f915875136060858a6a763821183ad6a1c7b0b2326aa87f01c708f7ea4`.
Both were rehashed unchanged after rasterization and image inspection.
Repository paths are relative to `Computability/DiophantineConsistency/`.

## Actual images and page metadata

Read `pdfinfo` and `pdffonts`; rasterized the actual PDF directly with
`pdftoppm` into `/tmp/grouped66-visual-peer-9oyVCb`. Viewed the whole page
at 200 dpi and five overlapping detail regions at 300 dpi with `view_image`
at original raster resolution. No image alteration or annotation occurred.

The PDF has one unrotated 612 by 792 point Letter page. All thirteen listed
Type 1 font subsets are embedded, subsetted and have Unicode mappings.
The visible body, mathematics and monospaced seed are sharp and distinct.
The exact bound TeX specifies a 9-point body and 7.7-point seed; the observed
rendering is consistent with those declarations. Physical font sizes were
not inferred from an enlarged screenshot.

| Inspected raster | Resolution | Pixel dimensions | Content |
| --- | ---: | ---: | --- |
| `whole-page-200dpi.png` | 200 dpi | 1700 by 2200 | Entire page, title, both columns and margins |
| `front-detail-300dpi.png` | 300 dpi | 1190 by 960 | Positive domain, all abbreviations, boxed equation |
| `constants-detail-300dpi.png` | 300 dpi | 1190 by 1500 | Fixed constants, floors, Phi, Lambda and set/rank definitions |
| `table-detail-300dpi.png` | 300 dpi | 1200 by 950 | Whole tile table, local domains and payload |
| `decoder-detail-300dpi.png` | 300 dpi | 1200 by 750 | Full action decoder and constructor explanation |
| `seed-footer-detail-300dpi.png` | 300 dpi | 1200 by 820 | Alphabet, entire seed and footer |

All six are retained in the directory above. The accompanying JSON records
their complete byte hashes, dimensions, resolution and exact PDF crop
rectangles, together with reproducible rasterization arguments. Crops are
inspection windows; the whole-page image establishes the actual page edges.

## Findings from the whole page and details

The centered title and cost/domain subtitle are clear. The two columns are
distinct, with adequate outer margins and white space below the complete
content. No content enters the intercolumn gap or runs off a page edge.
Headings and prose do not collide with formulas or table rules.

The full ordered positive-unknown signature is visible, including its
strict-positive domain. All front definitions, signs, subscripts and powers
are readable. The boxed six-factor equation is complete, centered, and its
border does not touch its mathematical contents. The final subtraction
and zero endpoint remain visible.

The radix, B, beta, geometric sum and complete two-term Lambda definition
are present. MC's entire indicator sum and both floor delimiters are clear;
the floor operand, division by rho and exterior rho power remain distinct.
All MF lines and the reciprocal Phi(1/rho) term in K are legible. Every
line of Phi, all four grouped control contributions, bounds and exponents
is visible without overlap. The rational-intermediate explanation and
tile-set/rank definitions remain complete at the lower left.

The entire table is visible in the upper right. Index and ordered-tile
columns align across the vertical rule without collisions. Both pass
rows, right/left copies, cleanup floor, literal controls, constructor
(3,436,4,4), tail tiles and final nine-tile row are readable. The smaller
last-row substack still distinguishes its index formula, floor, label set
and binary/ternary domains. The payload definition below the table is intact.

The complete digit/remainder definition and action decoder are readable.
Floor delimiters, the three packed components, both prefix sums, flag
selector, target decoder and final v/d equations have adequate separation.
The actual-first-target/constructor explanation follows without truncation.

All 62 alphabet symbols are visible in order. The seed's seven full lines
and final `8P` line are fully inside the column; every line is readable,
with no clipped terminal characters or overlapping baselines. The visible
start `BxEnhvy6Ni` and final `8P` match the bound literal seed. The complete
436-character region was inspected, not a selected example line. The whole
glyph audits recorded in ROOT's release separately bind its exact text.

The entire footer is present through its final unsolvability-proof sentence.
Its normal English line hyphenation is readable. The ordinary mathematical
statement and the explicit open native-calibration/internal-ZFC/Lean boundary
remain legible. No page-fit or readability finding remains.

## Review boundary

Only authorized read-only PDF metadata/font inspection and rasterization,
image viewing and inert hash/JSON checks were performed. No candidate,
source or metadata file was edited. No helper, auditor, compiler, native
decoder or Lean application ran. The PNGs are temporary inspection evidence;
only these two outside visual-review records were authored in the repository.
The reviewed PDF and TeX stayed byte-identical. Final closure or promotion
remains a separate ROOT decision.

# Independent actual visual review: compact66 radix55 page

**VISUAL PASS. Findings: none.** I inspected the entire actual page with
`view_image` in original detail, using the existing180dpi PNG supplied by
ROOT. I authored neither this page nor its renderer. This verdict comes
from viewing the rendered page, not from TeX text or a glyph receipt alone.

## Exact viewed artifacts and conversion attribution

* TeX: `candidates/one-page-compact66-radix55/equation.tex`,5195 bytes,
  SHA256 `440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
* Actual PDF: `candidates/one-page-compact66-radix55/equation.pdf`,160082 bytes,
  SHA256 `4681aa56300883fab83d1c1d47f65ee969bd0a4f68156de6455f74b8f828c302`.
* Actual viewed PNG: `/tmp/radix55-page-visual.png`,506910 bytes,
  SHA256 `399a4a5f02a9f43caaa503fc31e4abb23940c21dc46a60c0cfd1f7e92f51f15b`.

The separate existing-standard-viewer release is commit249d07ef0c,
`reviews/one-page-compact66-radix55-visual-release.md`,1930 bytes,
SHA256 `f6c0298f0650952240bcf1af7ee1d7e9f0afef0654ee501cbfb36f65193509f8`.
ROOT ran the released `/usr/bin/pdftoppm` command and directly observed
its actual exit0. I did not run or repeat that conversion. Both complete
conversion captures are present and empty: `/tmp/radix55-page-visual.stdout`
and `.stderr`, each0 bytes/SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The displayed page is1530×1980 pixels, consistent with one Letter sheet
at the released180dpi. Exact TeX/PDF/PNG hashes were rechecked by this reviewer.

## Entire-page observations

The title and subtitle are clear and fully inside the top margin. Both
columns have a clean gutter and adequate outer margins. The page has
comfortable remaining white space below its last material; no content
is crowded against a page edge. No clipping, overlapping text, unexpected
blank box, missing-glyph appearance or intersecting display was visible.

The full fifteen-positive-input line, all polynomial abbreviation rows,
all six named factors and the boxed single66-operation equation are
legible. The q-minus abbreviation, powers, Greek letters, subscripts,
minus signs and factor indices are distinguishable. The box is complete
and does not collide with neighboring prose or displays.

All four fixed integers and their full displayed definitions are visible.
In particular rho=2^55 and B=rho^8807 are readable. The high-mask line
shows both `-rho^8792` and `(2^41-4)rho^7691` without a clipped sign,
exponent or continuation. The support-decoded low-mask floors, Laurent
K term and the entire Phi display, including all control groups, are
legible. The separate indexed coordinates w_i,n_i,p_i,s_i appear clearly
in Phi and the tile-table header; the east coordinate is not visually
confused with the polynomial abbreviation E.

The lower-left head/set/rank definitions are complete. The top-right
fixed range ending942 continues normally across the prose line break.
Every tile-table row, its index expression, small range/subscript and
four coordinates can be read. The two columns and table rule remain
separate, including the compact direction-indexed copy-row caption.

The complete430-action decoder, all floor/remainder expressions, finite
sum limits, first-action statement and initializer explanation are
present and readable. The alphabet line is complete and remains inside
the column. All eight seed lines are visible, including the final `8P`;
the monospace text has no clipped line ending or collision with the
surrounding prose. This is an actual legibility check, not an assertion
that image inspection replaces the separate exact436-character audit.

The entire footer is visible and readable, including its statements
about ordinary calibration, the open Lean boundary and finite-specification
scope. Its prose line wrapping does not hide text. The source specifies
9pt body and7.7pt seed/footer; the actual rendered density and legibility
are consistent with those settings. No font reduction or layout repair
is requested by this visual review.

## Scope of the verdict

This review accepts visual legibility and layout of the exact actual
PDF/PNG above. It does not prove the polynomial, formal coefficient
identity, full glyph stream, complete source calibration, precise live
operation count or mathematical endpoint. ROOT's independent whole-PDF
audit was still pending when this visual task was assigned. Those audits,
fresh comparisons, complete ordinary evidence and endpoint/page-promotion
decisions remain separate. This report promotes no maintained page.

Only the standard image-view tool, existing bytes/source/release/capture
reads and hashes were used. No new conversion, rendering, import, AST,
application/helper/evaluator, native/tuple/collector, Lean, TeX or PDF
process ran. No source, candidate, frozen parent, main page or Lean file
was edited, repaired, resealed or committed by this review.

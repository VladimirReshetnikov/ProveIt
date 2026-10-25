# Compact66 independent actual visual review

Verdict: **PASS**. I actually viewed the exact PDF as a complete 200-dpi
page and six overlapping 300-dpi details. The arithmetic, constants, tile
table, decoder, alphabet, complete seed and footer are legible. No clipping,
overlap, lost glyph, column collision or layout defect was found.

The authorization is ROOT's separate fresh/visual release at commit
`b99f8c0b3a`, `reviews/one-page-compact66-fresh-visual-release.md`.
This is an actual visual review, not a new source audit, typesetting run,
runtime control result, fresh replay or promotion authorization.
Paths below are relative to `Computability/DiophantineConsistency/`.

## Exact inspected document

The actual `candidates/one-page-compact66/equation.pdf` is 159875 bytes,
SHA-256
`25458f58d4af6887eaf6cfc379dee0838e5aa867596268068f59da961f8f45bd`.
Its complete 5244-byte TeX has SHA-256
`dd56700d91a2805bd6051bc608522a30fb8cfdd45bbe0677de458215316d89af`.
Both were authenticated before rasterization and rechecked with the visual
records. `pdfinfo` independently reports one unrotated Letter page,
612 by 792 points, PDF 1.5, with no encryption or JavaScript.

`pdffonts` reports thirteen embedded, subset Type 1 fonts, all with Unicode
mapping. CMR9/CMMI9/CMSY9 supply the body/math and CMTT8 supplies the seed;
the authenticated source and render record specify 9-point body and
7.7-point seed. The retained transcript and diagnostics contain no
`Overfull` entry. Those metadata checks support the direct visual finding;
they do not substitute for looking at the rendered page.

ROOT's release records all ten first commands and both full PDF glyph
audits as passing. I read that release and ran only authorized read-only
PDF tools, scratch rasterization, and inert metadata/hash inspection.
I did not rerun any candidate auditor, producer, renderer or compiler.

## Actual views and observations

The complete page was viewed at original resolution, 1700 by 2200 pixels
at 200 dpi. The title and subtitle are centered and separated from the
two columns. The left arithmetic schedule and boxed product equation
have adequate spacing. The four-constant section continues into the
fixed-tile definitions at the lower left; the interval explanation and
table continue naturally at the upper right. Both columns and the footer
remain inside the page, with clear outer margins and substantial space
below the last line. No rule or glyph crosses the column gutter.

I also viewed every following 300-dpi crop at original image resolution:

| Image | Crop x,y,width,height in 300-dpi page pixels | Actual visual scope |
| --- | --- | --- |
| `front-300dpi.png` | 60,75,2430,1060 | Full title/subtitle, fifteen-positive signature, all displayed arithmetic, boxed equation; table context |
| `constants-300dpi.png` | 60,1110,1225,800 | rho/B/beta/G/Lambda, complete MC/MF/K displays and indicator floors |
| `phi-ranks-300dpi.png` | 60,1870,1225,720 | Full Phi, all four control groups, rational-cancellation prose, h/S/r definitions |
| `table-300dpi.png` | 1290,230,1200,900 | Every tile row/domain, merged copy substack, constructor, last-nine square row, complemented payload |
| `decoder-300dpi.png` | 1290,1130,1200,770 | Digit/remainder definitions and floor brackets, all eleven decoder assignments, first-target explanation |
| `seed-footer-300dpi.png` | 1290,1850,1200,730 | Complete alphabet, positional sum, all eight seed lines including final 8P, full ordinary/Lean/proof footer |

The nested subscripts `r_(0,u_j)`, `r_(1,u_j)` and `r_(d,q)` are visibly
distinct. The two-line merged copy index/domain fits within its table
cell without touching adjacent rows; the vertical rule clearly separates
indices from ordered tuples. All ten row schemas, binary domains, the
constructor `(3,436,4,4)`, and the terminal `a^2` are readable. The
complemented payload's minus signs and exponents 34,8,17,25 are clear.

The four integer definitions show complete sums, exponents, Lambda uses
and reciprocal Phi argument. Both floor delimiters are visible in the
MC indicator and the decoder's quotient/remainder expressions. Phi's
selector term and all four grouped terms fit without collision. The
rank cardinality bars, intersection symbol and interval endpoints remain
legible at the lower left.

The decoder's sum limits and Greek/indexed symbols are clear. The
factored flag parentheses in `14+m_q(D_16(E_0,tau_q)-14)` remain visible;
the target/write/direction assignments are separated. The monospaced
62-symbol alphabet and every line of the 436-character seed are visible,
with mixed uppercase/lowercase letters and digits distinguishable in the
enlarged view. The final short `8P` line is present. No seed line is cut
off at the right column edge.

The full footer is legible, including the ordinary equivalence, native
and internal-ZFC formalization boundary, and statement that the page is
not an unsolvability proof. Its automatic `unsolv-`/`ability` line break
is ordinary English hyphenation. It does not hide a missing footer line
or collide with the seed.

The authorized `pdftotext -raw` read corroborated the visible complete
front, constants, table, decoder, seed and footer. The saved extraction
has 2801 nonwhite characters, matching the render record; this count is
supporting actual-output metadata, not the basis of visual approval or
a replacement for ROOT's full glyph audits.

## Retained images and boundary

All seven images remain in `/tmp/compact66-visual-peer-LzvAtD/`.
The JSON records their absolute paths, full byte counts, dimensions,
SHA-256 values, rasterization arguments and explicit actual-view flags.
The whole-page image SHA-256 is
`9121e72ab3f834d3f272e03d5909325262c5333d520d5cf65372c44724e99679`.
These images derive directly from the approved PDF through `pdftoppm`;
they were not edited or regenerated by a candidate application.

Reauthenticated all nineteen held payloads against HOLD and the exact
candidate inventory of twenty held files plus nine released outputs.
The held inputs, PDF and TeX remained unchanged. Only scratch PNG images
and these two outside visual records were written. No candidate or
maintained-page file was edited, and no application/helper, TeX engine,
Lean process or new tuple/coefficient generation ran. ROOT owns the
separate fresh-replay verification and any later sealing or promotion.

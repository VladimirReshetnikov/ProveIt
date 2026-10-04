# Independent manuscript audit of Report 53

Date: 4 October 2026.

## Verdict

**PASS on the final pinned 17-page manuscript. No unresolved mathematical, scope, accounting, or layout defect was found.** The main physical-input theorem retains its explicitly identified constructive Pell dependency. The separate r.e.-completeness corollary retains its additional, disclosed corrected physical-simulation hypothesis. This audit does not claim a new formal verification, independently audited infinite physical routing, a numeric universal tile, or a paid raw-program compiler.

Reviewed final files:

- `Research_Report53.tex`: SHA256 `c0bf6e14c00b3db5929a26169485c5b6df48e970ac347f7686036f5d113ce197`
- `Research_Report53.pdf`: SHA256 `8d3fc79f999627b3d5786e00c36b7bb04ddd8201ed7f851d39d01c73a906089c`
- Both are in `/workspace/shared/repeated-sandpile-report53-release-20261004/`

The manuscript was read in full. Its final PDF was visually inspected on all 17 pages. An independently issued Poppler render of the final pinned PDF reproduced all 17 inspected PNGs byte-for-byte. The new Section 11 research directions and the revised final bibliography were included in this review.

## Method and execution boundary

I read the manuscript, the main adversarial audit, the physical-interface review and primary-source anchors, the pinned Lean theorem text, and the relevant literal source and receipts as data. I executed only newly authored inspection code and ordinary read-only/rendering utilities. No submitted builder, upstream checker, schedule, source-freezing script, or Lean file was executed or imported. No scientific source or manuscript file was changed by this audit.

The fresh `check_literal_dag.py` independently parses the inert JSON, checks reference order and declared leaves, expands each body expression into exact sparse integer coefficients, computes every residual degree and highest-degree term, verifies the actual ordered sum-of-squares syntax, and checks full reachability. It does not use the submitted builder's expression implementation or import an upstream auditor. This manuscript audit's fresh script verifies accounting and exact degree; it does not separately reconstruct all 2,251 intended clause specifications from prose. The existing exact specification-reconstruction audit is reviewed as separate evidence and is not represented as a new run here.

## Mathematical review

### Raw interface, domains, and arithmetic

The eleven-field positive-input contract is explicit and consistent with the exact source. Cantor tails are natural, dimensions are positive, and declared high zero padding is distinguished from forbidden nonzero tails. The tile mask permits exactly digits 0 through 5; the patch mask permits exactly digits 0 through 15. The signed target decoding is exact.

The displayed POWER specialization has all fifteen equations and twenty-six positive leaves. The shift to positive Pell index covers exponent zero. The auxiliary Pell equation forces the needed ordering for natural subtraction, and the converse explains the stronger positive-coordinate and positive-quotient requirements. The manuscript accurately identifies the two pinned Lean theorems without claiming a new compilation.

Sub handles the zero and out-of-range cases through strict extraction bounds. The AND argument is valid because contained-bit subtraction is borrow-free; its residual-disjointness clause is sufficient. SPREAD uses full radix digits, not merely bits, and its stride gap prevents product collisions and isolates the diagonal mask. Its copy denominators are strictly positive on the established domain.

Both original radix-32 streams undergo distinct paid conversions. Their length/stride conditions and enlarged-radix growth condition are compatible for every finite run. The source does not replace the free physical code by uncharged recoded input. The manuscript's well-founded domain order is sufficient to avoid invoking a macro on an unproved or negative domain.

### Geometry and every face

The row and plane strides give the claimed mixed-radix indices. The bound on each row output establishes the next plane call's input range. Tile repetition is collision-free by unique coordinate decomposition. The patch shift places it at the physical origin and strictly inside the box.

The three interior-mask equations yield exactly the strict interior, with all six faces excluded for event/count sources. Both positive and negative spatial shifts stay in their own frame. The x faces prevent row wrap, the y faces prevent plane wrap, and the z faces prevent temporal wrap. Destinations on the shell are permitted, correctly. Exact negative-shift divisions do not borrow from a preceding time frame.

### Noncircular recurrence

The frame proof begins only with the range and support that the actual masks establish; it does not assume small candidate counts or carry-free candidate addition. Modulo the frame radix, the first count frame is forced to zero. At each subsequent step, previously established cumulative counts plus a binary event digit are at most K and hence below b. This proves the next frame without assuming its conclusion. The last-frame argument covers the final count and excludes an extra temporal carry; K=1 and empty event layers are included.

The independent gcd proof is also correct. A canonical cumulative-count history can be constructed from the events alone, since K<b. Subtracting its telescoping equation from the candidate equation makes the difference of pre-streams divisible by the full time modulus, using coprimality with the frame radix minus one. Both pre-streams lie in the same half-open interval of that modulus's length, so they coincide. This argument does not use legality and excludes malicious large-digit candidates.

### Legality, repetitions, target, and equivalence

The availability bound is used only after count semantics are established. Its coefficient bound is below b. Both the selected count and availability streams are exact full-digit intersections. The half-radix slack bound makes the right-hand threshold equation carry-free, and the separate converse bound shows that every genuine legal event's slack fits. Prior own firings are charged by the full six-times-count term. Same-layer and future firings cannot subsidize an event.

The relaxed-slack example correctly demonstrates why a full-digit slack mask would be unsound. The actual guard excludes that attack.

The exact signed target is translated into one local slot. Separate spatial and time powers select an actual event bit, and containment in the bounded event stream supplies the time bound. Selection does not test final-count parity. The repeated-firing separator and the even-final-count example are valid.

Layer serialization is sound because distinct already-legal members only add chips to unprocessed members. Completeness can place one sequential event in each layer and enlarge independent padding enough to meet all lower bounds. No endpoint stability or completeness of an infinite execution is required. The no-finite-stabilization example correctly separates the relation from global stabilization.

The suggested phrase “complete finite prefix” was removed from the final draft; it now says that the original finite prefix may be retained. This resolves the only editorial ambiguity identified during this review.

## Independently recounted literal object

`literal-dag-check.json` records:

- 3,865 distinct positive witness leaves and one free positive input
- 2,251 residual equations
- 17,275 binary arithmetic gates: 6,788 multiplications, 5,931 additions, and 4,556 subtractions
- 10,523 body gates and 6,752 sum-of-squares gates
- 186 macro declarations: 138 POWER, 34 Sub, 8 AND, and 6 SPREAD
- 44 exposed ports
- Exact residual degree histogram: 462, 983, 211, 423, 7, 138, 18, 6, 3 at degrees 1 through 9 respectively
- The only degree-nine residuals are `patch.shift.eq8`, `patch.shift.eq9`, and `patch.shift.eq11`
- Each has the same degree-nine monomial with coefficient −4 in the six dimension leaves and the three pre-adapter padding leaves
- The resulting degree-eighteen homogeneous SOS term has coefficient 48, so degree 18 is exact
- Every gate, declared witness, and free input is reachable from the checked final output

These results match the manuscript, including its operation subtotals and resource decompositions. All six displayed principal content hashes were recalculated and found in the manuscript exactly. The DAG hash is `7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6`.

## Conditional computability section and source confidence

The corollary is explicitly conditional and separate from the main polynomial theorem. The exact coordinate normalization is valid: translating by period multiples preserves the tile, makes a finite seed nonnegative, and translates the target by the same vector. Encoding the translated data is a finite computation in the same eleven-field format. The r.e. enumeration and many-one composition arguments are sound.

The fixed-tile slice uses one fixed universal hardware realization and direct finite seeds; it does not confuse an input-dependent periodic initializer with fixed hardware. Hardcoding finitely many fixed realization constants is adequate for the stated existence of a computable reduction. No numeric tile, executable coordinate compiler, paid arithmetic compiler, or identification with a distinct global-halting loader is claimed.

Both initializer endpoint repairs are disclosed as the report's mathematical corrections. The interval-partition reasoning is independent and sound. The bounded-seed inference is identified as an interface inference rather than a printed raw-radix compiler. Qualitative routing remains an explicitly imported dependency; the text does not claim that this report newly audited all such geometry or that primary-source screenshots were verified.

For source-use accounting, I independently confirmed the designated conservative Cairns-discussion block counts: 54 words for the ingredient paragraph; 51 for the entire endpoint paragraph including corrections and disclaimers; 36 before the displayed imported equivalence; 8 for the finite-cell sentence; and 10 for the activation sentence. This totals 159 whitespace words. Adding the nine words in the displayed equivalence and sixteen bibliographic words gives 184. The report contains no verbatim quoted source passage. Its endpoint partition, reserved-seed inference, coordinate normalization, r.e. enumeration, composition, and fixed-hardware hardcoding arguments are original mathematical reasoning rather than an extended paraphrase of the source. The brief restatement of the selected event spells out the report's own imported hypothesis.

The new research section correctly treats a literal raw-program compiler, resource improvements with fresh ledgers, and end-to-end formalization as future projects with separate obligations.

## Visual result

All final pages are legible and consistently typeset. I found no clipped equation, table collision, missing glyph, unresolved reference, or overlapping text. Both ledger tables and the printed hashes are readable. The corrected bibliography avoids excessive word stretching. Pagination and section transitions are acceptable for a dense mathematical report.

`visual-check.json` pins the final PDF and every independently reproduced inspected image. The render command was `pdftoppm -r 110 -png`; the output directory was outside the release. Rendering is a read-only examination of the final PDF and does not reproduce or verify the TeX build toolchain. Deterministic build/archive claims are supported by separate packaging evidence, not newly asserted from rendering.

## Audit files

- `AUDIT.md`: this review
- `check_literal_dag.py`: fresh independent read-only source recount and exact-degree checker
- `literal-dag-check.json`: its successful receipt
- `visual-check.json`: final-PDF image verification and visual findings
- `render/`: independently rendered final PDF page images
- `audit-manifest.json`: hashes and sizes of this audit's files, excluding the manifest itself

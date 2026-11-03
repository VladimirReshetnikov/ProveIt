# Independent review of the clarified decimal displays

Both v2 displays pass the external checks described here; I found no graph,
coefficient, selector, or rendering mismatch. The earlier independent review
also reruns successfully against its pinned original files. This review
covers only the identified artifacts and is not an iPRA derivation or a
Lean theorem about the displayed files.

For each variant, a full TeX comparison shows exactly one change from the
original: the display says to use ordinary integer arithmetic, that
subtraction is integer subtraction, and that intermediate values may be
negative. The v2 extracted PDF text includes the clarification. The twelve
unknowns remain strictly positive integers. I visually inspected each v2
first page; the text and circuit rows are legible and fit on the page.
Extracted text on PDF pages 2–4 matches the original PDF for each variant;
that text comparison is not a pixel-level identity test. The earlier review
visually inspected the original 94 formula and table pages.

[`audit.py`](audit.py), adapted from the independent original audit, repeats
the full graph comparison: it parses all 95 Lean source rows, checks the
95-row graph and the precise five-operation tail of the 94-row variant,
compares every TeX and PDF-extracted row to the corresponding graph, and
traces all 94 or 95 rows to the output. It rechecks all 943 decimal selectors,
the 41 slots, the formula text in TeX, and all four exact coefficient
integers against the retained decompressed payloads. It checks each published
v2 file against three recorded builds, including a build after relocation.
The PDF-extracted word boxes all lie within the page, with minimum reported
margin 28.028 points for either PDF. Poppler emits an XML-invalid control
character for a math delimiter, which is removed for the bounding-box check;
that check does not prove the formula rendering. These are external checks.

The Lean model-level equivalences, external source/JSON/byte/PDF bindings,
and the missing compact iPRA endpoint remain distinct obligations. The
94/95 operation counts describe the positive-coordinate DAGs; counting
additional `x+1` shifts requires a separate convention. See the
[original independent review](../ordinary12-decimal-displays-independent-review/README.md)
and [94-candidate review](../ordinary12-sum-squares-independent-review/README.md)
for their precise scope and provider limitations. No Lean replay was run
and no author files were edited for this review.

`python3 -I -S -B run.py` captured six successful checks with empty stderr:
the v2 independent audit, the original independent audit, and both authors'
variant-specific checkers for both versions. The original independent output
hash exactly matches its earlier capture. The captured result and script
hashes are in [`terminal.json`](terminal.json); the two independent results
are [`v2_independent.stdout`](v2_independent.stdout) and
[`original_independent.stdout`](original_independent.stdout). The runner
does not rebuild the PDFs or compile Lean.

- `audit.py`: `9ff631c2c9f213b9e070aabbdee7b81cf3b2f95dce892cb02ed7ef5da45c03fc`
- `run.py`: `2c5442ec12c97327dfcda237a55dbe48abda8a4167b54920ff9fc6d4f714cfb5`
- `v2_independent.stdout`: `eab07a1232debe35d05bcdca3a48b05fdba50eb6c8f7670be0fa676a93c4b2de`
- `terminal.json`: `cb748b9d8a0e8ef5198a9218cb28bda3bee60496a4b5ab8973a516e738cb99e2`

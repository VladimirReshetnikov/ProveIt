# Clarified standalone decimal displays of the 12-variable graphs (v2)

This v2 presentation supersedes the [original display packet](../compact44-free-j-display-draft/README.md)
for readers: it explicitly clarifies the arithmetic used in evaluator rows.
The original packet and its hash-pinned independent review remain unchanged.

[`equation94.tex`](equation94.tex) and [`equation94.pdf`](equation94.pdf)
display the 94-operation sum-of-squares candidate. The parallel
[`equation.tex`](equation.tex) and [`equation.pdf`](equation.pdf) in this
directory display its 95-operation parent. The only unknowns are the twelve
distinct names `a` through `k` and `ℓ`; `r01` through `r94` or `r95` are
explicitly defined evaluator abbreviations, not unknowns. The evaluator rows use
ordinary integer arithmetic, including integer subtraction; intermediate values
may be negative even though the unknowns are positive. Both PDFs use decimal
numerals, include recipes for all four fixed integers and the entire 943-entry
decimal selector table, and need no external coefficient file to state the
equation. The separately maintained 14-variable root `equation.tex` and
`equation.pdf` were not changed.

[`generate.py`](generate.py) reads hash-pinned graph and symbolic coefficient
sources, verifies topological graph references, computes all four displayed
constants, and compares their complete values to the decompressed retained
parent payloads. `MF_source` is already shifted: the displayed `ν` includes
beta exactly once. The generator maps the original twelve witness positions
to the displayed names, renders the selected circuit and the decimal table,
and invokes `pdflatex` only in a fresh child of this draft directory. The
original packet retains the failed initial pin and overfull-layout attempts
and their evidence; this version changes only the arithmetic explanation in
the displayed source.

The clarified 94-operation builds `build-attempt07/` and `build-attempt08/`
and 95-operation builds `build-attempt09/` and `build-attempt10/` respectively
produce byte-identical TeX and PDF within each pair, matching the canonical
v2 files. These builds were created before this packet was moved to its v2
directory. Fresh builds in that directory, `build-attempt11/` (94) and
`build-attempt12/` (95), also match their canonical files byte-for-byte; their
comparison and rerun display checks are recorded in
[`observations/relocation-check01`](observations/relocation-check01/).
Both revised circuit pages were visually inspected. Each PDF has four
letter-size pages and no overfull boxes; each build reports one underfull box
at the explicit column break. The original builds and their prior generator and
checker remain in the [original packet](../compact44-free-j-display-draft/).

[`check_display.py`](check_display.py) compares every operation extracted
from the PDF with the selected pinned JSON graph, checks all 943 selector
blocks in both TeX and extracted PDF against the pinned Lean row source,
checks that the arithmetic clarification appears in both TeX and extracted PDF,
checks the printed constant formulas and 41 slots, and compares the four
computed integers with the entire retained raw payloads. The recorded results
and checker hashes are in
[`observations/display-check-94-attempt02`](observations/display-check-94-attempt02/)
and [`observations/display-check-95-attempt02`](observations/display-check-95-attempt02/).
The earlier checks and their source snapshots remain in the original packet.
The attempt02 receipts here were recorded before relocation; the relocation
receipt records fresh checks from this directory.
These are external finite and presentation checks, not Lean theorems about
TeX, PDF, gzip decoding or file bytes.

The 94-operation candidate replaces the parent's final six operations with
five for a sum of three squares. Its Lean theorem proves same-valuation zero
equivalence to the 95-operation literal in every `IΣ₁` model with the fixed
integer ports as parameters. Its independent graph comparison, degree-84
evidence, exact theorem scope and provider limitations are documented in
[`ordinary12-sum-of-squares-candidate`](../../ordinary12-sum-of-squares-candidate/README.md).
The parent's metadata states degree 70. The present display checker verifies
transcription, not the degree of either graph. The Lean model-level fixed-byte
recipe bridge applies to the parent expression; it has not been joined here
to a Lean statement about these PDF files. A coherent compact-candidate iPRA
endpoint remains a separate obligation. These drafts do not claim such an
endpoint or global optimality.

From this directory, rebuild either variant in a fresh output directory with
`python3 -I -S -B generate.py --variant 94 --output "$PWD/build-new-94"` or
`python3 -I -S -B generate.py --variant 95 --output "$PWD/build-new-95"`.
Run `python3 -I -S -B check_display.py --variant 94` or `--variant 95` to
repeat the external display checks. Each check compares its two named
corrected builds and canonical draft, so those artifacts must be present.

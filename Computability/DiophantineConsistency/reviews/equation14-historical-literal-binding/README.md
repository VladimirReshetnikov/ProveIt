# Finite binding of the historical fourteen-variable literal

This packet connects the single-author historical-hybrid standard-iPRA
endpoint to the maintained [`equation.tex`](../../equation.tex) and
[`equation.pdf`](../../equation.pdf) more closely. It is **not** a formal Lean
semantics for TeX or PDF, an independent second Lean proof replay, a claim that
all current-source dependencies have been rebuilt, or a proof of ZFC
consistency.

Both Python audit scripts use assertions for verification and explicitly
refuse optimized Python (`-O` or `-OO`). Their originally recorded receipts
predate that fail-closed guard; independent review rechecks the guarded script
versions and records their hashes separately.

## Polynomial and displayed variables

[`audit_expression.py`](audit_expression.py) parses the actual historical
Lean `expressionAt` source and checks all 14 variable indices, four symbolic
port positions, 22 arithmetic definitions, and final factor-product wiring
against the pinned 65-gate candidate. It compares exact sparse integer
polynomials; the existing `verify_display_tex14.py` separately parses the
actual TeX unknown list and definitions against the same graph. Three Lean
source mutations are rejected. The script also reproduces the committed PDF
byte-for-byte from the pinned TeX with the installed pdfTeX. Its final
[receipt](expression-receipt.json) was produced by tool session 97692,
observed exit 0.

The historical and current `CurrentEquationSyntax2011.lean` bytes agree. In
its 24-module source-declared project import closure, the only observed
workspace difference is `NaturalExpression.lean`; the audit checks that all
bytes outside the body of theorem `eval_splitNatural`, and that theorem's
signature, agree. This is a source observation, not a fresh Lean replay of
the current project or an audit of external/dynamic imports. The endpoint
source uses `positiveShift expression` and the two `splitNatural` sides. The
separate Lean theorem `ObjectCurrentEquation2011.polynomial_expressionAt`
states the expression-to-`Carrier65.polynomial` identity.

## Four concrete fixed ports

The bounded, idle-priority [`Probe.lean`](Probe.lean) directly evaluated
`CurrentWindowCarry2011.ports` at indices 0–3 using the freshly built author
project objects and the rebuilt Foundation/package provider. Tool session
82565 actually exited 0 and wrote all four complete decimal outputs. The
[dependency log](deps.log) resolves its declared project import to the
audited author `CurrentKernelData2011.olean`; the [probe log](probe.log)
records the success marker. [`audit_ports.py`](audit_ports.py) independently
compares the entire captured decimal strings with the exact integers in all
four decompressed, hash-pinned coefficient files, and verifies that object's
recorded author source and object hashes. Its [receipt](ports-receipt.json)
records the exact values' lengths and hashes. The compressed full outputs are
retained under [`port-outputs`](port-outputs/). The original direct comparison
also exited 0 in session 3268.

The existing printed-constant reconstruction was rerun separately, actually
exited 0, and its [captured output](printed-constants-repeat.json) reports all
942 tiles, 885,481 ranking comparisons, and four coefficient values. It pins
the complete TeX fixed-constant block, reads the printed decimal seed and
checks the Lean cached data, but its interpretation of the decoder, tile
table, ranking and fixed-port formulas is **manually transcribed**. It is not a
general parser of those TeX recipes. The earlier saved
`PRINTED-CONSTANTS-AUDIT.json` differs from the new output in exactly one
unrelated field: the hash of `equation86.tex`; the 14-variable TeX hash,
constant block, all computed records and all other JSON entries match. The
first combined rerun followed by a whole-file `cmp` therefore exited 1 on
that stale field; the separate reconstruction itself was then rerun with
observed exit 0. Both outcomes are recorded in
[`terminal-observation.json`](terminal-observation.json).

The direct `#eval` result is an executable Lean computation followed by an
external exact comparison, **not an internal Lean equality theorem**. It
inherits the fresh author's unverified package-transitive and dynamic-loading
ancestry, and the outer Foundation build-wrapper exit was not observed. The
remaining TeX-recipe transcription and PDF interpretation prevent claiming a
fully formal Lean proof that a PDF string denotes the endpoint. The paired
project/endpoint replays also remain separate obligations.

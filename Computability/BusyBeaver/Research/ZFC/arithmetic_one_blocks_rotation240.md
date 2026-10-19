# Internal one-valued spare blocks

[`ArithmeticOneRegisterBlocksRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticOneRegisterBlocksRotation240.lean)
defines the repeated register block `011` for arbitrary internal counts and
suffixes in every IΣ₁ model. The fixed Σ₁/Δ₁ graph is total and satisfies
`oneBlocks 0 s = s` and `oneBlocks (n+1) s = 8 * oneBlocks n s + 6`.
Concatenation and append laws retain the whole suffix. Over the natural
numbers, the function agrees with the existing finite-list tape codec.

This supplies the code algebra for the 240-state machine's spare invariant:
167 initial one-valued blocks, with one more appended by each increment.
An internally unbounded spare count is represented arithmetically, rather
than by an external finite list. The machine contracts enforcing this
invariant remain separate.

The [actual check](results/arithmetic-one-blocks-rotation240-verification.json)
passes nine axiom probes and eleven typed callers with zero warnings and only
standard Lean axioms. Source compilation took 3.884 seconds and the audit
1.933 seconds, sharing a 120-second deadline with one thread, 4,096 MiB and
default proof limits. The first check passed with two unused-simp warnings;
removing those two unused arguments produced this clean second check.
The statements and audit did not change, and both actual records are retained.

The selected boundary reuses 15 project prerequisites, three explicit external
pairs and Init/Omega from the actual RunFromRotation240 parent record. Its
machine run theorem is not imported by this tape-code unit. All 208 input
identities, first providers and fresh-object captures passed their postchecks;
dependencies were reused without a rebuild or whole-cache attestation.
The [completed-run review](arithmetic-one-blocks-rotation240/review.json)
checks the narrow source cleanup, unchanged audit and actual evidence, with
original guard authorship disclosed. Its
[history](arithmetic-one-blocks-rotation240/review-history.json.gz) preserves
the review reader and receipt.

The [publication record](results/arithmetic-one-blocks-rotation240-publication.json),
[guard, audit and logs](arithmetic-one-blocks-rotation240/), and
[history](arithmetic-one-blocks-rotation240/history.json.gz) preserve the exact
sources, executions and correction. They retain historical scratch paths and
do not supply a clean-checkout build package.

The construction follows `ArithmeticZeroRegisterBlocks254`, replacing its
affine update `4*x+2` by `8*x+6`. It proves tape-code algebra, with the machine
simulation and PA consistency equivalence still open.

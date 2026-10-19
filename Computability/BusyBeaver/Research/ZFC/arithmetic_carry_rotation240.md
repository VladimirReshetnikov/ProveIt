# Internal unary carry and return for Rotation240

[`ArithmeticRegisterCarryRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticRegisterCarryRotation240.lean)
proves the carry, seek, rollback and return effects on one unary register
block for every internal register value in every IΣ₁ model. Each endpoint
takes exactly `value + 2` steps and retains both complete numeric tape halves.
The zero-valued case is included.

Carry swaps the leading `01` of the ordinary block with `10`; seek crosses
the block unchanged. Rollback restores the carried block, and the two actual
return entries restore an ordinary reversed block. Twelve literal transition
equations and eight state-code identities bind these proofs to the exact
240-state table. The old Forward module supplies only the pure block-code
definitions; every executed step and scan uses Rotation240.

The [actual check](results/arithmetic-carry-rotation240-verification.json)
passes **11 axiom probes and 13 typed callers with zero warnings**, using
only standard Lean axioms. Source/audit times were 3.675/2.379 seconds, with
default proof limits, one thread, 4,096 MiB and a shared 120-second deadline.
The initial attempt exposed two overly broad rewrites of `2 = 1 + 1` that
also changed tape expressions. Restricting those rewrites to the clock
argument produced the passing version; all statements and audit clients
remain unchanged.

The guard reuses 35 project prerequisites, four directly imported external
boundaries, one retained external boundary and Init/Omega. Its parents are
the actual Scans240 check and the original ForwardPerm252 check. The latter
has historical evidence without the newer pre-audit object capture or recorded
shared deadline; the guard preserves that limitation explicitly. This is not
a dependency rebuild or whole-cache attestation.

The [publication record](results/arithmetic-carry-rotation240-publication.json),
[guard, audit and logs](arithmetic-carry-rotation240/), and
[history](arithmetic-carry-rotation240/history.json.gz) retain original source
review, both actual attempts and the final repair review. The reviewer authored
the guard, while root executed it; that role is disclosed. Historical scratch
paths are retained rather than presented as a clean-checkout build package.

The proof follows the maintained Rotation240/Rotation244 box contracts and
the older arithmetic return argument, preserving attribution to Mira-Cult,
Jeff Ketchersid, Andrew James Wade and ProveIt contributors. Whole-file
traversal, internally many spare blocks and the complete binary simulation
remain separate obligations.

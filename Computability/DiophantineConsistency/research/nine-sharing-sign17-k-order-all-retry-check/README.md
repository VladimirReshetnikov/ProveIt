# All K local order blocks and boundaries: corrected guard

This checked 17-stage attempt retains the unchanged manifest and sources
from the [initial packet](../nine-sharing-sign17-k-order-all-check/README.md),
whose prelaunch approval was withdrawn before any Lean run. The fresh runner
requires each direct import, including implicit `Init`, to use its first
candidate route; it compares `Init` realpath/hash against the common
captured Fin942 provider record, requires `Init` to appear in every dependency
list, and sets `LEAN_NUM_THREADS=1`. The original
per-child resource guards and all 40 provider source/object/log/direct-guard
and overlay checks remain. The original runner's differences did not by
themselves demonstrate a provider breach or extra Lean threads; these added
assertions make the intended route and configuration explicit.

The stages check Start, all within-block candidate index and weight
facts, and the 15 numeric/actual-weight interblock comparisons. A successful
run would not itself assemble a global ordering or prove ranks, K coefficient
aggregation, or external file binding. Author no-Lean preflight exited 0.
Runner SHA-256:
`bcb362640a9b64e233e0e1c5a15ad52c4472d4cbd672e0fcc54a129a40942d20`;
unchanged manifest SHA-256:
`00989ec839e9edac1a03867d3ff9a9c002620c0c2a91931b376a5230d09e81ae`.
The run used the established independent-review and exclusive-slot workflow.

At independent review's request, the runner was amended before any Lean run
to require the `Init` dependency explicitly; the no-Lean preflight then
passed again. The prior corrected-runner hash was
`9564573905b47fcfe55faf05d3986b075669ef087d5c4922b3ece45414b54742`.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-order-all-retry-prelaunch-independent/README.md) passed on the final runner bytes.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-order-all-retry-terminal-independent/README.md) passed; the packet is frozen.

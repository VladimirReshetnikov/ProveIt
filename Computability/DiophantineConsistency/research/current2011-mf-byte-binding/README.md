# Current2011 MF bytes: external shifted-recipe check and Lean gaps

The [external check](check-bytes.py) reads the fixed high-mask radix-digit
runs from the hash-pinned [draft Lean source](CurrentMFBytes.lean), evaluates
the corresponding 2,011 little-endian base-`2^47` digits, adds
`(2^47)^2011 - 1` **exactly once**, converts to minimal big-endian bytes, and
compares the entire result to both recorded MF payloads. It checks the graph,
compressed payload and raw-byte hashes. The comparison passed for 11,815
bytes encoding a 94,518-bit integer, and the checker also rejects equality
with the unshifted mask. The [result](bytes-observation.json) and
[observed exit](bytes-terminal.json) record the check. This is external Python
evaluation and comparison, not Lean file or gzip semantics.

The separate [recipe diagnostic](../current2011-mf-recipe-diagnostic/README.md)
successfully checked in Lean that the explicit high-mask digit list equals the
current2011 list and decodes to `highPort`, and that `rho^2011 - 1` equals
beta. The subsequent [shift diagnostic](../current2011-mf-shift-diagnostic/README.md)
has **not** proved that their sum casts to port 3: both attempts hit kernel
memory limits while checking that cast. The complete draft source in this
packet likewise has **no successful Lean check**. Four attempts are retained:
[01](attempt01/), [02](attempt02/), [03](attempt03/), and [04](attempt04/).
They failed at recursion/kernel or interpreter limits; a printed axiom report
from a failed run is not proof. These results do not establish an MF
byte-to-port theorem, an iPRA endpoint, PDF semantics, or a complete file
binding for any graph.

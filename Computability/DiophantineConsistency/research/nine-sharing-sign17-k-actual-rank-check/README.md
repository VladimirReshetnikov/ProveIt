# Conditional criterion for the actual K physical map

This checked 17-stage attempt replays the independently audited generic
rank criterion and proves its specialization to the existing
`MF.WangTiles942.physicalMap`. It explicitly imports the permutation module
from the existing sign17 degree-provider overlay and pins that object's
SHA-256 and recorded target. Candidate zero/nonzero behavior and strict
descending actual weights remain hypotheses: this does not establish those
for the external witness, complete K, an external file binding, or a
consistency equivalence. Lean checked the explicit import and specialization.

The prior [physical-map attempt](../nine-sharing-sign17-k-rank-certificate-check/README.md)
failed because it did not import the permutation namespace; the generic
criterion subsequently passed independent terminal audit. This attempt
recompiles the generic source rather than importing an object from its failed
predecessor. Usual per-child resource limits apply. Author no-Lean preflight
exited 0. Runner SHA-256:
`405c630cad2a2db3d5d5785accedb595e63017563a5b120b2cc55fd52e4c6ded`;
manifest SHA-256:
`307e5e6d090bed5839438f9d8a5e3dc93afa0118ffb8ac441a07bee41095b197`;
source SHA-256:
`8b616ffaac0deafcd1aeb67f61afecad528b82624a18e3a6b4c99a645ade6f9e`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-actual-rank-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-actual-rank-terminal-independent/README.md) passed; the packet is frozen.

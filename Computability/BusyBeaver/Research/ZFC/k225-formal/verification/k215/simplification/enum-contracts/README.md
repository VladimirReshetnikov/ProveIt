# Shared contracts in the command-permuted enumerator

This refactor centralizes three facts in `EnumPerm.lean`: a command preserves the
soundness invariant or halts with derivable falsity; a compiled block composes
with a continuation while preserving early halting; and AX followed by ten pops
restores the previous stack while loading the previous current code. Seven
existing proofs use these facts. GEN and MP no longer repeat the early-halting
case analysis, and discard, bundle selection and MP share the AX cleanup proof.

All 91 previous public declarations retain their statements. All executable
definitions, command encodings and compiler blocks are unchanged. The complete
module decreases from 693 to 682 lines (27,922 to 27,903 bytes); this is a local
structural simplification, not a large compression result.

The isolated candidate with three axiom reports passed in 8.683 seconds with no
warnings. An audit importing the checked baseline produced byte-identical reports
for `sound`, `complete` and `enum_halts_iff`: only `propext`, `Classical.choice`
and `Quot.sound`. The parent performs affected endpoint-closure checking after
adoption; the isolated check is not a fresh full-closure replay.

Runs 1–4 are retained: proof-shape/rewrite errors and one 120-second timeout caused
by a broad definitional conversion. The successful proof uses explicit rewrite
arguments instead. No resource increase, admission or failed object is used.

The independently reviewed candidate is now adopted in the canonical source.
The independent source peer is `peer-review.json`; its own static reader is
`peer-review.py`. Parent endpoint-closure revalidation follows separately.

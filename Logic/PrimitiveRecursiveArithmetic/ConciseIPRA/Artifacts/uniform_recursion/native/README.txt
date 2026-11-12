STRICT NATIVE CHECKER REFINEMENT

Selected program: fused_native.py
Optional smaller implementation: fused_scoped.py

Both accept exactly the certificates accepted by the pinned native780.py
control. The selected program has an explicit public grammar guard. The
optional implementation integrates that guard into the existing list and
scalar cases. It also rejects malformed syntax immediately and never relies
on RecursionError for rejection.

This supplement is independent of the report's new arithmetic construction.
It implements the unchanged native scalar Eq/D calculus. It is a proved
implementation refinement, not a new arithmetic or logical axiom deletion.

Complete normalized modules (bytes / tokens / AST nodes / gzip-9):

  controls/native780.py       780 / 360 / 409 / 458
  fused_native.py             685 / 340 / 385 / 409
  fused_scoped.py             661 / 336 / 381 / 390

All parsing, validation, proof checking, and verdict code is counted.
Measurements use ast.unparse plus one final LF. Gzip-9 is informational.
The preserved control controls/compact508.py has a DIFFERENT public syntax
contract and is supplied for transparent provenance, not as a matched
competitor beaten by either strict program.

Run from this directory:

  python3 audit_fusion.py
  python3 fused_native.py < fixtures/native/new_reflexivity_zero.json
  python3 fused_native.py < fixtures/native/canonical_false_without_proof.json

Acceptance means exit status zero and exactly ACCEPT followed by one LF.
The first example accepts; the second rejects. Rejection diagnostics are
not part of the contract. Unused leading certificate entries retain their
inherited behavior. The entire proof translation is the identity in both
directions: certificates need no recoding.

Files:

  FUSION_PROOF.txt     Universal acceptance proof and precise claim limits.
  fusion_audit.json   Executed verification receipt and measured sources.
  audit_fusion.py     Self-contained reproduction, standard library only.
  fixtures/          Eighteen inherited native cases and their declarations.
  controls/          Exact incoming native780 and compact508 source files.
  PROVENANCE.json     Pinned commit, archive identity, source hashes, attribution.
  LICENSE-ProveIt.txt Inherited MIT No Attribution license.

The audit compares 143580 generated syntax test positions with a separate
sorted decoder, for 430740 program checks, and runs 108 end-to-end CLI checks
using the declared outcomes of 18 pinned fixtures in ordinary and optimized
Python. Finite validation supports the implementation; the universal result
rests on the proof in FUSION_PROOF.txt. No new proof-assistant verification
or absolute minimality theorem is claimed.

The kernels require Python 3.8+; the audit requires Python 3.9+ for ast.unparse.
Exact
normalization/AST measurements may depend on the Python version. This audit
was executed with the runtime version recorded in the accompanying receipt.

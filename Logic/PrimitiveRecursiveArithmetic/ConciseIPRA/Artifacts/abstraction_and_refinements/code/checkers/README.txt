SMALLER COMPLETE iPRA VALIDATORS AND BYTE PROFILES

Read PROOF_NOTES.txt for the exact changes, mathematical argument, input
contracts, attribution, and limits. No logical axiom has been removed.

Complete source vectors (tokens / AST nodes / normalized bytes):
  compact_checker.py        274 / 306 / 476
  native_tokens_checker.py  317 / 364 / 617
  native_ast_checker.py     321 / 358 / 622
  native_bytes_checker.py   332 / 373 / 594
  strict_tokens_checker.py  328 / 377 / 634
  strict_ast_checker.py     335 / 368 / 643
  strict_bytes_checker.py   340 / 382 / 616

New native coordinate envelope: 317 / 358 / 594, versus 321 / 369 / 596.
New strict coordinate envelope: 328 / 368 / 616, versus 330 / 380 / 621.
Each coordinate envelope combines different programs. The compact byte
record falls from 477 to 476; compact token244 and AST265 are not improved.

For a single recommended complete JSON interface use strict_bytes_checker.py,
which validates the whole integer/list certificate and the native public goal.

Example:
  python3 strict_bytes_checker.py < fixtures/strict_proofs/computation_zero_local.json

Reproduce all metrics and matched tests:
  python3 verify.py

Every candidate has a frozen *_control.py. PROVENANCE.json records control
paths and SHA-256 identities. LICENSE-ProveIt.txt preserves upstream licensing.
fixtures/ contains the complete JSON tests. verification.json contains the
actual results: 582 profile/fixture cases, 2,328 isolated executions, and zero
failed expectations on CPython 3.12.14. The programs use only Python's standard
json parser.

This is a proof-checker implementation reduction. The native scalar calculus,
all logical/nonlogical rules, and its iPRA bi-interpretation remain inherited.
There is no claim to absolute shortestness or to compact full-coordinate
domination, and no compressed payload or external checker is hidden in size.


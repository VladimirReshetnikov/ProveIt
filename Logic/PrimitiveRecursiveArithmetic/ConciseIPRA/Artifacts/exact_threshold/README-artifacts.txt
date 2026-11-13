EXACT-BINDING iPRA CHECKER ARTIFACTS
13 November 2026

RESULT
The complete counted checker code/checker.py measures 314 significant tokens,
357 AST nodes, and 590 normalized UTF-8 bytes on CPython 3.12.14. These are
strictly below the inspected exact-canonical-binding envelope 316 / 358 / 591.
They are NOT below the smaller promised-grammar compact programs. No global
minimum or new arithmetic axiom deletion is claimed.

RUN A PROOF
  python3 code/checker.py < examples/computation_zero_local.json
  python3 code/checker.py < examples/guarded_induction_with_used_hypothesis_local.json

Acceptance is normal process termination printing exactly ACCEPT plus LF.
Exceptions, resource exhaustion, or any other output reject. No assertion
statement enforces a proof obligation, so Python -O has the same proof rules.

RUN THE CHECKS
  python3 reproduce.py
  python3 tests/translate.py
  python3 tests/verify.py
  python3 tests/verify_threshold_modes.py

reproduce.py checks the source metrics and all supplied accepting/rejecting
examples against both the counted checker and its readable expansion.
tests/translate.py reconstructs the fourteen current certificates from the
old control fixtures, under tests/fixtures/regenerated/. It is a TRACE-BASED
CERTIFICATE TRANSLATOR, not a general search procedure or independently
verified compiler for arbitrary iPRA proofs. It traces the known source
checker to locate introduction nodes and changes only equation-mode flags.
The paper gives the general rule-by-rule completeness argument; the script
is a reproducible test of that construction on the shipped fixtures.
tests/verify.py performs the independent grammar, opener, mutation, capture,
and normal/-O command-line checks and writes tests/verification.json.
tests/verify_threshold_modes.py reproduces the 90 threshold/future-witness
capture trials and checks their frozen receipt.

TRUST BOUNDARY
Only code/checker.py is counted and trusted for acceptance. Other programs
are explanatory expansions, untrusted proof producers, tests, controls, or
measurement scripts. The counted checker imports only Python's JSON reader.
It does not import a theorem table, trusted proof compiler, or other kernel.
The accepted byte language intentionally allows unused prefix JSON values.
Public formulas use true as an alias for code 1 (numerical zero), while false
is rejected in the public goal. The actual binder grammar is checked locally.

CONTENTS
  code/checker.py               Complete counted program.
  code/readable.py              Explanatory expansion, not counted.
  controls/intrinsic_checker.py Prior intrinsic-validation control.
  controls/native_positives.json Old fourteen canonical certificates.
  examples/                    Translated proofs and two rejections.
  tests/                       Portable translator and independent tests.
  evidence/                    Measurements, proof notes, validation receipt.
  LICENSE-upstream.txt          Repository's MIT-0 license.

ATTRIBUTION AND SOURCE PIN
The scalar Choice-DI calculus, the bi-interpretation with iPRA, the prior
checker, fixtures, and the main independent-test framework are derived from:
  Vladimir Reshetnikov, ProveIt
  https://github.com/VladimirReshetnikov/ProveIt
  commit f25af53c682ea76c57b67c70c976bcaf836b0c91
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
In particular, the matched control and source fixtures were delivered in
  docs/incoming/ipra_intrinsic_validation_2026-11-13.zip
with source provenance pinned there to fc05b10f0e03f22edbfdde9298a29fb2fee5dc59.
The present refinement changes an unused source traversal, the mode-bit
convention, and the reader binding. Full mathematics remains inherited.

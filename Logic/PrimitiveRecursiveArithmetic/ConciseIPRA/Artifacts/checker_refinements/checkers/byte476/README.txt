476-BYTE COMPOSITION: COMPLETE CHECKER AND FIXTURE AUDIT
====================================================

Result
------
checker476.py composes the head_conversion product opener with the eager
mode selector of checked_reductions. It changes exactly this expression:

    bool(m or 3 % len(a))
to
    any((m, 3 % len(a)))

Whole-module normalized sizes on CPython 3.12.14:
                        significant tokens   AST nodes   UTF-8 bytes
control477.py                  272               306          477
checker476.py                  274               306          476

This is a byte-count improvement in the existing guarded presentation.
It does not delete an axiom, beat the token/AST minima, or prove minimality.
The containing report states the mathematical equivalence and its limits.

Run
---
    python3 checker476.py < proof_zero_computation.json
    python3 verify476.py

Success is normal termination with exactly ACCEPT followed by LF.
The verifier is self-contained and uses only the standard library.
It verifies upstream Git blob hashes, checks all 66 retained fixture labels
(40 unique payloads), and invokes both checkers in ordinary and optimized
Python. That is 264 isolated CLI executions. The resulting fixture_audit.json
records every expectation and outcome. The delivered run has no failures
or discrepancies. Finite tests supplement the written equivalence proof.

Example decoded
---------------
proof_zero_computation.json is the unchanged canonical upstream fixture
compact_context__computation_zero_local.json. Its closed goal is

    I(0, S(S(0)); u.S(0)) = S(S(0)).

It uses a nonempty initializer, so the computation branch is selected directly.
The final input record is [goal, 0]; preceding records have four fields.
The administrative neutral major is [], distinct from the numerical zero 0.

Input contract
--------------
The checker assumes finite exact-integer/list certificate trees and a
canonical closed guarded Eq/D public formula. It does not independently
validate that public grammar or all arbitrary JSON values. An unused prefix
of proof packets is allowed. The final record supplies the public goal and
initial floor 0. The complete inference/reader/output module is charged.

Provenance
----------
provenance.json fixes the repository commit, source path and control Git SHA.
fixture_index.json retains the original paths, sizes and Git blob SHA values.
The fixtures are inherited from head_conversion at the same commit. Labels
in cases.json preserve the upstream expectations, including off-contract
diagnostics; they must not all be described as canonical public formulas.
The files may be used under the repository's MIT No Attribution license.

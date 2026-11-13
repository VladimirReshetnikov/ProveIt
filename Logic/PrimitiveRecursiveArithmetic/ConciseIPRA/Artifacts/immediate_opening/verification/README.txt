Verification contents
=====================

Run from the package root:

    python3 verification/verify.py

The script also works from any other working directory. Python 3.12.14
is the measured environment. Only Python's standard library is needed.

The full reproduction performs 438 isolated checker executions:

* 66 frozen fixtures x 3 compact implementations x 2 Python modes = 396.
  These implementations are the 487-byte control, the 479-byte candidate,
  and the explanatory readable expansion.
* 21 explicit strict-interface cases x 2 Python modes = 42.

The Python modes are ordinary execution and -O. Each process is also run
with -I -S -B. Acceptance means exit status zero and exactly ACCEPT plus
a newline on standard output. A timeout is a failure, not a successful
rejection. The script checks fixture hashes before executing any case,
checks the frozen expected verdicts, compares control with candidate,
and checks that the strict validator functions and its candidate kernel
are exact AST matches to their retained source controls.

The 65 byte-profile fixtures retain both context/ and progress/ collections
from the incoming single-binder package. They include positive derivations,
capture attacks, unsupported or malformed public forms, and deliberately
out-of-contract raw data. A compact acceptance on an out-of-contract input
is a protocol-regression datum, not a theorem of the public theory.

The additional scope/future_scope_attack.json is the seventeen-packet
counterexample from the incoming scope audit. It encodes the false public
fixed-point formula. All supplied checkers reject it.

fixture_manifest.json records the SHA-256 digest, original archive path,
original member path, and expected compact acceptance for every fixture.
The repository snapshot is pinned there as well.

Delivered execution receipts
----------------------------

evidence/initial_validation.json records the original 260 executions of
the control and candidate on the 65 byte fixtures. Its historical local
paths are retained unchanged; fixture_manifest.json maps the same bytes
to this package's portable paths.

evidence/companion_validation.json records 178 subsequent executions:
132 readable-checker runs on all 66 fixtures, four control/candidate runs
on the added scope counterexample, and 42 strict-interface runs. Thus the
two new receipts together cover the same 438 executions as a full run,
with no unnecessary rerun caused merely by moving the files.

evidence/inherited_scope_counterexample_results.json is an attributed
historical receipt supplied in the original scope-audit archive; it is
separate from the new results. In that old experiment a deliberately
unsound deleted-scan control accepted the attack. No such unsound checker
is part of this package's acceptance interface.

The optional --companions-only switch reproduces the second receipt.
Default full reproduction writes evidence/verification.json.

Assurance boundary
------------------

These finite tests supplement the exact operational equivalence proof.
They neither replace that proof nor independently formalize the inherited
bi-interpretation with intuitionistic primitive recursive arithmetic.
